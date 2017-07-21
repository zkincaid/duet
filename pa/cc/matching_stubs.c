#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <cstdio>
#include <vector>
#include <string>
#include <cstdint>
#include <map>
#include <set>
#include <queue>
#include <stack>
#include <cmath>
#include <limits>
#include <functional>
#include <unistd.h>
#include <sys/wait.h>
#include <string.h>
#include "graph.h"
#include "embedding.h"
#include "gecode_embedding.h"
#include <gecode/search.hh>

#define TRACE false

/* Variable Selection */
enum Var_selection {
  MIN_DOMAIN_SIZE,
  MAX_CONFLICTS,
  MAX_CONFLICT_HISTORY,
};

using namespace std;

bool embedding(Embedding emb);
bool uembedding(Embedding emb);
bool cembedding(Embedding emb);
void find_conflicts(const Embedding& emb, const vector<int>& matching, vector<int>& confs);
void backtrack(stack<decision>& decisions, Embedding& emb);
bool choose(stack<decision>& decisions, const vector<int>& confs, Embedding& emb);

/**********************************************************
  This is the function that is called by the ocaml code
  It processes the ocaml structures to more efficient
  representations and calls the embedding function
  Which determines if str1 is embedded in str2.
***********************************************************/
extern "C" {
  CAMLprim value embedsOCAML(value str1, value str2, value algo){ /* str = int * (string * int list) list */
    CAMLparam3(str1, str2, algo);
    CAMLlocal3(head, propList, predList);
    
    vector<vector<uint8_t> > sig1, sig2;    /* Signature of str1 and str2 respectively */
    sig1.resize(Int_val(Field(str1, 0))+1); /* Resize to respective universe size */
    sig2.resize(Int_val(Field(str2, 0))+1);
    map<string, size_t> preds;              /* Mapping from predicate symbols to [0 .. n] */
    size_t predi, count(0);
    string pred;
    int arg;

    vector<prop> pu_label, pv_label;
    prop tmp;

    /* Process structure 1 */
    propList = Field(str1, 1);
    while (propList != Val_emptylist){
      head = Field(propList, 0);        /* hd propList Type: (string * int list) */
      propList = Field(propList, 1);    /* tl propList */
      predList = Field(head, 1);

      pred = String_val(Field(head, 0));
      if (preds.count(pred) == 0){
	preds[pred] = count;
      }
      predi = preds[pred];
      tmp = prop(predi);
      while (predList != Val_emptylist){
	head = Field(predList, 0);
	arg = Int_val(head);
	tmp.vars.push_back(arg);

	if (sig1[arg].size() <= predi){
	  sig1[arg].resize(predi + 1, 0);
	}
	if (sig1[arg][predi] != 255)
  	  ++sig1[arg][predi];
	
	predList = Field(predList, 1);
	++predi;
      }
      if (tmp.vars.size() >= 2){
	pu_label.push_back(tmp);
      }
      if (predi > count) { count = predi; }
    }

    /* Process structure 2 */
    propList = Field(str2, 1);
    while (propList != Val_emptylist){
      head = Field(propList, 0);        /* hd propList Type: (string * int list) */
      propList = Field(propList, 1);    /* tl propList */
      predList = Field(head, 1);

      pred = String_val(Field(head, 0));
      if (preds.count(pred) == 0) continue; /* This has no affect on embedding problem */
      predi = preds[pred];
      tmp = prop(predi);
      while (predList != Val_emptylist){
	head = Field(predList, 0);
	arg = Int_val(head);
        tmp.vars.push_back(arg);
	
	if (sig2[arg].size() <= predi){
	  sig2[arg].resize(predi + 1, 0);
	}
	if (sig2[arg][predi] != 255)
  	  ++sig2[arg][predi];

	predList = Field(predList, 1);
	++predi;
      }
      if (tmp.vars.size() >= 2){
	pv_label.push_back(tmp);
      }
    }

    bool result;
    switch (Int_val(algo)){
      case 0:
	result = uembedding(std::move(Embedding(sig1, sig2, pu_label, pv_label)));
	break;
      case 1:
	result = embedding(std::move(Embedding(sig1, sig2, pu_label, pv_label)));
	break;
      case 2:
	result = cembedding(std::move(Embedding(sig1, sig2, pu_label, pv_label)));
        break;
      default:
	printf("Error: Invalid Algorithm Choice %d\n", Int_val(algo));
	exit(-1);
    }
    CAMLreturn(Val_bool(result));
  }
}

/* Is there an injective homomorphism from the source vertices (U)
   to target vertices (V) of emb.universe_graph satisfying the
   constraints of emb.predicate_graph ? */
bool embedding(Embedding emb){
  if (!emb.get_valid()) return false;
  Graph& u_graph = emb.get_universe_graph();

  vector<int> match1, match2, vis, conflicts;

  match1.resize(u_graph.uSize(), -1);
  match2.resize(u_graph.vSize(), -1);
  vis.resize(u_graph.uSize(), 0);
  size_t ans, num(0), bt(0);

  stack<decision> decisions;

  do {
    std::fill(vis.begin(), vis.end(), 0);            /* Reset variables for matching problem */
    ans = u_graph.max_matching(match1, match2, vis); /* Compute maximum cardinality matching */
    ++num;

#if TRACE
    printf("iterations: %lu\tbacktrack: %lu\tlevel: %lu\n", num, bt, decisions.size());
#endif

    if (ans != u_graph.uSize()){
      backtrack(decisions, emb);
      bt++;
    } else {
      find_conflicts(emb, match1, conflicts);
      if (conflicts.size() == 0){
#if TRACE
	printf("iterations: %lu\tbacktrack: %lu\tlevel: %lu\n", num, bt, decisions.size());
#endif
        return true;
      }

      if (!choose(decisions, conflicts, emb)){
        backtrack(decisions, emb);
	bt++;
      } else {
	vector<Graph::VertexPair>& edges = decisions.top().u_edges;
	for (size_t i = 0; i < edges.size(); ++i){
	  if (match1[edges[i].u] == (int)edges[i].v){
	    match1[edges[i].u] = -1;
	    match2[edges[i].v] = -1;
	  }
	}
	/* Check if this loop is necessary */
	for (size_t i = 0; i < match1.size(); ++i){
	  if (match1[i] != -1 && !u_graph.has_edge(i, match1[i])){
	    match2[match1[i]] = -1;
	    match1[i] = -1;
	  }
	}
      }
    }
  } while(!decisions.empty());

#if TRACE
  printf("iterations: %lu\nbacktrack: %lu\n", num, bt);
#endif

  return false;
}


void ubacktrack(Embedding &emb, stack<udecision> &decisions) {
    Graph& u_graph = emb.get_universe_graph();
    udecision& d = decisions.top();

    emb.add_back(d.remove_p, d.remove_u);

    // Remove the (d.u -> d.v) edge
    size_t pos;
    const vector<Graph::Edge>& adj = u_graph.uAdj(d.u);
    for(pos = 0; pos < adj.size() && adj[pos].vertex != d.v; pos++) ;
    assert(pos < adj.size());
    bool check = u_graph.check();
    u_graph.remove_edge(d.u, pos);
    assert (!check || u_graph.check());

    decisions.pop();

    // Blame the (d.u -> d.v) edge removal on the previous decision
    if (decisions.size() > 0) {
	udecision& prev = decisions.top();
	prev.remove_u.emplace_back(d.u, d.v);
    }
}

size_t select_variable(const Embedding& emb, const vector<int>& conflicts, Var_selection sel){
  const Graph& u_graph = emb.get_universe_graph();
  const LabeledGraph<prop, prop>& p_graph = emb.get_predicate_graph();
  static vector<size_t> conflict_history;
  if (conflict_history.size() < u_graph.uSize()){ conflict_history.resize(u_graph.uSize(), 0); }

  if (sel == MIN_DOMAIN_SIZE || sel == MAX_CONFLICTS) {
    set<int> vars;
  
    for (size_t i = 0; i < conflicts.size(); ++i){
      const vector<int>& cvars = p_graph.getULabel(conflicts[i]).vars;
      bool valid(false);
      for (size_t j = 0; j < cvars.size(); ++j){
        if (u_graph.uAdj(cvars[j]).size() > 1){
          vars.insert(cvars[j]);
          valid = true;
  	  ++conflict_history[cvars[j]]; // increment conflict history even on non-decision variables
        }
      }
      if (!valid){ /* valid == false -> emb is arc inconsistent */
        return 0;
      }
    }

    size_t best_var = 0;
    if (sel == MIN_DOMAIN_SIZE){
      size_t min_val = u_graph.vSize() + 1; // MAX_VALUE + 1
      for (set<int>::iterator it = vars.begin(); it != vars.end(); ++it){
        if (min_val > u_graph.uAdj(*it).size()){
          best_var = *it;
          min_val = u_graph.uAdj(*it).size();
        }
      }
    } else {
      size_t max_val = 0;
      for (set<int>::iterator it = vars.begin(); it != vars.end(); ++it){
	if (max_val < conflict_history[*it]){
	  best_var = *it;
	  max_val = conflict_history[*it];
	} else if (max_val == conflict_history[*it] && u_graph.uAdj(*it).size() < u_graph.uAdj(best_var).size()){
	  best_var = *it;
	  max_val = conflict_history[*it];
	}
      }
    }
    assert (best_var != 0);
    return best_var;
  } else { /* sel == MAX_CONFLICTS */
    map<int, int> vars;

    for (size_t i = 0; i < conflicts.size(); ++i){
      const vector<int>& cvars = p_graph.getULabel(conflicts[i]).vars;
      bool valid(false);
      for (size_t j = 0; j < cvars.size(); ++j){
	if (u_graph.uAdj(cvars[j]).size() > 1){
	  ++vars[cvars[j]];
	  valid = true;
	}
      }
      if (!valid){
	return 0;
      }
    }
    size_t best_var = 0;
    int max_val = 0;
    for (map<int, int>::iterator it = vars.begin(); it != vars.end(); ++it){
      if (max_val < it->second){
	best_var = it->first;
	max_val = it->second;
      }
    }
    assert (best_var != 0);
    return best_var;
  }
}

bool uembedding(Embedding emb){
  {
      vector<Graph::VertexPair> p_removed, u_removed;
      emb.ufilter(p_removed, u_removed);
  }

  if (!emb.get_valid()) return false;
  Graph& u_graph = emb.get_universe_graph();

  vector<int> match1, match2, vis, conflicts;

  match1.resize(u_graph.uSize(), -1);
  match2.resize(u_graph.vSize(), -1);
  vis.resize(u_graph.uSize(), 0);
  size_t ans, num(0), bt(0);

  stack<udecision> decisions;
  while (1) {
      num++;

#if TRACE
      printf("iterations: %lu\tbacktrack: %lu\tlevel: %lu\n", num, bt, decisions.size());
#endif

      for (size_t i = 0; i < match1.size(); ++i){
	  if (match1[i] != -1 && !u_graph.has_edge(i, match1[i])){
	      match2[match1[i]] = -1;
	      match1[i] = -1;
	  }
      }

      std::fill(vis.begin(), vis.end(), 0);            /* Reset variables for matching problem */
      ans = u_graph.max_matching(match1, match2, vis); /* Compute maximum cardinality matching */
      if (ans != u_graph.uSize()) {
#if TRACE
	  printf("Backtrack: no total matching\n");
#endif
	  if (decisions.size() >= 1) {
	      bt++;
	      ubacktrack(emb, decisions);
	      continue;
	  } else {
	      return false;
	  }
      }

      find_conflicts(emb, match1, conflicts);
      if (conflicts.size() == 0){
	return true;
      }
      size_t d_var = select_variable(emb, conflicts, MAX_CONFLICT_HISTORY);
      if (d_var == 0){ /* d_var only equals 0 if emb is arc inconsistent */
#if TRACE
        printf("Backtrack: no decision variables in conflict\n");
#endif
        if (decisions.size() >= 1) {
	  bt++;
	  ubacktrack(emb, decisions);
	  continue;
	} else {
	  return false;
	}
      }
#if TRACE
      printf("Decision: %lu -> %lu\n", d_var, match1[d_var]);
#endif

      decisions.emplace(d_var, match1[d_var]);
      udecision& d = decisions.top();
      emb.decide(d);

#if TRACE
      printf("Removed %lu P-graph edges and %lu U-graph edges\n",
	     d.remove_p.size(),
	     d.remove_u.size());
#endif
      if (!emb.get_valid()) {
#if TRACE
	  printf("Backtrack: arc inconsistent\n");
#endif
	  bt++;
	  ubacktrack(emb, decisions);
      }
  }
}

bool cembedding(Embedding emb){
  {
    vector<Graph::VertexPair> p_removed, u_removed;
    emb.ufilter(p_removed, u_removed);
  }
  if (!emb.get_valid()) return false;

  ConstraintEmbedding* cemb = new ConstraintEmbedding(emb);
  Gecode::DFS<ConstraintEmbedding> e(cemb);
  (void) cemb->status();
  delete cemb;
  if ((cemb = e.next())) {
    delete cemb;
    return true;
  }
  return false;
}


/* Finds all vertices in pgraph.U that are violated by the candidate matching */
void find_conflicts(const Embedding& emb, const vector<int>& matching, vector<int>& confs){
  const LabeledGraph<prop, prop>& p_graph = emb.get_predicate_graph();
  confs.clear();
  for (size_t i = 0, j, k; i < p_graph.uSize(); ++i){
    const vector<Graph::Edge>& adj = p_graph.uAdj(i);
    const vector<int>& u_vars = p_graph.getULabel(i).vars;
    for (j = 0; j < adj.size(); ++j){
      const vector<int>& v_vars = p_graph.getVLabel(adj[j].vertex).vars;
      for (k = 0; k < u_vars.size() && matching[u_vars[k]] == v_vars[k]; ++k);
      if (k == u_vars.size()) break;
    }
    if (j == adj.size()){
      confs.push_back(i);
    }
  }
}

/* Performs backtracking on decisions only choosing decisions that are consistent
   with all previous decisions 
   This is done by maintaining consistence with the universe graph that is forced
   to be consistent with all previously made decisions */
void backtrack(stack<decision>& decisions, Embedding& emb){
  while(!decisions.empty()){
    decision& d = decisions.top();
    emb.add_back(d.p_edges, d.u_edges);
    for (; ++d.pos < d.pu_adj.size();){
      d.p_edges.clear(); d.u_edges.clear();
      emb.choose_constraint(d.u, d.pu_adj[d.pos].vertex, d.p_edges, d.u_edges);
      if (!emb.get_valid()){
	emb.add_back(d.p_edges, d.u_edges);
      } else {
	return;
      }
    }
    decisions.pop();
  }
}

/* computes the number of times a variable is involved in some conflict */
vector<size_t> num_conflicts(const LabeledGraph<prop, prop>& p_graph, const vector<int>& confs){
  vector<size_t> num_involved;
  for (size_t i = 0; i < confs.size(); ++i){
    const vector<int>& vars = p_graph.getULabel(confs[i]).vars;
    for (size_t j = 0; j < vars.size(); ++j){
      if (num_involved.size() <= (size_t)vars[j]) num_involved.resize(vars[j]+1, 0);
      ++num_involved[vars[j]];
    }
  }
  return num_involved;
}

/* Selects a vertex in pgraph.U to decide on next (only trying vertices that
   can be consistent with decisions already made) */
bool choose(stack<decision>& decisions, const vector<int>& confs, Embedding& emb){
  const LabeledGraph<prop, prop>& p_graph = emb.get_predicate_graph();

  vector<size_t> num_involved = num_conflicts(p_graph, confs);

  /* Priority Queue of conflicts ranked by hueristic value (smaller is better) */
  auto cmp = [](const pair<double, size_t>& l, const pair<double, size_t>& r){ return l.first < r.first; };
  priority_queue<pair<double, size_t>, vector<pair<double, size_t>>, decltype(cmp)> q(cmp);

  for (size_t i = 0; i < confs.size(); ++i){
    const vector<int>& vars = p_graph.getULabel(confs[i]).vars;
    double val(0);
    for (size_t j = 0; j < vars.size(); ++j){
      val += num_involved[vars[j]];
    }
    val /= vars.size(); /* average number of involved conflicts */
    q.push(make_pair(val, confs[i]));
  }
  
  vector<Graph::VertexPair> p_removed, u_removed;
  while (!q.empty()){
    size_t pu = q.top().second; q.pop();
    vector<Graph::Edge> adj = p_graph.uAdj(pu);
    for (size_t i = 0; i < adj.size(); ++i){
      p_removed.clear(); u_removed.clear();
      emb.choose_constraint(pu, adj[i].vertex, p_removed, u_removed);
      if (!emb.get_valid()){
	emb.add_back(p_removed, u_removed);
      } else {
	decisions.emplace(pu, i, u_removed, p_removed, adj);
	return true;
      }
    }
  }
  return false;
}
