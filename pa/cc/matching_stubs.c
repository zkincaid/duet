#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <cstdio>
#include <vector>
#include <string>
#include <cstdint>
#include <map>
#include <queue>
#include <stack>
#include <cmath>
#include <limits>
#include <functional>
#include "graph.h"
#include "embedding.h"
using namespace std;

bool embedding(Embedding emb);
void find_conflicts(const Embedding& emb, const vector<int>& matching, vector<int>& confs);
//void find_conflicts(const LabeledGraph<prop, prop>& p_graph, const vector<int>& matching, vector<int>& confs);
void backtrack(stack<decision>& decisions, Embedding& emb);
//void backtrack(stack<decision>& decisions, const LabeledGraph<prop, prop>& p_graph, Graph& u_graph);
bool choose(stack<decision>& decisions, const vector<int>& confs, Embedding& emb);
//bool choose(stack<decision>& decisions, const vector<int>& confs, const LabeledGraph<prop, prop>& p_graph, Graph& u_graph);

/**********************************************************
  This is the function that is called by the ocaml code
  It processes the ocaml structures to more efficient
  representations and calls the embedding function
  Which determines if str1 is embedded in str2.
***********************************************************/
extern "C" {
  CAMLprim value embedsOCAML(value str1, value str2){ /* str = int * (string * int list) list */
    CAMLparam2(str1, str2);
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
    CAMLreturn(Val_bool(embedding(std::move(Embedding(sig1, sig2, pu_label, pv_label)))));
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
  size_t ans, num(0);

  stack<decision> decisions;
  
  do {
    std::fill(vis.begin(), vis.end(), 0);            /* Reset variables for matching problem */
    ans = u_graph.max_matching(match1, match2, vis); /* Compute maximum cardinality matching */
    ++num;

    if (ans != u_graph.uSize()){
      backtrack(decisions, emb);
    } else {
      find_conflicts(emb, match1, conflicts);
      if (conflicts.size() == 0){
        printf("iterations: %lu\n", num);
        return true;
      }
      if (!choose(decisions, conflicts, emb)){
        backtrack(decisions, emb);
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
  printf("iterations: %lu\n", num);
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
  const LabeledGraph<prop, prop>& p_graph = emb.get_predicate_graph();
  Graph& u_graph = emb.get_universe_graph();
  while(!decisions.empty()){
    decision d = decisions.top(); decisions.pop();
    for (size_t i = 0; i < d.u_edges.size(); ++i){
      u_graph.add_edge(d.u_edges[i].u, d.u_edges[i].v);
    }
    const vector<Graph::Edge>& adj = p_graph.uAdj(d.u);
    const vector<int>& u_vars = p_graph.getULabel(d.u).vars;
    for (size_t k; ++d.pos < adj.size();){
      const vector<int>& v_vars = p_graph.getVLabel(adj[d.pos].vertex).vars;
      for (k = 0; k < u_vars.size(); ++k){
        if (!u_graph.has_edge(u_vars[k], v_vars[k])) break;
      }
      if (k == u_vars.size()){
	vector<Graph::VertexPair> uedges = u_graph.remove_edges(u_vars, v_vars);
	u_graph.unit_prop(uedges);
  	if (u_graph.unit_prop(uedges)){
  	  decisions.emplace(d.u, d.pos, uedges);
	  return;
	} else {
	  for (size_t i = 0; i < uedges.size(); ++i){
	    u_graph.add_edge(uedges[i].u, uedges[i].v);
	  }
	}
      }
    }
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
  Graph& u_graph = emb.get_universe_graph();

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

  while (!q.empty()){
    size_t pu = q.top().second; q.pop();
    const vector<Graph::Edge>& adj = p_graph.uAdj(pu);
    const vector<int>& u_vars = p_graph.getULabel(pu).vars;
    for (size_t j = 0, pv, k; j < adj.size(); ++j){
      pv = adj[j].vertex;
      const vector<int>& v_vars = p_graph.getVLabel(pv).vars;
      for (k = 0; k < u_vars.size(); ++k){
	if (!u_graph.has_edge(u_vars[k], v_vars[k])) break;
      }
      if (k == u_vars.size()){
	vector<Graph::VertexPair> uedges = u_graph.remove_edges(p_graph.getULabel(pu).vars, p_graph.getVLabel(pv).vars);
	if (u_graph.unit_prop(uedges)){
  	  decisions.emplace(pu, j, uedges);
	  return true;
	} else {
	  for (size_t i = 0; i < uedges.size(); ++i){
  	    u_graph.add_edge(uedges[i].u, uedges[i].v);
	  }
	}
      }
    }
  }
  return false;
}
