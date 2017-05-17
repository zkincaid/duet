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
#include "graph.h"
using namespace std;

/* The label for the proposition graph (pgraph) (simply the predicate symbol and list of arguments) */
struct prop{
  prop(size_t p = 0) : pred(p) {}
  size_t pred;
  vector<int> vars;
};

/* The type of decisions. It's a vertex in pgraph.U and position in it's adjacency list
   representing an edge of the predicate graph we must satisfy.
   edges, are the edges of the universe graph we removed in-order to gaurantee the
   decision is satisfied */
struct decision{
  decision(size_t pu = 0, size_t ppos = 0) : u(pu), pos(ppos) {}
  decision(size_t pu, size_t ppos, const vector<Graph::VertexPair>& e) : u(pu), pos(ppos), u_edges(e) {}
  size_t u;                          /* pgraph vertex decided on */
  size_t pos;                        /* position of edge */
  vector<Graph::VertexPair> u_edges; /* edges removed due to this decision */
};

Graph make_graph(const vector<vector<uint8_t>>& sigs1, const vector<vector<uint8_t>>& sigs2);
LabeledGraph<prop, prop> make_pgraph(const Graph& u_graph, const vector<prop>& u_label, const vector<prop>& v_label);
bool embedding(const vector<vector<uint8_t>>& sigs1, const vector<vector<uint8_t>>& sigs2,
	       const vector<prop>& pu_label, const vector<prop>& pv_label);
void find_conflicts(const LabeledGraph<prop, prop>& p_graph, const vector<int>& matching, vector<int>& confs);
void backtrack(stack<decision>& decisions, const LabeledGraph<prop, prop>& p_graph, Graph& u_graph);
bool choose(stack<decision>& decisions, const vector<int>& confs, const LabeledGraph<prop, prop>& p_graph, Graph& u_graph);

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
    CAMLreturn(Val_bool(embedding(sig1, sig2, pu_label, pv_label)));
  }
}

/* Is there an injective homomorphism between (pu_label, sigs1) and (pv_label, sigs2)
   More specifically the two structures they represent */
bool embedding(const vector<vector<uint8_t>>& sigs1, const vector<vector<uint8_t>>& sigs2,
	       const vector<prop>& pu_label, const vector<prop>& pv_label){
  Graph u_graph = make_graph(sigs1, sigs2);
  LabeledGraph<prop, prop> p_graph = make_pgraph(u_graph, pu_label, pv_label);
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
      backtrack(decisions, p_graph, u_graph);
    } else {
      find_conflicts(p_graph, match1, conflicts);
      if (conflicts.size() == 0){
        printf("iterations: %lu\n", num);
        return true;
      }
      if (!choose(decisions, conflicts, p_graph, u_graph)){
        backtrack(decisions, p_graph, u_graph);
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

bool subset(const vector<uint8_t>& sig1, const vector<uint8_t>& sig2){
  bool subset(sig1.size() <= sig2.size());
  for (size_t i = 0; subset && i < sig1.size(); ++i){ /* assert(sig1.size() <= sig2.size()) */
    subset = sig1[i] <= sig2[i];
  }
  return subset;
}

/* Makes the universe graph */
Graph make_graph(const vector<vector<uint8_t> >& sigs1, const vector<vector<uint8_t> >& sigs2){
  Graph g(sigs1.size(), sigs2.size());
  vector<vector<int>> adj;
  adj.resize(sigs1.size());

  /* use adj as placeholder in order to safely parallel ize */
  #pragma omp parallel for schedule(guided)
  for (size_t i = 1; i < sigs1.size(); ++i){
    for (size_t j = 1; j < sigs2.size(); ++j){
      if (subset(sigs1[i], sigs2[j])){
	adj[i].push_back(j);
      }
    }
  }

  /* create reverse edges for quick lookup */
  for (size_t i = 1; i < adj.size(); ++i){
    for (size_t j = 0; j < adj[i].size(); ++j){
      g.add_edge(i, adj[i][j]);
    }
  }

  vector<Graph::VertexPair> tmp; /* It doesn't mater what is removed */
  g.unit_prop(tmp);
  return g;
}

/* Makes the predicate graph. There is an edge from i \in [0, u_label.size()) to
   j \in [0, v_label.size()) if u_label[i].prop == v_label[j].prop and
   forall (u, v) \in u_label[i].vars x v_label[j], (u, v) is in the universe graph */
LabeledGraph<prop,prop> make_pgraph(const Graph& u_graph, const vector<prop>& u_label, const vector<prop>& v_label){
  LabeledGraph<prop, prop> p_graph(u_label, v_label);

  for (size_t i = 0; i < u_label.size(); ++i){
    for (size_t j = 0; j < v_label.size(); ++j){
      if (u_label[i].pred == v_label[j].pred){
       	bool mem(true);
	for (size_t k = 0; mem && k < u_label[i].vars.size(); ++k){
	  mem = u_graph.has_edge(u_label[i].vars[k], v_label[j].vars[k]);
	}
	if (mem) p_graph.add_edge(i, j);
      }
    }
  }
  return p_graph;
}

/* Finds all vertices in pgraph.U that are violated by the candidate matching */
void find_conflicts(const LabeledGraph<prop, prop>& p_graph, const vector<int>& matching, vector<int>& confs){
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
void backtrack(stack<decision>& decisions, const LabeledGraph<prop, prop>& p_graph, Graph& u_graph){
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
        decisions.push(decision(d.u, d.pos, u_graph.remove_edges(u_vars, v_vars)));
        return;
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
bool choose(stack<decision>& decisions, const vector<int>& confs, const LabeledGraph<prop, prop>& p_graph, Graph& u_graph){
  vector<size_t> num_involved = num_conflicts(p_graph, confs);
  size_t best_u(0), best_v(0), best_j(0);
  double best_val = 0;
  for (size_t i = 0, pu; i < confs.size(); ++i){
    pu = confs[i];
    const vector<Graph::Edge>& adj = p_graph.uAdj(pu);
    const vector<int>& u_vars = p_graph.getULabel(pu).vars;
    for (size_t j = 0, pv, k; j < adj.size(); ++j){
      pv = adj[j].vertex;
      const vector<int>& v_vars = p_graph.getVLabel(pv).vars;
      for (k = 0; k < u_vars.size(); ++k){
	if (!u_graph.has_edge(u_vars[k], v_vars[k])) break;
      }
      if (k == u_vars.size()){
     	double val(0);
	for (k = 0; k < u_vars.size(); ++k){
	  val += num_involved[u_vars[k]];
	}
	val /= u_vars.size(); /* average number of involved conflicts */
	if (best_val < val){
	  best_val = val;
	  best_u = pu;
	  best_v = pv;
	  best_j = j;
	}
        /* decisions.push(decision(pu, j, remove_edges(u_label[pu].vars, v_label[pv].vars, adj_u, adj_v)));
	   return true; */
      }
    }
  }
  if (best_val != 0){
    decisions.push(decision(best_u, best_j, u_graph.remove_edges(p_graph.getULabel(best_u).vars, p_graph.getVLabel(best_v).vars)));
    return true;
  }
  return false;
}
