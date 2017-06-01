/********************************************************************************
    Author: Charlie Murphy
    Email:  tcm3@cs.princeton.edu

    Date:   May 19, 2017

    Description: Header file for various types used in embedding algorithm.
    Provides a class interface for combining the universe and predicate graphs
 ********************************************************************************/

#include <vector>
#include <map>
#include <queue>
#include <cstdint>
#include "graph.h"

#ifndef CM_EMBEDDING_H
#define CM_EMBEDDING_H

/* The label for the proposition graph predicate symbol and list of arguments */
struct prop{
  prop (size_t p = 0) : pred(p) {}
  /* copy semantics / cast to const if you want to copy a non-const vector*/
  prop (size_t p, const std::vector<int>& v) : pred(p), vars(v) {}
  /* move semantics (default) */
  prop (size_t p, std::vector<int>& v) : pred(p), vars(std::move(v)) {}
  size_t pred;
  std::vector<int> vars;
};

/* The type of decisions:
     u: vertex in predicate graph
     pos: choice of edge eminating from u
     u_edges : edges of universe graph removed due to decision */
struct decision{
  decision(size_t pu = 0, size_t ppos = 0) : u(pu), pos(ppos) {}
  /* copy semantics */
  decision(size_t pu, size_t ppos, const std::vector<Graph::VertexPair>& ue,
	  const std::vector<Graph::VertexPair>& pe,
	  const std::vector<Graph::Edge>& adj) : u(pu), pos(ppos), u_edges(ue), p_edges(pe), pu_adj(adj) {}
  /* move semantics (default) */
  decision(size_t pu, size_t ppos, std::vector<Graph::VertexPair>& ue,
	  std::vector<Graph::VertexPair>& pe,
	  const std::vector<Graph::Edge>& adj) : u(pu), pos(ppos), u_edges(std::move(ue)), p_edges(std::move(pe)), pu_adj(adj) {}
  size_t u;
  size_t pos;
  std::vector<Graph::VertexPair> u_edges;
  std::vector<Graph::VertexPair> p_edges;
  std::vector<Graph::Edge> pu_adj;
};

/* Assume sig1 and sig2 represent multisets of elements */
bool subset(const std::vector<uint8_t>& sig1, const std::vector<uint8_t>& sig2){
  bool subset(sig1.size() <= sig2.size());
  for (size_t i = 0; subset && i < sig1.size(); ++i){ /* assert(sig1.size() <= sig2.size()) */
    subset = sig1[i] <= sig2[i];
  }
  return subset;
}

class Embedding{
  Graph u_graph_;
  LabeledGraph<prop, prop> p_graph_;
  /* (vert, pos) \in u_inv_label_[u] -> p_graph_.getULabel(vert).vars[pos] = u */
  std::vector<std::vector<Graph::Edge>> u_inv_label_;
  /* (vert, pos) \in u_inv_label_[v] -> p_graph_.getVLabel(vert).vars[pos] = v */
  std::vector<std::vector<Graph::Edge>> v_inv_label_;
  bool valid_;

  /* finish constructing the universe graph */
  void fill_ugraph(const std::vector<std::vector<uint8_t>>& sigs1, const std::vector<std::vector<uint8_t>>& sigs2){
    std::vector<std::vector<size_t>> adj;
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
    /* Add (undirected) edges to universe graph */
    for (size_t i = 1; i < adj.size(); ++i){
      for (size_t j = 0; j < adj[i].size(); ++j){
	u_graph_.add_edge(i, adj[i][j]);
      }
    }

    /* It doesn't matter what is removed */
    std::vector<Graph::VertexPair> tmp;
    std::vector<int> junk;
    valid_ = u_graph_.unit_prop(tmp, junk, junk);
  }

  /* finish constructing the predicate graph */
  void fill_pgraph(){
    for (size_t i = 0; i < p_graph_.uSize(); ++i){
      const prop& u_label = p_graph_.getULabel(i);
      for (size_t j = 0; j < p_graph_.vSize(); ++j){
	const prop& v_label = p_graph_.getVLabel(j);
	if (u_label.pred == v_label.pred){
	  bool mem(true);
	  for (size_t k = 0; mem && k < u_label.vars.size(); ++k){
	    mem = u_graph_.has_edge(u_label.vars[k], v_label.vars[k]);
	  }
	  if (mem) p_graph_.add_edge(i, j);
	}
      }
    }
    for (size_t i = 0; i < p_graph_.uSize(); ++i){
      if (p_graph_.uAdj(i).size() == 1){
	std::vector<Graph::VertexPair> junk;
        choose_constraint(i, p_graph_.uAdj(i)[0].vertex, junk, junk);
	break;
      } else if (p_graph_.uAdj(i).size() == 0){
	valid_ = false;
	break;
      }
    }
  }

  /* construct inverse label */
  void fill_inv_label(){
    u_inv_label_.resize(u_graph_.uSize());
    for (size_t i = 0; i < p_graph_.uSize(); ++i){
      const std::vector<int>& vars = p_graph_.getULabel(i).vars;
      for (size_t k = 0; k < vars.size(); ++k){
	u_inv_label_[vars[k]].emplace_back(i, k);
      }
    }

    v_inv_label_.resize(u_graph_.vSize());
    for (size_t i = 0; i < p_graph_.vSize(); ++i){
      const std::vector<int>& vars = p_graph_.getVLabel(i).vars;
      for (size_t k = 0; k < vars.size(); ++k){
	v_inv_label_[vars[k]].emplace_back(i, k);
      }
    }
  }
  
 public:
  Embedding() : valid_(true) {}

  /* Copy Semantics */
  Embedding(const std::vector<std::vector<uint8_t>>& sigs1, const std::vector<std::vector<uint8_t>>& sigs2,
	    const std::vector<prop>& pu_label, const std::vector<prop>& pv_label) : u_graph_(sigs1.size(), sigs2.size()), valid_(true) {
    fill_ugraph(sigs1, sigs2);
    p_graph_ = std::move(LabeledGraph<prop, prop>(pu_label, pv_label));
    fill_pgraph();
    fill_inv_label();
  }

  /* Move Semantics */
  Embedding(const std::vector<std::vector<uint8_t>>& sigs1, const std::vector<std::vector<uint8_t>>& sigs2,
	    std::vector<prop>& pu_label, std::vector<prop>& pv_label) : u_graph_(sigs1.size(), sigs2.size()), valid_(true) {
    fill_ugraph(sigs1, sigs2);
    p_graph_ = std::move(LabeledGraph<prop, prop>(pu_label, pv_label));
    fill_pgraph();
    fill_inv_label();
  }

  Graph& get_universe_graph() { return u_graph_; }
  const Graph& get_universe_graph() const { return u_graph_; }
  LabeledGraph<prop, prop>& get_predicate_graph() { return p_graph_; }
  const LabeledGraph<prop, prop>& get_predicate_graph() const { return p_graph_; }
  bool get_valid() const { return valid_; }

  /* Assert that the constraint p_graph_.uLabel(pu) |-> p_graph_.vLabel(pv)
     and performs "arc consistency" */
  void choose_constraint(size_t pu, size_t pv, std::vector<Graph::VertexPair>& p_removed,
			 std::vector<Graph::VertexPair>& u_removed){
    /*    const std::vector<int>& u_vars = p_graph_.getULabel(pu).vars;
    const std::vector<int>& v_vars = p_graph_.getVLabel(pv).vars;
    for (size_t i = 0; valid_ && i < u_vars.size(); ++i){
      valid_ = u_graph_.has_edge(u_vars[i], v_vars[i]);
    }
    if (!valid_){
      return;
    }
    std::vector<Graph::VertexPair> tmp = u_graph_.remove_edges(u_vars, v_vars);
    u_removed.insert(u_removed.end(), tmp.begin(), tmp.end());
    std::vector<int> junk;
    valid_ = u_graph_.unit_prop(u_removed, junk, junk); */

    

    std::vector<int> matches;
    matches.resize(u_graph_.uSize(), -1);

    std::vector<Graph::VertexPair> tmp;

    std::vector<int> pu_units, pv_units;
    pu_units.push_back(pu), pv_units.push_back(pv);
    tmp = std::move(p_graph_.remove_edges(pu_units, pv_units));
    p_removed.insert(p_removed.begin(), tmp.begin(), tmp.end());
    if (!p_graph_.unit_prop(p_removed, pu_units, pv_units)) valid_ = false;

    while (valid_ && pu_units.size() != 0){
      std::vector<int> uu_units, uv_units;
      for (size_t i = 0; valid_ && i < pu_units.size(); ++i){
	const std::vector<int>& u_vars = p_graph_.getULabel(pu_units[i]).vars;
	const std::vector<int>& v_vars = p_graph_.getVLabel(pv_units[i]).vars;
	for (size_t k = 0; valid_ && k < u_vars.size(); ++k){
	  if (matches[u_vars[k]] == -1){
	    matches[u_vars[k]] = v_vars[k];
	    uu_units.push_back(u_vars[k]);
	    uv_units.push_back(v_vars[k]);
	  } else if (matches[u_vars[k]] != v_vars[k]){ /* Universe Inconsistency */
	    valid_ = false;
	  }
	}
      }
      if (!valid_) break;
      tmp = std::move(u_graph_.remove_edges(uu_units, uv_units));
      u_removed.insert(u_removed.begin(), tmp.begin(), tmp.end());
      uu_units.clear(); uv_units.clear();
      if (!u_graph_.unit_prop(u_removed, uu_units, uv_units)){
	valid_ = false;
	break;
      }
      pu_units.clear(); pv_units.clear();
      //filter(uu_units, uv_units, p_removed, pu_units, pv_units);
    }
  }

  /* Remove any edge inconsistent with U[i] |-> V[i] in the universe graph */
  void filter(const std::vector<int>& U, const std::vector<int>& V,
	      std::vector<Graph::VertexPair>& removed,
	      std::vector<int>& pu_units, std::vector<int>& pv_units){
    for (size_t i = 0; i < U.size(); ++i){
      const std::vector<Graph::Edge>& u_invs = u_inv_label_[U[i]];
      for (size_t j = 0; j < u_invs.size(); ++j){
	size_t pu = u_invs[j].vertex;
	size_t k = u_invs[j].position;
	const std::vector<Graph::Edge>& adj = p_graph_.uAdj(pu);
	size_t l = 0;
	while (l < adj.size()){
	  if (p_graph_.getVLabel(adj[l].vertex).vars[k] != V[i]){
	    removed.emplace_back(pu, adj[l].vertex);
	    /* Assumes that remove_edge does not affect the
               order of edges at position [0, l) */
	    p_graph_.remove_edge(pu, l);
	  } else {
  	    ++l;
	  }
	}
	if (adj.size() == 1){
	  pu_units.push_back(pu);
	  pv_units.push_back(adj[0].vertex);
	} else if (adj.size() == 0){
	  valid_ = false;
	  return;
	}
      }
    }
    if (!p_graph_.unit_prop(removed, pu_units, pv_units)) valid_ = false;
  }

  void add_back(const std::vector<Graph::VertexPair>& p_edges, const std::vector<Graph::VertexPair>& u_edges){
    valid_ = true;
    for (size_t i = 0; i < p_edges.size(); ++i){
      p_graph_.add_edge(p_edges[i].u, p_edges[i].v);
    }
    for (size_t i = 0; i < u_edges.size(); ++i){
      u_graph_.add_edge(u_edges[i].u, u_edges[i].v);
    }
  }
};

#endif
