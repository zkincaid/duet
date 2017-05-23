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
  decision(size_t pu, size_t ppos, const std::vector<Graph::VertexPair>& e) : u(pu), pos(ppos), u_edges(e) {}
  /* move semantics (default) */
  decision(size_t pu, size_t ppos, std::vector<Graph::VertexPair>& e) : u(pu), pos(ppos), u_edges(std::move(e)) {}
  size_t u;
  size_t pos;
  std::vector<Graph::VertexPair> u_edges;
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
    valid_ = u_graph_.unit_prop(tmp);
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
};

#endif
