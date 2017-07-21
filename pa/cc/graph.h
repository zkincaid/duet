/*******************************************************************
    Author: Charlie Murphy
    Email:  tcm3@cs.princeton.edu

    Date:   April 25, 2017

    Description: This file provides an implementation of bipartite graphs.

    Assumptions: G.U = 1..n
                 G.V = 1..m
 *******************************************************************/
#include <vector>
#include <queue>
#include <cassert>

#ifndef CM_GRAPH_H
#define CM_GRAPH_H

/************************************************************
  A Bipartite Graph represented as two adjacency lists --
  edges from u and reverse edges from v -- for quick removal.
 ************************************************************/
class Graph{
 public:
  /* The Type of Edges */
  struct Edge{
    Edge(size_t v = 0, size_t p = 0) : vertex(v), position(p) {}
    size_t vertex;    /* outgoing vertex */
    size_t position;  /* position of reverse edge */
  };

  /* A pair of vertices (u, v) */
  struct VertexPair{
    VertexPair(size_t uv = 0, size_t vv = 0) : u(uv), v(vv) {}
    size_t u;
    size_t v;
  };
  
  Graph(size_t u_size = 0, size_t v_size = 0){
    adj_u.resize(u_size);
    adj_v.resize(v_size);
  }

  /***********************************************
    Functions to access part's of the graph
   ***********************************************/
  size_t uSize() const { return adj_u.size(); }
  size_t vSize() const { return adj_v.size(); }

  std::vector<Edge>& uAdj(size_t u){ return adj_u[u]; }
  const std::vector<Edge>& uAdj(size_t u) const { return adj_u[u]; }
  std::vector<Edge>& vAdj(size_t v){ return adj_v[v]; }
  const std::vector<Edge>& vAdj(size_t v) const { return adj_v[v]; }

  /* Simple linear search for v in adj_u[u]
     We could do logarithmic if we maintained
     adj_u[u] was sorted (but adding edges
     would be linear time then) */
  bool has_edge(size_t u, size_t v) const {
    if (u >= adj_u.size()) return false;

    for (size_t i = 0; i < adj_u[u].size(); ++i){
      if (adj_u[u][i].vertex == v)
	return true;
    }
    return false;
  }
  
  /* Adds edge (u,v) to the graph */
  void add_edge(size_t u, size_t v){
    if (adj_u.size() <= u){
      adj_u.resize(u+1);
    }
    if (adj_v.size() <= v){
      adj_v.resize(v+1);
    }
    adj_u[u].emplace_back(v, adj_v[v].size());
    adj_v[v].emplace_back(u, adj_u[u].size() - 1);
  }

  /* Ford Fulkerson algorithm for Bipartite Maximum Matching
     Assumptions:
       matches_u and matches_v form a consistent partial matching (-1 for no selected match)
         i.e. forall i j, matches_u[i] = -1 = matches_u[v] \/ (j in Adj_u[i] /\ matches_u[i] = j /\ matches[j] = i)
       forall i, vis[i] = 0
  */
  size_t max_matching(std::vector<int>& matches_u, std::vector<int>& matches_v, std::vector<int>& vis) const {
    size_t ans = 1;
    for (size_t i = 1; i < adj_u.size(); ++i){
      ans += (matches_u[i] != -1) || dfs(matches_u, matches_v, vis, i, i);
    }
    return ans;
  }

  bool unit_prop(std::vector<VertexPair>& removed, std::vector<int>& u_units, std::vector<int>& v_units){
    std::queue<size_t> units;
    for (size_t i = 1; i < adj_u.size(); ++i){
      if (adj_u[i].size() == 0) return false;
      if (adj_u[i].size() == 1 && adj_v[adj_u[i][0].vertex].size() != 1) units.push(i);
    }
    size_t u;
    Edge k, v;
    while(!units.empty()){
      u = units.front();
      if (adj_u[u].size() == 1){
	v = adj_u[u][0];
  	u_units.push_back(u); v_units.push_back(v.vertex);
	size_t i = 0;
	while (i < adj_v[v.vertex].size()){
	  k = adj_v[v.vertex][i];
	  if (k.vertex != u){
	    remove_edge(k.vertex, k.position);
	    removed.emplace_back(k.vertex, v.vertex);
	    if (adj_u[k.vertex].size() == 1 && adj_v[adj_u[k.vertex][0].vertex].size() != 1){
	      units.push(k.vertex);
	    }
	  } else {
	    ++i;
	  }
	}
      } else if (adj_u[u].size() == 0) { /* We can never have a covering matching if u is incident to 0 edges */
	return false;
      }
      units.pop();
    }
    return true;
  }

  /* Remove a single edge
     Assumption:
       ajd_u[u][pos] = {v, pos'} <->
       adj_v[v][pos'] = {u, pos}
   */
  void remove_edge(size_t u, size_t pos){
    Edge k = adj_u[u][pos], l;
    if (pos != adj_u[u].size() - 1){
      adj_u[u][pos] = l = adj_u[u].back();
      adj_v[l.vertex][l.position].position = pos;
    }
    if (k.position != adj_v[k.vertex].size()-1){
      adj_v[k.vertex][k.position] = l = adj_v[k.vertex].back();
      adj_u[l.vertex][l.position].position = k.position;
    }
    adj_u[u].pop_back();
    adj_v[k.vertex].pop_back();
  }

  /* Remove all edges inconsistent with U[i] |-> V[i],
     Assumptions:
       U.size() == V.size()
   */
  std::vector<VertexPair> commit_edges(const std::vector<int>& U, const std::vector<int>& V){
    std::vector<VertexPair> removed;
    for (size_t i = 0; i < U.size(); ++i){
      size_t u(U[i]), v(V[i]);
      size_t j = 0;
      /* Remove anything adjacent to u that is not v */
      while (j < adj_u[u].size()){
	if (adj_u[u][j].vertex != v){
	  removed.emplace_back(u, adj_u[u][j].vertex);
	  remove_edge(u, j);
	} else {
	  ++j;
	}
      }
      j = 0;
      /* Remove anything adjacent to v that is not u */
      while (j < adj_v[v].size()){
	if (adj_v[v][j].vertex != u){
	  removed.emplace_back(adj_v[v][j].vertex, v);
	  remove_edge(adj_v[v][j].vertex, adj_v[v][j].position);
	} else {
	  ++j;
	}
      }
    }
    return removed;
  }

  /* Print the adjacency list of the graph [u -> v] */
  void print_graph() const {
    for (size_t i = 0; i < adj_u.size(); ++i){
      printf("%lu |-> {", i);
      for (size_t j = 0; j < adj_u[i].size(); ++j){
	if (j != adj_u[i].size() -1){
  	  printf("[%lu, %lu], ", adj_u[i][j].vertex, adj_u[i][j].position);
	} else {
	  printf("[%lu, %lu]", adj_u[i][j].vertex, adj_u[i][j].position);
	}
      }
      printf("}\n");
    }
  }

  /* Print the reverse adjacency list of the graph [v -> u] */
  void print_vgraph() const {
    for (size_t i = 0; i < adj_v.size(); ++i){
      printf("%lu |- {", i);
      for (size_t j = 0; j < adj_v[i].size(); ++j){
	if (j != adj_v[i].size() - 1){
  	  printf("[%lu, %lu], ", adj_v[i][j].vertex, adj_v[i][j].position);
	} else {
	  printf("[%lu, %lu]", adj_v[i][j].vertex, adj_v[i][j].position);
	}
      }
      printf("}\n");
    }
  }

  /* Does the graph invariant hold: useful for debugging issues */
  bool check() const {
    Edge k;
    for (size_t i = 0; i < adj_u.size(); ++i){
      for (size_t j = 0; j < adj_u[i].size(); ++j){
	k = adj_u[i][j];
	if (k.vertex < adj_v.size() && k.position < adj_v[k.vertex].size()){
  	  k = adj_v[k.vertex][k.position];
	  if (k.vertex != i || k.position != j){
	    printf("Error: u_reverse_mapping not correct (%lu, %lu)\n", i, j);
	    return false;
	  }
	} else {
	  printf("Error: u_forward out of bounds (%lu, %lu)\n", i, j);
	  return false;
	}
      }
    }
    for (size_t i = 0; i < adj_v.size(); ++i){
      for (size_t j = 0; j < adj_v[i].size(); ++j){
	k = adj_v[i][j];
	if (k.vertex < adj_u.size() && k.position < adj_u[k.vertex].size()){
	  k = adj_u[k.vertex][k.position];
	  if (k.vertex != i || k.position != j){
	    printf("Error: v_reverse_mapping not correct (%lu, %lu)\n", i, j);
	    return false;
	  }
	} else {
	  printf("Error: v_forward out of bounds (%lu, %lu)\n", i, j);
	  return false;
	}
      }
    }
    return true;
  }

 private:
  std::vector<std::vector<Edge>> adj_u;
  std::vector<std::vector<Edge>> adj_v;

  /* Depth First Search as part of Ford Fulkerson Algorithm */
  bool dfs(std::vector<int>& matches_u, std::vector<int>& matches_v, std::vector<int>& vis, int x, int iter) const {
    if (vis[x] == iter) return false;
    vis[x] = iter;
    for (size_t i = 0; i < adj_u[x].size(); ++i){
      int y = adj_u[x][i].vertex;
      if (matches_v[y] < 0 || dfs(matches_u, matches_v, vis, matches_v[y], iter)){
	matches_v[y] = x;
	matches_u[x] = y;
	return true;
      }
    }
    return false;
  }
};

/******************************************************************
    A labeled graph: A Graph where each vertex has a label
 ******************************************************************/
template <class UT, class VT>
class LabeledGraph : public Graph {
 public:
  LabeledGraph () {}
  
  /* use copy semantics for vectors */
  LabeledGraph (const std::vector<UT>& u_label, const std::vector<VT>& v_label) :
    Graph(u_label.size(), v_label.size()),
    labels_u(u_label), labels_v(v_label) {}

  /* should use move semantics for vectors */
  LabeledGraph (std::vector<UT>& u_label, std::vector<VT>& v_label) :
    Graph(u_label.size(), v_label.size()),
    labels_u(std::move(u_label)), labels_v(std::move(v_label)) {}

  /*****************************
   Get the label at vertex u / v
   *****************************/
  const UT& getULabel(size_t u) const {
    return labels_u[u];
  }

  UT& getULabel(size_t u) {
    return labels_u[u];
  }

  const VT& getVLabel(size_t v) const {
    return labels_v[v];
  }

  VT& getVLabel(size_t v) {
    return labels_v[v];
  }

  /**************************************
   Set label at vertex u/v to u_val/v_val
  ***************************************/
  void setULabel(size_t u, const UT& u_val){
    labels_u[u] = u_val;
  }

  void setVLabel(size_t v, const VT& v_val){
    labels_v[v] = v_val;
  }
  
 private:
  std::vector<UT> labels_u;
  std::vector<VT> labels_v;
};

#endif
