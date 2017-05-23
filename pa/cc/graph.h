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
    adj_u[u].push_back(Edge(v, adj_v[v].size()));
    adj_v[v].push_back(Edge(u, adj_u[u].size() - 1));
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

  bool unit_prop(std::vector<VertexPair>& removed){
    std::queue<size_t> units;
    for (size_t i = 1; i < adj_u.size(); ++i){
      if (adj_u[i].size() == 0) return false;
      if (adj_u[i].size() == 1 && adj_v[adj_u[i][0].vertex].size() != 1) units.push(i);
    }
    size_t u;
    Edge v, k, l;
    while(!units.empty()){
      u = units.front();
      if (adj_u[u].size() == 1){
	v = adj_u[u][0];
	for (size_t i = 0; i < adj_v[v.vertex].size(); ++i){
	  k = adj_v[v.vertex][i];
	  if (k.vertex != u){
	    adj_u[k.vertex][k.position] = adj_u[k.vertex][adj_u[k.vertex].size()-1];
	    l = adj_u[k.vertex][k.position];
	    adj_v[l.vertex][l.position].position = k.position;
	    adj_u[k.vertex].pop_back();
	    if (adj_u[k.vertex].size() == 1){
	      units.push(k.vertex);
	    }
	    removed.push_back(VertexPair(k.vertex, v.vertex));
	  }
	}
	adj_v[v.vertex].clear();
	adj_v[v.vertex].push_back(Edge(u, 0));
	adj_u[u][0].position = 0;
      } else if (adj_u[u].size() == 0) { /* We can never have a covering matching if u is incident to 0 edges */
	return false;
      }
      units.pop();
    }
    return true;
  }

  /* Remove all edges inconsistent with U[i] |-> V[i],
     Assumptions:
       U.size() == V.size()
       has_edge(U[i], V[i]) = true
   */
  std::vector<VertexPair> remove_edges(const std::vector<int>& U, const std::vector<int>& V){
    std::vector<VertexPair> removed;
    Edge k, l;
    for (size_t i = 0; i < U.size(); ++i){
      size_t u(U[i]), v(V[i]);
      /* Remove anything adjacent to u */
      for (size_t j = 0; j < adj_u[u].size(); ++j){
	k = adj_u[u][j];
	if (k.vertex != v){
	  adj_v[k.vertex][k.position] = adj_v[k.vertex][adj_v[k.vertex].size()-1];
	  l = adj_v[k.vertex][k.position];
	  adj_u[l.vertex][l.position].position = k.position;
	  adj_v[k.vertex].pop_back();
	  removed.push_back(VertexPair(u, k.vertex));
	}
      }
      adj_u[u].clear();
      adj_u[u].push_back(Edge(v,0));
      /* remove anything adjacent to v */
      for (size_t j = 0; j < adj_v[v].size(); ++j){
	k = adj_v[v][j];
	if (k.vertex != u){
          adj_u[k.vertex][k.position] = adj_u[k.vertex][adj_u[k.vertex].size()-1];
	  l = adj_u[k.vertex][k.position];
	  adj_v[l.vertex][l.position].position = k.position;
	  adj_u[k.vertex].pop_back();
	  removed.push_back(VertexPair(k.vertex, v));
        }
      }
      adj_v[v].clear();
      adj_v[v].push_back(Edge(u, 0));
    }
    return removed;
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
