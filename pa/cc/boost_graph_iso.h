#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/vf2_sub_graph_iso.hpp>
#include <set>
#include <map>
#include <algorithm>
#include <cassert>
#include "embedding.h"
#include "graph.h"
using namespace boost;

#ifndef BOOST_SUBGRAPH_ISO_H
#define BOOST_SUBGRAPH_ISO_H

#define BSIH_DEBUG

template <typename PropertyMapFirst,
          typename PropertyMapSecond,
          typename T>
struct property_map_inclusion {
  property_map_inclusion(const PropertyMapFirst property_map1,
			 const PropertyMapSecond property_map2) :
    m_property_map1(property_map1), m_property_map2(property_map2) {}

  template <typename ItemFirst, typename ItemSecond>
  bool operator()(const ItemFirst& item1, const ItemSecond& item2) {
    const std::set<T>& s1 = get(m_property_map1, item1);
    const std::set<T>& s2 = get(m_property_map2, item2);
    return std::includes(s2.begin(), s2.end(), s1.begin(), s1.end());
  }
private:
  const PropertyMapFirst& m_property_map1;
  const PropertyMapSecond& m_property_map2;
};

template <typename Graph1,
          typename Graph2>
struct VF2_do_once_callback {
  VF2_do_once_callback(const Graph1& graph1, const Graph2& graph2,
		       bool* iso) : graph1_(graph1), graph2_(graph2),
                                    iso_(iso) { *iso_ = false; }

  template<typename CorrespondenceMap1to2,
           typename CorrespondenceMap2to1>
  bool operator()(const CorrespondenceMap1to2& map1,
		  const CorrespondenceMap2to1& map2) {
    (*iso_) = true;
    return false;
  }

private:
  const Graph1& graph1_;
  const Graph2& graph2_;
  bool* iso_;
};

bool boost_embeds(const Embedding& emb) {
  typedef boost::property<edge_name_t, std::set<size_t> > edge_property;
  typedef boost::property<vertex_name_t, std::set<size_t>, property<vertex_index_t, int>> vertex_property;

  typedef boost::adjacency_list<vecS, vecS, bidirectionalS, vertex_property, edge_property> graph_type;

  // Build graph1
  graph_type graph1;

  const Graph& u_graph = emb.get_universe_graph();
  const LabeledGraph<prop, prop>& p_graph = emb.get_predicate_graph();
  for (size_t i = 1; i < u_graph.uSize(); ++i){
    std::set<size_t> vprop;
    vprop.insert(i);
    #ifdef BSIH_DEBUG
    printf("%lu -{%lu}\n", i-1, i);
    #endif
    add_vertex(vertex_property(vprop), graph1);
  }
  
  std::map<size_t, std::map<size_t, std::set<size_t>>> edge_labels;
  for (size_t i = 0; i < p_graph.uSize(); ++i){
    const prop& p = p_graph.getULabel(i);
    assert (p.vars.size() == 2);
    edge_labels[p.vars[0]-1][p.vars[1]-1].insert(p.pred);
  }

  for (auto it = edge_labels.begin(); it != edge_labels.end(); ++it){
    for (auto it2 = it->second.begin(); it2 != it->second.end(); ++it2){
      #ifdef BSIH_DEBUG
      printf("%lu --{", it->first);
      for (auto sit = it2->second.begin(); sit != it2->second.end(); ++sit){
	printf("%lu, ", *sit);
      }
      printf("}--> %lu\n", it2->first);
      #endif
      add_edge(it->first, it2->first, edge_property(it2->second), graph1);
    }
  }

  // Build graph2
  graph_type graph2;

  for (size_t i = 1; i < u_graph.vSize(); ++i){
    const std::vector<Graph::Edge>& vAdj = u_graph.vAdj(i);
    std::set<size_t> vprop;
    #ifdef BSIH_DEBUG
    printf("%lu -{", i-1);
    #endif
    for (size_t j = 0; j < vAdj.size(); ++j){
      vprop.insert(vAdj[j].vertex);
      #ifdef BSIH_DEBUG
      printf("%lu, ", vAdj[j].vertex);
      #endif
    }
    #ifdef BSIH_DEBUG
    printf("}\n");
    #endif
    add_vertex(vertex_property(vprop), graph2);
  }

  std::map<size_t, std::map<size_t, std::set<size_t>>> edge2_labels;
  for (size_t i = 0; i < p_graph.vSize(); ++i){
    const prop& p = p_graph.getVLabel(i);
    assert (p.vars.size() == 2);
    edge2_labels[p.vars[0]-1][p.vars[1]-1].insert(p.pred);
  }

  for (auto it = edge2_labels.begin(); it != edge2_labels.end(); ++it){
    for (auto it2 = it->second.begin(); it2 != it->second.end(); ++it2){
      #ifdef BSIH_DEBUG
      printf("%lu --{", it->first);
      for (auto sit = it2->second.begin(); sit != it2->second.end(); ++sit){
	printf("%lu, ", *sit);
      }
      printf("}--> %lu\n", it2->first);
      #endif
      add_edge(it->first, it2->first, edge_property(it2->second), graph2);
    }
  }

  typedef property_map<graph_type, vertex_name_t>::type vertex_name_map_t;
  typedef property_map_inclusion<vertex_name_map_t, vertex_name_map_t, size_t> vertex_comp_t;
  vertex_comp_t vertex_comp(get(vertex_name, graph1), get(vertex_name, graph2));

  typedef property_map<graph_type, edge_name_t>::type edge_name_map_t;
  typedef property_map_inclusion<edge_name_map_t, edge_name_map_t, size_t> edge_comp_t;
  edge_comp_t edge_comp(get(edge_name, graph1), get(edge_name, graph2));

  bool is_iso(false);
  VF2_do_once_callback<graph_type, graph_type> callback(graph1, graph2, &is_iso);

  vf2_subgraph_iso(graph1, graph2, std::ref(callback), vertex_order_by_mult(graph1), edges_equivalent(edge_comp).vertices_equivalent(vertex_comp));

  return is_iso;
}


#endif
