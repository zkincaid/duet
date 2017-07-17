#include <gecode/int.hh>
#include <vector>
#include <map>
#include <ctime>
#include "embedding.h"

#ifndef GECODE_EMBEDDING_H
#define GECODE_EMBEDDING_H

class ConstraintEmbedding : public Gecode::Space {
 protected:
  Gecode::IntVarArray l;
 public:
  ConstraintEmbedding(const Embedding& emb) : l(*this, emb.get_universe_graph().uSize()-1, 1, emb.get_universe_graph().vSize()) {
    const Graph& u_graph = emb.get_universe_graph();
    Gecode::BoolVar y(*this, 0, 1);

    /* Setup the domain of each variable */
    for (size_t i = 1; i < u_graph.uSize(); ++i){
      std::vector<int> tmp;
      const std::vector<Graph::Edge>& adj = u_graph.uAdj(i);
      for (size_t j = 0; j < adj.size(); ++j){
	tmp.push_back(adj[j].vertex);
      }
      dom(*this, l[i-1], Gecode::IntSet(Gecode::IntArgs(tmp)));
    }
    distinct(*this, l);

    /* Add Constraints Here */
    const LabeledGraph<prop, prop>& p_graph = emb.get_predicate_graph();
    for (size_t i = 0; i < p_graph.uSize(); ++i){
      const std::vector<Graph::Edge>& adj = p_graph.uAdj(i);
      const std::vector<int>& u_vars = p_graph.getULabel(i).vars;

      assert(adj.size() != 0);
      Gecode::BoolVarArray disj_constraint(*this, adj.size(), 0, 1);
      for (size_t j = 0; j < adj.size(); ++j){
	const std::vector<int>& v_vars = p_graph.getVLabel(adj[j].vertex).vars;
	Gecode::BoolVarArray conj_constraint(*this, u_vars.size(), 0, 1);
	for (size_t k = 0; k < u_vars.size(); ++k){
	  rel(*this, l[u_vars[k]-1], Gecode::IRT_EQ, v_vars[k], conj_constraint[k]);
	}
	rel(*this, Gecode::BOT_AND, conj_constraint, disj_constraint[j]);
      }
      rel(*this, Gecode::BOT_OR, disj_constraint, 1);
    }
    Gecode::IntCHB chb(*this, l,
    	    [](const Gecode::Space& home, Gecode::IntVar x, int i){
    		 return 0.0;
    	       });
    branch(*this, l, Gecode::tiebreak(Gecode::INT_VAR_CHB_MAX(chb), Gecode::INT_VAR_SIZE_MIN(), Gecode::INT_VAR_RND(time(NULL))), Gecode::INT_VAL_RND(time(NULL)));
  }

  ConstraintEmbedding(bool share, ConstraintEmbedding& s) : Gecode::Space(share, s) {
    l.update(*this, share, s.l);
  }

  virtual Gecode::Space* copy(bool share){
    return new ConstraintEmbedding(share, *this);
  }

  void print(){
    printf("[");
    for(int i = 0; i < l.size(); ++i){
      printf("{");
      bool first(true);
      for (Gecode::IntVarRanges j(l[i]); j(); ++j){
	if (!first){
	  printf(", ");
	} else {
	  first = false;
	}
	if (j.min() == j.max()){
	  printf("%d", j.min());
	} else if (j.max() - j.min() == 1){
	  printf("%d, %d", j.min(), j.max());
	} else {
	  printf("%d..%d", j.min(), j.max());
	}
      }
      printf("}");
      if (i+1 != l.size()){
	printf(", ");
      }
    }
    printf("]\n");
  }
};

#endif
