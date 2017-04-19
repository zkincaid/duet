#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <cstdio>
#include <vector>
#include <string>
#include <cstdint>
#include <map>
#include <queue>
#include <stack>
using namespace std;

/* The type of edges in the universe graph */
struct edge{
  edge(size_t vertex = 0, size_t position = 0) : vert(vertex), pos(position) {}
  size_t vert; /* outgoing vertex */
  size_t pos;  /* position of reverse edge */
};

/* The label for the proposition graph (pgraph) (simply the predicate symbol and list of arguments) */
struct prop{
  prop(size_t p = 0) : pred(p) {}
  size_t pred;
  vector<int> vars;
};

/* an abstract edge (u, v) (i.e. just a pair of size_t) */
struct vpair{
  vpair(size_t uv = 0, size_t vv = 0) : u(uv), v(vv) {}
  size_t u;
  size_t v;
};

/* The type of decisions. It's a vertex in pgraph.U and position in it's adjacency list
   representing an edge of the predicate graph we must satisfy.
   edges, are the edges of the universe graph we removed in-order to gaurantee the
   decision is satisfied */
struct decision{
  decision(size_t pu = 0, size_t ppos = 0) : u(pu), pos(ppos) {}
  decision(size_t pu, size_t ppos, const vector<vpair>& e) : u(pu), pos(ppos), edges(e) {}
  size_t u;            /* pgraph vertex decided on */
  size_t pos;          /* position of edge */
  vector<vpair> edges; /* edges removed due to this decision */
};

void make_graph(const vector<vector<uint64_t>>& sigs1, const vector<vector<uint64_t>>& sigs2,
		vector<vector<edge>>& ajd_u, vector<vector<edge>>& adj_v);
void make_pgraph(const vector<vector<edge>>& adj_u, const vector<vector<edge>>& adj_v,
		 const vector<prop>& u_label, const vector<prop>& v_label, vector<vector<int>>& pgraph);
bool has_edge(const vector<vector<edge>>& adj, size_t u, size_t v);
void unit_prop(vector<vector<edge>>& adj_u, vector<vector<edge>>& adj_v, vector<vpair>& removed);
void print_graph(const vector<vector<int>>& adj_u);
bool embedding(const vector<vector<uint64_t>>& sigs1, const vector<vector<uint64_t>>& sigs2,
	       const vector<prop>& pu_label, const vector<prop>& pv_label);
size_t max_matching(const vector<vector<edge>>& adj, vector<int>& match1, vector<int>& match2, vector<int>& vis, int iter);
bool dfs(const vector<vector<edge>>& adj, vector<int>& match1, vector<int>& match2, vector<int>& vis, int x, int iter);
void find_conflicts(const vector<vector<int>>& pgraph, const vector<prop>& u_label, const vector<prop>& v_label,
	            const vector<int>& matching, vector<int>& confs);
void backtrack(stack<decision>& decisions, const vector<vector<int>>& pgraph, const vector<prop>& u_label, const vector<prop>& v_label,
	       vector<vector<edge>>& adj_u, vector<vector<edge>>& adj_v);
bool choose(stack<decision>& decisions, const vector<int>& confs,
	    const vector<vector<int>>& pgraph, const vector<prop>& u_label, const vector<prop>& v_label,
	    vector<vector<edge>>& adj_u, vector<vector<edge>>& adj_v);

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
    
    vector<vector<uint64_t> > sig1, sig2;   /* Signature of str1 and str2 respectively */
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

	if (sig1[arg].size() <= (predi >> 6)){
	  sig1[arg].resize((predi >> 6) + 1, 0);
	}
	sig1[arg][predi >> 6] |= (1 << (predi & 63)); /* >> 6 = / 64 and (& 63) = % 64 */
	
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
	
	if (sig2[arg].size() <= (predi >> 6)){
	  sig2[arg].resize((predi >> 6)+1, 0);
	}
	sig2[arg][predi >> 6] |= (1 << (predi & 63)); /* >> 6 = / 64 and (& 63) = % 64 */

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

/*******************************************************************
  Simple functionality for printing the adjacency list representation
  of the universe graph.
 *******************************************************************/
void print_graph(const vector<vector<edge>>& adj){
  for (size_t i = 0; i < adj.size(); ++i){
    printf("%lu |-> {", i);
    for (size_t j = 0; j < adj[i].size(); ++j){
      printf("%lu", adj[i][j].vert);
      if (j != adj[i].size()-1){
	printf(", ");
      }
    }
    printf("}\n");
  }
}

/**********************************************************************
  Simple functionality for printing the proposition graph
 **********************************************************************/
void print_pgraph(const vector<vector<int>>& pgraph, const vector<prop>& u_label, const vector<prop>& v_label){
  for (size_t i = 0; i < pgraph.size(); ++i){
    printf("<");
    for (size_t j = 0; j < u_label[i].vars.size(); ++j){
      printf("%d", u_label[i].vars[j]);
      if (j != u_label[i].vars.size()-1){
	printf(" ");
      }
    }
    printf("> |=> ");
    for (size_t j = 0; j < pgraph[i].size(); ++j){
      printf("<");
      for (size_t k = 0; k < v_label[pgraph[i][j]].vars.size(); ++k){
	printf("%d", v_label[pgraph[i][j]].vars[k]);
	if (k != v_label[pgraph[i][j]].vars.size()-1){
	  printf(" ");
	}
      }
      printf(">");
      if (j != pgraph[i].size()-1){
	printf(" ");
      }
    }
    printf("\n");
  }
}

/* Is there an injective homomorphism between (pu_label, sigs1) and (pv_label, sigs2)
   More specifically the two structures they represent */
bool embedding(const vector<vector<uint64_t>>& sigs1, const vector<vector<uint64_t>>& sigs2,
	       const vector<prop>& pu_label, const vector<prop>& pv_label){
  vector<vector<edge>> adj_u, adj_v;
  make_graph(sigs1, sigs2, adj_u, adj_v); /* Populate the universe graph */
  vector<vector<int>> p_graph;
  make_pgraph(adj_u, adj_v, pu_label, pv_label, p_graph); /* Populate the propisition graph */
  vector<int> match1, match2, vis, conflicts;
  int iter;

  match1.resize(adj_u.size(), -1);
  match2.resize(adj_v.size(), -1);
  vis.resize(adj_u.size(), 0);
  size_t ans;

  stack<decision> decisions;
  
  do {
    iter = 0;
    std::fill(vis.begin(), vis.end(), 0);                 /* Reset variables for matching problem */
    std::fill(match1.begin(), match1.end(), -1);
    std::fill(match2.begin(), match2.end(), -1);
    ans = max_matching(adj_u, match1, match2, vis, iter); /* Compute maximum cardinality matching */

    if (ans != adj_u.size()){
      backtrack(decisions, p_graph, pu_label, pv_label, adj_u, adj_v);
    } else {
      find_conflicts(p_graph, pu_label, pv_label, match1, conflicts);
      if (conflicts.size() == 0){
	return true;
      }
      if (!choose(decisions, conflicts, p_graph, pu_label, pv_label, adj_u, adj_v)){
        backtrack(decisions, p_graph, pu_label, pv_label, adj_u, adj_v);
      }
    }
  } while(!decisions.empty());
  return false;
}

bool subset(const vector<uint64_t>& sig1, const vector<uint64_t>& sig2){
  bool subset(sig1.size() <= sig2.size());
  for (size_t i = 0; subset && i < sig1.size(); ++i){ /* assert(sig1.size() <= sig2.size()) */
    subset = ((sig1[i] & sig2[i]) == sig1[i]);
  }
  return subset;
}

/* Unit Propagation for Maximum Matching Algorithms on Bipartite Graph
   If any vertex has only one outgoing edge it must obviously match
   to that vertex */
void unit_prop(vector<vector<edge>>& adj_u, vector<vector<edge>>& adj_v, vector<vpair>& removed){
  queue<size_t> units;
  for (size_t i = 0; i < adj_u.size(); ++i){
    if (adj_u[i].size() == 1){
      units.push(i);
    }
  }
  size_t u;
  edge v, k, l;
  while(!units.empty()){
    u = units.front();
    if (adj_u[u].size() == 1){
      v = adj_u[u][0];
      for (size_t i = 0; i < adj_v[v.vert].size(); ++i){
	k = adj_v[v.vert][i];
	if (k.vert != u){
	  adj_u[k.vert][k.pos] = adj_u[k.vert][adj_u[k.vert].size()-1];
	  l = adj_u[k.vert][k.pos];
	  adj_v[l.vert][l.pos].pos = k.pos;
	  adj_u[k.vert].pop_back();
	  if (adj_u[k.vert].size() == 1){
	    units.push(k.vert);
	  }
	  removed.push_back(vpair(k.vert, v.vert));
	}
      }
      adj_v[v.vert].clear();
      adj_v[v.vert].push_back(edge(u, 0));
      adj_u[u][0].pos = 0;
    }
    units.pop();
  }
}

/* Makes the universe graph */
void make_graph(const vector<vector<uint64_t> >& sigs1, const vector<vector<uint64_t> >& sigs2,
		 vector<vector<edge>>& adj_u, vector<vector<edge>>& adj_v){
  adj_u.resize(sigs1.size()); /* assume adj_u and adj_v are previously empty / cleared */
  adj_v.resize(sigs2.size());

  #pragma omp parallel for schedule(guided)
  for (size_t i = 1; i < sigs1.size(); ++i){
    for (size_t j = 1; j < sigs2.size(); ++j){
      if (subset(sigs1[i], sigs2[j])){
	adj_u[i].push_back(edge(j));
      }
    }
  }

  /* create reverse edges for quick lookup */
  for (size_t i = 1; i < adj_u.size(); ++i){
    for (size_t j = 0; j < adj_u[i].size(); ++j){
      adj_u[i][j].pos = adj_v[adj_u[i][j].vert].size();
      adj_v[adj_u[i][j].vert].push_back(edge(i, j));
    }
  }
  vector<vpair> tmp; /* It doesn't mater what was removed */
  unit_prop(adj_u, adj_v, tmp);
}

/* simple linear search; while the adjacency lists are originally sorted
   removing and adding edges violates this property */
bool has_edge(const vector<vector<edge>>& adj, size_t u, size_t v){
  if (u >= adj.size()){ return false; }

  for (size_t i = 0; i < adj[u].size(); ++i){
    if (adj[u][i].vert == v){
      return true;
    }
  }
  return false;
}

/* Makes the predicate graph. There is an edge from i \in [0, u_label.size()) to
   j \in [0, v_label.size()) if u_label[i].prop == v_label[j].prop and
   forall (u, v) \in u_label[i].vars x v_label[j], (u, v) is in the universe graph */
void make_pgraph(const vector<vector<edge>>& adj_u, const vector<vector<edge>>& adj_v,
		 const vector<prop>& u_label, const vector<prop>& v_label, vector<vector<int>>& pgraph){
  pgraph.clear(); pgraph.resize(u_label.size());

  #pragma omp parallel for schedule(guided)
  for (size_t i = 0; i < u_label.size(); ++i){
    for (size_t j = 0; j < v_label.size(); ++j){
      if (u_label[i].pred == v_label[j].pred){
       	bool mem(true);
	for (size_t k = 0; mem && k < u_label[i].vars.size(); ++k){
	  mem = has_edge(adj_u, u_label[i].vars[k], v_label[j].vars[k]);
	}
	if (mem) { pgraph[i].push_back(j); }
      }
    }
  }
}


/* Ford Fulkerson Max Flow Algorithm (Specialized to Bipartite Graphs) */
size_t max_matching(const vector<vector<edge>>& adj, vector<int>& match1, vector<int>& match2, vector<int>& vis, int iter){
  size_t ans = 1;
  for (size_t i = 1; i < adj.size(); ++i){
    ++iter;
    ans += dfs(adj, match1, match2, vis, i, iter);
  }
  return ans;
}

bool dfs(const vector<vector<edge>>& adj, vector<int>& match1, vector<int>& match2, vector<int>& vis, int x, int iter){
  if (vis[x] == iter) return false;
  vis[x] = iter;
  for (size_t i = 0; i < adj[x].size(); ++i){
    int y = adj[x][i].vert;
    if (match2[y] < 0 || dfs(adj, match1, match2, vis, match2[y], iter)){
      match2[y] = x;
      match1[x] = y;
      return true;
    }
  }
  return false;
}

/* Finds all vertices in pgraph.U that are violated by the candidate matching */
void find_conflicts(const vector<vector<int>>& pgraph, const vector<prop>& u_label, const vector<prop>& v_label,
	            const vector<int>& matching, vector<int>& confs){
  confs.clear();
  for (size_t i = 0, j, k; i < pgraph.size(); ++i){
    for (j = 0; j < pgraph[i].size(); ++j){
      for (k = 0; k < u_label[i].vars.size() && matching[u_label[i].vars[k]] == v_label[pgraph[i][j]].vars[k]; ++k);
      if (k == u_label[i].vars.size()) break;
    }
    if (j == pgraph[i].size()){
      confs.push_back(i);
    }
  }
}

/* removes any edges in the universe graph that are inconsistent with the decision pu |-> pv */
vector<vpair> remove_edges(const vector<int>& pu, const vector<int>& pv,
			 vector<vector<edge>>& adj_u, vector<vector<edge>>& adj_v){
  vector<vpair> removed;
  edge k, l;
  for (size_t i = 0; i < pu.size(); ++i){
    size_t u(pu[i]), v(pv[i]);
    for (size_t j = 0; j < adj_u[u].size(); ++j){
      k = adj_u[u][j];
      if (k.vert != v){
	adj_v[k.vert][k.pos] = adj_v[k.vert][adj_v[k.vert].size()-1];
	l = adj_v[k.vert][k.pos];
	adj_u[l.vert][l.pos].pos = k.pos;
	adj_v[k.vert].pop_back();
	removed.push_back(vpair(u, k.vert));
      }
    }
    adj_u[u].clear();
    adj_u[u].push_back(edge(v,0));
    for (size_t j = 0; j < adj_v[v].size(); ++j){
      k = adj_v[v][j];
      if (k.vert != u){
	adj_u[k.vert][k.pos] = adj_u[k.vert][adj_u[k.vert].size()-1];
	l = adj_u[k.vert][k.pos];
	adj_v[l.vert][l.pos].pos = k.pos;
	adj_u[k.vert].pop_back();
	removed.push_back(vpair(k.vert, v));
      }
    }
    adj_v[v].clear();
    adj_v[v].push_back(edge(u, 0));
  }
  unit_prop(adj_u, adj_v, removed);
  return removed;
}

/* Adds each (u,v) in edges into the universe graph
   Note: (u,v) should not already be in the universe graph
   This operation is not idempotent */
void add_edges(const vector<vpair>& edges, vector<vector<edge>>& adj_u, vector<vector<edge>>& adj_v){
  for (size_t i = 0; i < edges.size(); ++i){
    vpair e = edges[i];
    edge u(e.v, adj_v[e.v].size()), v(e.u, adj_u[e.u].size());
    adj_u[e.u].push_back(u);
    adj_v[e.v].push_back(v);
  }
}

/* Performs backtracking on decisions only choosing decisions that are consistent
   with all previous decisions 
   This is done by maintaining consistence with the universe graph that is forced
   to be consistent with all previously made decisions */
void backtrack(stack<decision>& decisions, const vector<vector<int>>& pgraph, const vector<prop>& u_label, const vector<prop>& v_label,
	       vector<vector<edge>>& adj_u, vector<vector<edge>>& adj_v){
  while(!decisions.empty()){
    decision d = decisions.top(); decisions.pop();
    add_edges(d.edges, adj_u, adj_v);
    for (size_t k; ++d.pos < pgraph[d.u].size();){
      for (k = 0; k < u_label[d.u].vars.size(); ++k){
        if (!has_edge(adj_u, u_label[d.u].vars[k], v_label[pgraph[d.u][d.pos]].vars[k])) break;
      }
      if (k == u_label[d.u].vars.size()){
        decisions.push(decision(d.u, d.pos, remove_edges(u_label[d.u].vars, v_label[pgraph[d.u][d.pos]].vars, adj_u, adj_v)));
        return;
      }
    }
  }
}

/* Selects a vertex in pgraph.U to decide on next (only trying vertices that
   can be consistent with decisions already made) */
bool choose(stack<decision>& decisions, const vector<int>& confs,
	    const vector<vector<int>>& pgraph, const vector<prop>& u_label, const vector<prop>& v_label,
	    vector<vector<edge>>& adj_u, vector<vector<edge>>& adj_v){
  for (size_t i = 0, pu; i < confs.size(); ++i){
    pu = confs[i];
    for (size_t j = 0, pv, k; j < pgraph[pu].size(); ++j){
      pv = pgraph[pu][j];
      for (k = 0; k < u_label[pu].vars.size(); ++k){
	if (!has_edge(adj_u, u_label[pu].vars[k], v_label[pv].vars[k])) break;
      }
      if (k == u_label[pu].vars.size()){
	decisions.push(decision(pu, j, remove_edges(u_label[pu].vars, v_label[pv].vars, adj_u, adj_v)));
	return true;
      }
    }
  }
  return false;
}
