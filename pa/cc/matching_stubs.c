#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <cstdio>
#include <vector>
#include <string>
#include <cstdint>
#include <map>
using namespace std;

vector<vector<int> > make_graph(const vector<vector<uint64_t> >& sigs1, const vector<vector<uint64_t> >& sigs2);
bool embedding(const vector<vector<uint64_t> >& sigs1, const vector<vector<uint64_t> >& sigs2);
size_t max_matching(const vector<vector<int> >& adj, vector<int>& match1, vector<int>& match2, vector<int>& vis, int iter);
bool dfs(const vector<vector<int> >& adj, vector<int>& match1, vector<int>& match2, vector<int>& vis, int x, int iter);

extern "C" {
  CAMLprim value embedsOCAML(value str1, value str2){ /* str = int * (string * int list) list */
    CAMLparam2(str1, str2);
    CAMLlocal3(head, propList, predList);
    
    vector<vector<uint64_t> > sig1, sig2;   /* Signature of str1 and str2 respectively */
    sig1.resize(Int_val(Field(str1, 0))+1); /* Resize to respective universe size */
    sig2.resize(Int_val(Field(str2, 0))+1);
    map<string, int> preds;                 /* Mapping from predicate symbols to [0 .. n] */
    string pred;
    int arg, predi;

    /* Process structure 1 */
    propList = Field(str1, 1);
    while (propList != Val_emptylist){
      head = Field(propList, 0);        /* hd propList Type: (string * int list) */
      propList = Field(propList, 1);    /* tl propList */
      predList = Field(head, 1);

      pred = String_val(Field(head, 0));
      if (preds.count(pred) == 0){
	preds[pred] = preds.size();

	if (((preds.size() - 1)& 63) == 0){ /* Should we resize signatures? */
	  size_t size = preds.size() / 64 + 1;
	  for (size_t i = 0; i < sig1.size(); ++i){
	    sig1[i].resize(size, 0);
	  }
        }
      }
      predi = preds[pred];
      while (predList != Val_emptylist){
	head = Field(predList, 0);
	arg = Int_val(head);
	sig1[arg][predi >> 6] |= (1 << (predi & 63)); /* >> 6 = / 64 and (& 63) = % 64 */
	predList = Field(predList, 1);
      }
    }

    /* Resize Signature 2 to match signature 1 */
    size_t size = (preds.size() + 63) / 64;
    for (size_t i = 0; i < sig2.size(); ++i){
      sig2[i].resize(size, 0);
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
      while (predList != Val_emptylist){
	head = Field(predList, 0);
	arg = Int_val(head);
	sig2[arg][predi >> 6] |= (1 << (predi & 63)); /* >> 6 = / 64 and (& 63) = % 64 */
	predList = Field(predList, 1);
      }
    }
    CAMLreturn(Val_bool(embedding(sig1, sig2)));
  }
}

bool embedding(const vector<vector<uint64_t> >& sigs1, const vector<vector<uint64_t> >& sigs2){
  vector<vector<int> > adj = make_graph(sigs1, sigs2);
  vector<int> match1, match2, vis;
  int iter(0);

  match1.resize(adj.size(), -1);   /* We could do a greedy match to speed things up */
  match2.resize(sigs2.size(), -1);
  vis.resize(adj.size(), 0);
  return adj.size() == max_matching(adj, match1, match2, vis, iter);
}

bool subset(const vector<uint64_t>& sig1, const vector<uint64_t>& sig2){
  bool subset(true);
  for (size_t i = 0; i < sig1.size() && (subset = ((sig1[i] & sig2[i]) == sig1[i])); ++i); /* assert(sig1.size() == sig2.size()) */
  return subset;
}

vector<vector<int> > make_graph(const vector<vector<uint64_t> >& sigs1, const vector<vector<uint64_t> >& sigs2){
  vector<vector<int> > adj;
  adj.resize(sigs1.size());

  #pragma omp parallel for schedule(guided)
  for (size_t i = 1; i < sigs1.size(); ++i){
    for (size_t j = 1; j < sigs2.size(); ++j){
      if (subset(sigs1[i], sigs2[j])){
	adj[i].push_back(j);
      }
    }
  }
  return adj;
}

/* Ford Fulkerson Max Flow Algorithm (Specialized to Bipartite Graphs) */
size_t max_matching(const vector<vector<int> >& adj, vector<int>& match1, vector<int>& match2, vector<int>& vis, int iter){
  size_t ans = 1;
  for (size_t i = 1; i < adj.size(); ++i){
    ++iter;
    ans += dfs(adj, match1, match2, vis, i, iter);
  }
  return ans;
}

bool dfs(const vector<vector<int> >& adj, vector<int>& match1, vector<int>& match2, vector<int>& vis, int x, int iter){
  if (vis[x] == iter) return false;
  vis[x] = iter;
  for (size_t i = 0; i < adj[x].size(); ++i){
    int y = adj[x][i];
    if (match2[y] < 0 || dfs(adj, match1, match2, vis, match2[y], iter)){
      match2[y] = x;
      match1[x] = y;
      return true;
    }
  }
  return false;
}
