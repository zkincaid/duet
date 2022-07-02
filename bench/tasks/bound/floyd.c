
#include "assert.h"
#include "tick.h"

void floydWarshall (int V)
{
  int i, j, k;

	for (i = 0; i < V; i++)
      for (j = 0; j < V; j++) {
        tick(1);
      }

	for (k = 0; k < V; k++)
	{
		for (i = 0; i < V; i++)
		{
			for (j = 0; j < V; j++)
			{
              tick(1);
			}
		}
	}

}

int main()
{
    int V;
	int V = __VERIFIER_nondet_int();
	__VERIFIER_assume(V > 0);
    init_tick(0);


	floydWarshall(V);
    /* free(graph); */
    int bnd = V * V * V + V* V;
	__VERIFIER_assert(__cost <= bnd);
	return 0;
}
