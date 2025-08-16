The first idea for this came up in January 2025.

At first, I was considering to calculate multiphi by using algorithm similar to depth-first search of a large graph, with nodes representing positive integers and edges representing multiplying/dividing by prime numbers.

This quite got stuck early when I tried to extend this idea into $\varphi^3, \varphi^4$ and further beyond, and it was inconvenient not to be able to calculated multiphi of n in ascending order of n anyway.

I completed the algorithm which works sometime between February to June 2025, and added some optimisations like parallelization and wheel-sieve-like-optimisations of spaces later.

However, the resulting algorithm required to record chains of partial factors directly for all primes, resulting in $O(k \sqrt{N}\log N)$ complexity (though I was quite satisfied with this one.)

Later, when I was discussing this algorithm with GPT-5, it suggested me to only store $f'_0, f'_1$ at $f_2$, using it like a forest of linked list which forms a direct acyclic graph.

Probably GPT-5 didn't proved that any $f_2^{(i)}$ fits inside the harmonic map internally - it somehow just assumed it and showed me the idea.

I followed the argument, noticed the non-trivial flaw in the reasoning but noticed it can be fixed, and I completed the algorithm you see now on 2025.08.15.
