This example features an implementation of red black trees in SPARK using
access types (pointers).

A few years ago, I wrote an article for NFM 2017
about proof of a minimal implementation of red black trees in SPARK (with only
the Insert and Contains functions) entirely verified in SPARK. At the time,
pointers were not supported in SPARK, so I used an array to represent a chunk of
memory, and indexes in this array to act as pointers in my tree structure
(see https://link.springer.com/chapter/10.1007/978-3-319-57288-8_5).

I wanted to see if, now that pointers are in SPARK, I could manage to entirely
verify the same minimal implementation of red black trees, but using accesses
instead of indexes. You will see that the goal is only partly achieved. Indeed,
the initial implementation was using the usual encoding of red black trees,
which involves a back pointer to the parent of each node in the tree. Due to
the ownership policy enforced in SPARK
(see https://blog.adacore.com/using-pointers-in-spark), all access types should
have a single owner, ruling out cyclic structures like the one I was planning
to use... Instead, I choose to simply remove this back-pointer, and rather
use a recursive version of the algorithm, where balancing is done on the way
back up the call stack. With this change, I could prove my code entirely (with
the 20.0 version of SPARK, to be released soon). Compared to the previous
version, I even improved the model to use a sequence to represent the model of
my trees instead of a set. It allows users to get elements in order.
