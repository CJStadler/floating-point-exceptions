# Definitions of equivalent traces

1. Strictest: An exception of type E is reported on line L in P' iff an
   exception of type E is reported on line L in P.
2. 1-to-1: the traces are the same if you ignore line numbers.
3. Allow collapsing: For every exception of type E on line L in P the next
   exception after L in P' is of type E.
4. Variable based? Debug info says which variables correspond to which
   registers.
