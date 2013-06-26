module unit.

of (abs T R) (arrow T U) :- pi x\ (of x T => of (R x) U).
of (app M N) T :- of M (arrow U T), of N U.

path (app M N) (left P) :- path M P.
path (app M N) (right P) :- path N P.
path (abs T R) (bnd S) :- pi x\ pi p\ path x p => path (R x) (S p).
