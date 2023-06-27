# LaurentPolynomials

A simple magma package for dealing with Laurent polynomials.

It simply wraps the magma FunctionField implementation. (I.e. all the actual computation relies on magma internals.)

There are only two differences:
1) Every time one does a div we check that the result is a LaurentPolynomial (i.e. has a denominator of a special form)
2) We print in a way which is more appropriate for Laurent polynomials.

In order to use this package, download the repo and run

> magma start.m

This file should give you a basic understanding of the capabilities of the package.

I am sure there are some bugs. In particular, printing could be prettier. However it should be enough to get started.

My motivation for writing this package was to experiment with Demazure operators in K-theory. You can see some of this functionality running

> magma start-Demazure.m 

(Standard health warnings apply).
