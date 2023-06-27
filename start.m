
Attach("LaurentPolynomials.m");

SetEchoInput(true);

print("We create a Laurent series ring.");

R<x,y> := LaurentPolynomialRing(Rationals(), 2);

Print(R);

print("We create some elements and multiply them.");

f := x*y^(-10) + y^7;

f * y^(-2);

print("Note that printing is slightly nicer than in a function field.");

print("Also note that exact division is possible:");

(x^10 - x^(-10)) div (x - x^(-1));

print("If the result is not a Laurent polynomial one gets an error.");

(x^10 - x^(-10)) div (x - 2*x^(-1));
