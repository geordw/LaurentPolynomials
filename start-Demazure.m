
Attach("LaurentPolynomials.m");

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
//                     CartanType                                             //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

CartanType := "B2";

C := CartanMatrix(CartanType);
n := Nrows(C);

Wp := CoxeterGroup(CartanType);
W := CoxeterGroup(GrpFPCox, CartanType); 
whom := hom< W -> Wp | [Wp.i : i in [1..n]]>;
whomi := whom^(-1);
elts := [whomi(x) : x in Wp];

RM := HorizontalJoin(C, IdentityMatrix(Integers(),n)); // Matrix of universal realization.

R := LaurentPolynomialRing(Integers(),2*n);

AssignNames(~R, ["a" cat IntegerToString(i) : i in [1..n]] cat ["w" cat IntegerToString(i) : i in [1..n]]);

// Not sure how to do this elegantly:
// (AssignNames makes the variable names print nicely, however when "a1" is typed into magma, it still doesn't know what this means.)
if n eq 1 then
    a1 := R.1; w1 := R.2;
end if;

if n eq 2 then
    a1 := R.1; a2 := R.2; w1 := R.3; w2 := R.4;
end if;

if n eq 3 then
    a1 := R.1; a2 := R.2; a3 := R.3; w1 := R.4; w2 := R.5; w3 := R.6;
end if;

rho := &*[R.i : i in [n+1..2*n]];

if CartanType eq "C2" then

    printf "\n%o\n", "WARNING: magma conventions are opposite to paper for C2";
    printf "%o\n\n", "We recommend using B2 instead.";

end if;

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
//                     Demazure operators                                     //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////
    
// We are not quite sure how to write down automorphisms of LaurentPolynomials,
// so we write them down as automorphisms of the underlying function field instead.

K := R`FunctionField;
s_pre := [ hom<K->K | [K.j*K.i^(-RM[i,j]) : j in [1..2*n]]> : i in [1..n]];

s := function(i,f);
 return R!s_pre[i](f`Element);
end function;

sdot := function(i,f);
		     return s(i,f*rho)*rho^(-1);
end function;

sdem := function(i,f)
    return (f - s(i,f)*(R.i)^(-1)) div (1-(R.i)^(-1));
end function;

dem := function(seq, f)
    g := f;
    for i in Reverse(seq) do
	g := sdem(i,g);
    end for;
    return g;
end function;

wdot := function(seq, f)
    g := f;
    for i in Reverse(seq) do
	g := sdot(i,g);
    end for;
    return g;
end function;

Wdot := function(w,f)
    return wdot(Eltseq(w),f);
end function;

// to ease entry of interesting elements:
e := function(seq)
    return &*[R.i^seq[i] : i in [1..2*n]];
end function;

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
//                     A2 computations                                        //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

if CartanType eq "A2" then

    print("Checking braid relations on some random elements...");    
    for k in [1..10] do
	z := Random(CartesianProduct([[1..10] : i in [1..4]]));
	z := [z[i] : i in [1..4]];
	dem([1,2,1],e(z)) eq dem([2,1,2],e(z));
    end for;

    // We check Weyl character formula for the adjoint representation:

    dem([1,2,1],a1*a2);

    // We now provide dual bases for type A2.

    X := [R!1, w1^(-1),w2^(-1),w1^(-2),w2^(-2),w1^(-1)*w2^(-1)];

    L := [ W!1, W.1, W.2, W.1*W.2, W.2*W.1, W![1,2,1]];

    Y := [(-1)^CoxeterLength(L[i])*Wdot(L[i],R!1)*X[i]^(-1) : i in [1..6]];

    // We check that the matrix is the identity:

    Matrix( [ [ dem([1,2,1],X[i]*Y[j])`Element : i in [1..6] ] : j in [1..6]]) eq IdentityMatrix(K,6);

    // We check the Weyl demonimator formula:

    &+[X[i]*Y[i] : i in [1..6]] eq &+[ (-1)^CoxeterLength(x)*Wdot(x, R!1) : x in elts];

    // We also check dual bases for R_K^s \subset R_K^{s,t}.

    X := [R!1, w2^(-1), w2^(-2)];
    Y := [R!1, -(e([0,-1,0,1])+e([-1,-1,0,1])),e([-1,-2,0,2])];
    
    Matrix( [ [ dem([1,2,1],X[i]*Y[j])`Element : i in [1..3] ] : j in [1..3]]) eq IdentityMatrix(K,3);

    prodcoprod := &+[ X[i]*Y[i] : i in [1..3]];
    Factorisation(Numerator(prodcoprod`Element));

end if;

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
//                     B2 computations                                        //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

// Recall our warning from above:
// Magma conventions for C2 are opposite to
// the conventions of our paper (our \alpha_s in the paper is Magma's R.2, our \alpha_t is Magma's R.1).
// However, there is a simple fix: use B2 instead.
// These computations match the computations in the paper.

if CartanType eq "B2" then

    print("Checking braid relations on some random elements...");
    for k in [1..10] do
	z := Random(CartesianProduct([[1..10] : i in [1..4]]));
	z := [z[i] : i in [1..4]];
	dem([1,2,1,2],e(z)) eq dem([2,1,2,1],e(z));
    end for;

    // We check Weyl character formula for the adjoint representation:

    dem([1,2,1,2],a1^2*a2);

    // We also check it for the rep corresponding to the highest short root:

    dem([1,2,1,2],a1*a2);
    
    // We now provide dual bases for type A2.

    X := [R!1,  w1^(-1),  w2^(-1),   w1^(-3)*w2,    w2^(-2)*w1,   w1^(-2)      ,   w1^(-1)*w2^(-1) ,   w1^(-2)*w2^(-1) ];

    L := [W!1,  W.1,      W.2,       W.1*W.2,       W.2*W.1,     W![1,2,1]    ,   W![2,1,2]      ,   W![1,2,1,2]];

    Y := [(-1)^CoxeterLength(L[i])*Wdot(L[i],R!1)*X[i]^(-1) : i in [1..8]];

    // We check that the matrix is the identity:

    Matrix( [ [ dem([1,2,1,2],X[i]*Y[j])`Element : i in [1..6] ] : j in [1..6]]);
    
    Matrix( [ [ dem([1,2,1,2],X[i]*Y[j])`Element : i in [1..6] ] : j in [1..6]]) eq IdentityMatrix(K,6);

    // We check the Weyl demonimator formula:

    &+[X[i]*Y[i] : i in [1..#elts]] eq &+[ (-1)^CoxeterLength(x)*Wdot(x, R!1) : x in elts];

    // We also check dual bases for R_K^t \subset R_K^{s,t}.
    // (See Figure: "A dual basis for t-invariants in type C2" in paper.)

    X := [R!1, w1^(-1), w1^(-2), w1^(-3)];
    L := [W![],W![1],W![1,2],W![1,2,1]];
    Y_pre := [Wdot(L[i],R!1)*(X[i]^(-1)) : i in [1..4]];
    Y_pre[2] := Y_pre[2] + s(2,Y_pre[2]);
    Y_pre[3] := Y_pre[3] + s(2,Y_pre[3]);
    Y := [(-1)^(i+1)*Y_pre[i] : i in [1..4]];
    
    Matrix( [ [ dem([1,2,1,2],X[i]*Y[j])`Element : j in [1..4] ] : i in [1..4]]);

    // We need to modify our basis slightly to get a genuine dual basis:

    gamma := dem([1,2,1,2],X[1]*Y[3]);
    gammap := dem([1,2,1,2],X[4]*Y[2]);
    gamma eq gammap^(-1);

    X[1] := X[1] - gamma*X[3];
    X[4] := X[4] - gamma^(-1)*X[2];

    Matrix( [ [ dem([1,2,1],X[i]*Y[j])`Element : j in [1..4] ] : i in [1..4]]);

    // With this modification, we get a beautiful factorisation of product / coproduct element:
    
    prodcoprod := &+[ X[i]*Y[i] : i in [1..4]];
    Factorisation(Numerator(prodcoprod`Element));

    
//    Matrix( [ [ dem([1,2,1],X[i]*Y[j])`Element : i in [1..4] ] : j in [1..3]]) eq IdentityMatrix(K,3);

    // We also check dual bases for R_K^t \subset R_K^{s,t}.
    // (See Figure: "A dual basis for s-invariants in type C2" in paper.)

    X_pre := [R!1, s(1,w1^(-1)), w2^(-1), w2^(-2)];
    X := [R!1, w1^(-1)+s(1,w1^(-1)), w2^(-1), w2^(-2)];
    
    L := [W![],W![2],W![2,1],W![2,1,2]];
    Y_pre := [Wdot(L[i],R!1)*(X_pre[i]^(-1)) : i in [1..4]];
    &and[ s(1,f) eq f : f in X];

//    Y := Y_pre;
    Y_pre[2] := Y_pre[2] + s(1,Y_pre[2]);
    Y_pre[3] := Y_pre[3] + s(1,Y_pre[3]);
    Y := [(-1)^(i+1)*Y_pre[i] : i in [1..4]];
    
    Matrix( [ [ dem([1,2,1,2],X[i]*Y[j])`Element : j in [1..4] ] : i in [1..4]]);

    gamma := dem([1,2,1,2],X[1]*Y[3]);

    X[1] := X[1] - gamma*X[3];
    X[4] := X[4] + gamma^(-1)*X[3];

    Matrix( [ [ dem([1,2,1,2],X[i]*Y[j])`Element : j in [1..4] ] : i in [1..4]]);

    // With this modification, we get a beautiful factorisation of product / coproduct element:
    
    prodcoprod := &+[ X[i]*Y[i] : i in [1..4]];
    Factorisation(Numerator(prodcoprod`Element));
    
end if;

