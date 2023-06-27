    
/////////////////////////////////////////////
//                                         //
// LaurentPolynomials.m                    //
//                                         //
// Geordie Williamson                      //
// 2023-05
//                                         //
/////////////////////////////////////////////

// A simple implementation of Laurent polynomials in Magma.

// The idea is simple:
// We do all operations in magma's "QuotientField",
// all that changes is the printing.

declare type RngMLau[RngMLauElt];

declare attributes RngMLau:
	FunctionField; // Underling function field.
	
declare attributes RngMLauElt:
	Parent,
	Element; // an element of a quotient.


////////////////////////////////////////////////////////////////////////
//                                                                    //
//                        Creation functions                          //
//                                                                    //
////////////////////////////////////////////////////////////////////////


intrinsic LaurentPolynomialRing(R::Rng,n::RngIntElt)-> RngMLau
    {Rank n Laurent polynomial Ring over R.}
    M := New(RngMLau);
    M`FunctionField := FunctionField(R,n);
    return M;
end intrinsic;

intrinsic '.'(M::RngMLau,w::.) -> RngMLauElt
    {The standard basis element given by w.}
    case Type(w): 
	when RngIntElt:
	    x := New(RngMLauElt);
	    x`Parent := M;
	    x`Element := (M`FunctionField).w;
	    return x;
	else : 
	    require true: "w must be an integer indexing a generator.";
    end case;
end intrinsic;

// We try as much as possible to piggy back on top of top of
// magma's function field stuff.

intrinsic AssignNames(~R::RngMLau,names::[MonStgElt])
    {}
    AssignNames(~R`FunctionField, names);
end intrinsic;

intrinsic Name(R::RngMLau, i::RngIntElt) -> .
{}
  return R.i;
end intrinsic;


////////////////////////////////////////////////////////////////////////
//                                                                    //
//                           Helper functions                         //
//                                                                    // 
////////////////////////////////////////////////////////////////////////

intrinsic CheckElement(x::RngMLauElt) -> BoolElt
{Check that the numerator is a monomial.}
   return IsMonomial(Denominator(x`Element));
end intrinsic;

	  

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                           Coercions                                //
//                                                                    // 
////////////////////////////////////////////////////////////////////////

intrinsic IsCoercible(M::RngMLau,S::.) -> BoolElt, RngMLauElt
    {Return whether S is coercible into M and the result if so}
    // First the easy case!:
    if Type(S) eq RngMLauElt and M eq Parent(S) then
	return true, S;
    end if;
    if IsCoercible(M`FunctionField,S) then
	x := New(RngMLauElt);
	x`Parent := M;
	x`Element := M`FunctionField!S;
	return true, x;
    end if;
    return false, "Illegal coercion.";
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                           Printing                                 //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Print(M::RngMLau)
    {}
    printf "Laurent polynomial ring of rank %o over %o.",
	Rank(M`FunctionField), BaseRing(M`FunctionField); 
end intrinsic;

function mon_func(R,seq)

    function pow(b,exp)
	if exp eq 1 then
	    return b;
	else
	    return b cat "^" cat IntegerToString(exp);
	end if;
    end function;
    
    if seq eq [0 : i in [1..Rank(R)]] then
	return "1";
    else
	return &cat[ pow( Sprint(Name(R`FunctionField,i)), seq[i]) : i in [1..Rank(R)] | seq[i] ne 0];
    end if;
end function;

intrinsic Print(x::RngMLauElt, level::MonStgElt)
    {}
    require CheckElement(x): "You did an illegal divison somewhere.";
    f := Numerator(x`Element);
    coeffs := Coefficients(f);
    mons := Monomials(f);
    g := Denominator(x`Element);
    dcoeffs := Coefficients(g);
    dmons := Monomials(g);
    require #dcoeffs eq 1: "Denominator not a monomial.";
    require dcoeffs[1] eq 1: "Illegal coefficient in demonator.";
    dseq := Exponents(dmons[1]);
			     
    if #coeffs eq 0 then // we are dealing with zero.
	printf "%o", x`Element;
    else
	for j in [1..#coeffs-1] do
	    seq := Exponents(mons[j]);
	    if coeffs[j] eq 1 then
		printf "%o + ", mon_func(x`Parent, [ seq[i] - dseq[i] : i in [1..Rank(x`Parent)]]);
	    else
		printf "%o*%o + ", coeffs[j], mon_func(x`Parent, [ seq[i] - dseq[i] : i in [1..Rank(x`Parent)]]);
	    end if;
	end for;
    	seq := Exponents(mons[#coeffs]);
	if coeffs[#coeffs] eq 1 then
	    printf "%o", mon_func(x`Parent, [ seq[i] - dseq[i] : i in [1..Rank(x`Parent)]]);
	else
	    printf "%o*%o", coeffs[#coeffs], mon_func(x`Parent, [ seq[i] - dseq[i] : i in [1..Rank(x`Parent)]]);
	end if;
    end if;
    end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                      Attribute Access Functions                    //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Rank(M::RngMLau) -> RngIntElt
	  {}
	  return Rank(M`FunctionField);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                  Membership and equality testing                   //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Parent(x::RngMLauElt) -> RngMLau
    {}
    return x`Parent;
end intrinsic;

intrinsic IsZero (x::RngMLauElt) -> BoolElt
    {}
    return x`Element eq 0;
end intrinsic;

intrinsic 'eq' (M::RngMLau,N::RngMLau) -> BoolElt
    {}
    return (M`FunctionField eq N`FunctionField);
end intrinsic;

intrinsic 'eq' (x::RngMLauElt,y::RngMLauElt) -> BoolElt
    {}
    return IsZero(x-y);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//               Simple arithmetic operations, etc.                   //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic '-' (x::RngMLauElt) -> RngMLauElt
    {}
    y := New(RngMLauElt);
    y`Parent := x`Parent;
    y`Element := -x`Element;
    return y;
end intrinsic;

intrinsic '-' (x::RngElt,y::RngMLauElt) -> RngMLauElt
    {}
    return x + (-y);
end intrinsic;

intrinsic '-' (x::RngMLauElt,y::RngMLauElt) -> RngMLauElt
    {}
    require x`Parent eq y`Parent:
       "Arguments must have the same parent.";
    return x + (-y);
end intrinsic;

intrinsic '+' (x::RngMLauElt,y::RngMLauElt) -> RngMLauElt
    {}
    require x`Parent eq y`Parent:
	"Arguments must have the same parent.";
    z := New(RngMLauElt);
    z`Parent := x`Parent;
    z`Element := x`Element + y`Element;
    return z;
end intrinsic;

intrinsic '+' (x::RngMLauElt,y::RngElt) -> RngMLauElt
    {}
    require IsCoercible(x`Parent,y):
	"Cannot coerce y into Laurent Polynomial Ring.";
    _, z := IsCoercible(x`Parent,y);
    return x + z;
end intrinsic;

intrinsic '+' (y::RngElt,x::RngMLauElt) -> RngMLauElt
    {}
    require IsCoercible(x`Parent,y):
	"Cannot coerce y into Laurent Polynomial Ring.";
    _, z := IsCoercible(x`Parent,y);
    return x + z;
    end intrinsic;

intrinsic '*' (x::RngMLauElt,y::RngMLauElt) -> RngMLauElt
    {}
    z := New(RngMLauElt);
    z`Parent := x`Parent;
    z`Element := x`Element*y`Element;
    require CheckElement(z): "Illegal division";
    return z;
end intrinsic;

intrinsic '*' (y::RngElt,x::RngMLauElt) -> RngMLauElt
    {}
    require IsCoercible(x`Parent,y):
	"Cannot coerce y into Laurent Polynomial Ring.";
    _, z := IsCoercible(x`Parent,y);
    return x * z;
    end intrinsic;

intrinsic '^' (x::RngMLauElt,y::RngElt) -> RngMLauElt
    {}
    z := New(RngMLauElt);
    z`Parent := x`Parent;
    z`Element := x`Element^y;
    return z;
end intrinsic;

intrinsic 'div' (x::RngMLauElt,y::RngMLauElt) -> RngMLauElt
    {}
    z := New(RngMLauElt);
    z`Parent := x`Parent;
    z`Element := x`Element / y`Element;
    require CheckElement(z): "Division isn't Laurent polynomial";
    return z;
end intrinsic;
