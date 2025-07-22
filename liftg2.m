R<x>:=PolynomialRing(Rationals());

/*
We don't use this function if p < 64.
*/
ComputeA1 := function(fModp,p,a1modp)
    assert p gt 64; // If p > 64, use magma's built-in function instead 
    a1:=Integers()! a1modp;
    assert 0 le a1 and a1 lt p;
    return (a1 gt p/2) select a1-p else a1;
end function;


/*
Compute bounds for a2, using page 8 on 
https://arxiv.org/pdf/0801.2778
*/
KSBoundA2 := function(a1, p)

    UB := 2*p+(1/4)*a1^2;

    b:= a1/Sqrt(p);
    
    delta := Abs(b - 4*Floor(b/4)-2); 

    LB := Ceiling((a1^2-p*delta^2)/2);

    return LB, UB;
end function;

/*
Generate candidates using the narrower 
interval as in the output of A2Bounds
*/
CandidatesA2KS := function(a1, a2modp,p)

    LB, UB := KSBoundA2(a1, p);
    a2Rep := (Integers()!(a2modp) eq p) select 0 else Integers()!a2modp;
    assert (0 le a2Rep) and (a2Rep lt p);

    lowerCandidate := Ceiling((LB-a2Rep)/p)*p+a2Rep;
    upperCandidate := Floor((UB-a2Rep)/p)*p+a2Rep;

    assert lowerCandidate mod p eq a2Rep;
    assert upperCandidate mod p eq a2Rep;
    assert lowerCandidate-p lt LB;
    assert upperCandidate+p gt UB;

    candidateSize :=(((upperCandidate-lowerCandidate)/p)+1);
    assert Denominator(candidateSize) eq 1;
    candidateSize := Numerator(candidateSize);
    candidates := [lowerCandidate + p*i : i in [0..candidateSize-1]];
    
    return candidates;
end function;


/*
Compute the 2-rank of Jac(C) where C is given by y^2=f(x)
Using https://scispace.com/pdf/implementing-2-descent-for-jacobians-of-hyperelliptic-curves-l5xzr5qgvn.pdf
*/

Jacobian2Rank := function(fModp, factorizationPattern)

    k:=#factorizationPattern;
    if (Degree(fModp) mod 2) eq 1 then 
        return k-1;
    elif &and[(factorDegree mod 2 )eq 0 : factorDegree in factorizationPattern] then 
        // Deg(f) is even and all factors have even degree
        return k-1;
    else //Deg(f) is even and at least one of the factors have odd degree
        return k-2;
    end if;

end function;

/*
    Convert a degree 6 model to degree 5 whenever possible
*/
Convert6To5IfNeeded := function(fModp,p)

    P<x> := Parent(fModp);
    if &or [Degree(tuple[1]) eq 1 : tuple in Factorization(fModp)] then 
        x0 := Roots(fModp)[1][1];
        fModp := Evaluate(fModp, x+x0);
        fCoeffs := Coefficients(fModp);
        return PolynomialRing(GF(p))!Reverse(fCoeffs[2..#fCoeffs]);
    end if;
    return fModp;
end function;

liftResult := recformat<it: Integers(), a1:Integers(), a2: Integers(), jSize: Integers()>;

/*
    If prime is too small, we use magma's built-in function to compute the $L$-polynomial instead
*/
LiftLpolySmallPrime := function(f,p)
    assert p lt 64;

    C:=HyperellipticCurve(f);
    LC:= EulerFactor(C,p);
    a1 := Coefficients(LC)[2];
    a2 := Coefficients(LC)[3];

    result := rec<liftResult | it:=0, a1:=a1, a2:=a2, jSize:=Evaluate(LC,1)>;

    return result;

end function;

/*
    Main logic in the algorithm
*/
RunOneInstance := function(f,p, a1modp, a2modp)

    if p lt 64 then 
        return LiftLpolySmallPrime(f,p);
    end if;

    fModp := PolynomialRing(GF(p))!f;

    if Degree(f) eq 6 then 
        fModp := Convert6To5IfNeeded(fModp,p);
    end if;

    a1:= ComputeA1(fModp,p,a1modp);

    initialCandidates := CandidatesA2KS(a1,a2modp,p);

    factorizationPattern := {*Degree(tuple[1]): tuple in Factorization(fModp)*};

    split14 :=factorizationPattern eq {*1,4*};
    split23 := factorizationPattern eq {*2,3*};
    split24 := factorizationPattern eq {*2,4*};

    tworank:=Jacobian2Rank(fModp, factorizationPattern);

    jacobianSize := AssociativeArray(Integers());

    jacobianTwistSize := AssociativeArray(Integers());

    for candidate in initialCandidates do 
        jacobianSize[candidate] := p^2 + a1*p + candidate + a1 + 1;
    end for;

    if split14 then 
        x0 := ((Roots(fModp))[1])[1];

        P<x>:=PolynomialRing(GF(p));
        fModp := Evaluate(fModp, x+x0);

        quarticfs := [tuple[1]: tuple in Factorization(fModp) | Degree(tuple[1]) eq 4];
        quarticf := quarticfs[1];

        residue := (IsSquare(Coefficients(quarticf)[1])) select 0 else 2;
        refinedCandidates := [candidate: candidate in initialCandidates| jacobianSize[candidate] mod 4 eq residue];
    end if;

    if split23 or split24 then 

        deg2Factor :=[tuple[1]: tuple in Factorization(fModp) | Degree(tuple[1]) eq 2][1];
        deg34Factor :=[tuple[1]: tuple in Factorization(fModp) | (Degree(tuple[1]) eq 3) or (Degree(tuple[1]) eq 4)][1];

        resultant := Resultant(deg2Factor, deg34Factor);
        residue := (IsSquare(resultant)) select 0 else 2;

        refinedCandidates := [candidate: candidate in initialCandidates| jacobianSize[candidate] mod 4 eq residue];
    end if;


    if tworank eq 0 then 
        refinedCandidates := [candidate : candidate in initialCandidates | (jacobianSize[candidate] mod 2) eq 1 ];
    elif tworank ge 2 then
        refinedCandidates := [candidate : candidate in initialCandidates | (jacobianSize[candidate] mod 2^tworank) eq 0 ];
    end if;
    
    maxIterations := 100;
    it := 0;

    loopCandidates := refinedCandidates;

    while it lt maxIterations and #loopCandidates gt 1 do 

        if it mod 2 eq 0 then 
            J := Jacobian(HyperellipticCurve(fModp));
            randomP := Random(J);
            loopCandidates := [candidate: candidate in loopCandidates | jacobianSize[candidate] * randomP eq (J!0)];
        else 
            /*
                If needed, compute the corresponding sizes of Jacobians of 
                the twists of the curve
            */
            if it eq 1 then 
                for candidate in loopCandidates do 
                    jacobianTwistSize[candidate] := p^2 - a1*p + candidate - a1 + 1;
                end for;
            end if;

            J := Jacobian(QuadraticTwist(HyperellipticCurve(fModp)));
            randomP := Random(J);
            loopCandidates := [candidate: candidate in loopCandidates | jacobianTwistSize[candidate] * randomP eq (J!0)];
        end if;

        it +:= 1;
    end while;

    if #loopCandidates eq 0 then 
        //this is not supposed to happen.
        assert false; // Number of final candidates should be 1
    end if;

    if #loopCandidates eq 1 then 

        if #initialCandidates eq 5 and (split14 or split23 or split24 ) and #refinedCandidates gt 1 then 
            print "Edge case: ";
            print factorizationPattern;
            print <fModp, p>;
        end if;

        a2 :=loopCandidates[1];


        // The following code double whether the selected candidate yields a jacobian size that annihilates all points.
        /*
        J := Jacobian(HyperellipticCurve(fModp));
        randomP := Random(J);
        assert jacobianSize[a2] * randomP eq (J!0);
        */
        lpolyInfo := rec<liftResult | it:=it, a1:=a1, a2:=a2, jSize:=jacobianSize[a2]>;
        return lpolyInfo;
    end if;

    assert false; // Number of final candidates should be 1
end function;

Demo := procedure()
    Examples := [
    <393*x^6 + 112*x^5 - 122*x^4 + 490*x^3 - 158*x^2 - 238*x - 444, 983, 958, 716>,
    <393*x^6 + 112*x^5 - 122*x^4 + 490*x^3 - 158*x^2 - 238*x - 444, 241, 239, 20>,
    <-98*x^6 - 152*x^5 - 253*x^4 - 238*x^3 + 448*x^2 - 175*x + 20, 1009, 1008,700>,
    <x^6 + 202*x^5 + 77*x^4 + 152*x^3 + 153*x^2 + 34*x + 283, 313, 311, 627>,
    <43*x^6 - 45*x^5 - 219*x^4 - 162*x^3 + 477*x^2 - 296*x + 346, 281, 0, 0>
    ];

    ExampleDescriptions := [
        "Example 1: 2-rank is 0, and Jacobian arithmetic is needed to eliminate the wrong candidate.",
        "Example 2: 2-rank is 1, and no Jacobian arithmetic is needed.",
        "Example 3: 2-rank is 2, and no Jacobian arithmetic is needed.",
        "Example 4: 2-rank is 0, and Jacobian arithmetic on the twist is needed. Note that in this case a1=-2, a2=2p-1",
        "Example 5: 2-rank is 2, but Jacobian arithmetic is needed as the two candidats for a2 are {-2p, 2p}."
    ];

    for index in [1..#Examples] do 
        print ExampleDescriptions[index];
        p := Examples[index][2];
        result := RunOneInstance(Examples[index][1],Examples[index][2],GF(p)!Examples[index][3],GF(p)!Examples[index][4]); 
        print "f=", Examples[index][1], " p=",Examples[index][2], " a1modp=", Examples[index][3], " a2modp=",Examples[index][4];
        print "Result:";
        print "a1=", result`a1;
        print "a2=", result`a2;
        print "Total iterations", result`it;
        print "";
        print "";
    end for;

end procedure;

Demo();