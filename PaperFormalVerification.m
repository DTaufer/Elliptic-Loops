// ---------
// Functions
// ---------

function Sum(_P1, _P2, _AB)
// Input:	P1 = [x1,y1,z1], P2 = [x2,y2,z2], AB = [A,B]
// Output:	[x,y,z] = P1 +_(0:1:0) P2
	local _I, _x1, _x2, _y1, _y2, _z1, _z2, _A, _B, _X, _Y, _Z;
	_x1 := _P1[1]; _y1 := _P1[2]; _z1 := _P1[3];
	_x2 := _P2[1]; _y2 := _P2[2]; _z2 := _P2[3];
	_A := _AB[1]; _B := _AB[2];

	_X := ( _y1*_y2*(_x1*_y2 + _x2*_y1) - _A*_x1*_x2*(_y1*_z2 + _y2*_z1) - _A*(_x1*_y2 + _x2*_y1)*(_x1*_z2 + _x2*_z1) - 3*_B*(_x1*_y2 + _x2*_y1)*_z1*_z2 - 3*_B*(_x1*_z2 + _x2*_z1)*(_y1*_z2 + _y2*_z1) + _A^2 *(_y1*_z2 + _y2*_z1)*_z1*_z2 );
	_Y := ( _y1^2*_y2^2 + 3*_A*_x1^2*_x2^2 + 9*_B*_x1*_x2*(_x1*_z2 + _x2*_z1) - _A^2*_x1*_z2*(_x1*_z2 + 2*_x2*_z1) - _A^2*_x2*_z1*(2*_x1*_z2 + _x2*_z1) - 3*_A*_B*_z1*_z2*(_x1*_z2 + _x2*_z1) - (_A^3 + 9*_B^2)*_z1^2*_z2^2 );
	_Z := ( 3*_x1*_x2*(_x1*_y2 + _x2*_y1) + _y1*_y2*(_y1*_z2 + _y2*_z1) + _A*(_x1*_y2 + _x2*_y1)*_z1*_z2 + _A*(_x1*_z2 + _x2*_z1)*(_y1*_z2 + _y2*_z1) + 3*_B*(_y1*_z2 + _y2*_z1)*_z1*_z2 );
	return [_X,_Y,_Z];
end function;

function ScalarMult(_l, _P, _AB)
// Input: An integer l, a point P, a pair AB = [A,B]
// Output: l*P
	local _tot, _sign;
	_sign := Sign(_l);
	_tot := [0, 1, 0];
	for i in Reverse(Intseq(_l*_sign, 2)) do
    		_tot := Sum(_tot, _tot, _AB);
    		if i eq 1 then
        		_tot := Sum(_tot, _P, _AB);
    		end if;
	end for;
	if _sign eq -1 then
    		_tot := [_tot[1], -_tot[2], _tot[3]]; 
	end if;
	return _tot;
end function;

function Pinverse( _P )
// Input: A point P
// Output: The inverse of P
	return [_P[1],-_P[2],_P[3]];
end function;

function EV(_F,_Ps)
// Input:	A polynomial F and a sequence of points Ps = [P1,...,Pn]
// Output:	[ F(P1), ..., F(Pn) ]
	return [ Evaluate(_F,_p) : _p in _Ps ];
end function;


// --------------------
// Formal verifications
// --------------------

// Lemma 2.1

R<A,B,X1,Y1,Z1,X2,Y2,Z2> := PolynomialRing(Integers(),8);

Q1 := -A*X1*Z2 - A*X2*Z1 - 3*B*Z1*Z2 + Y1*Y2;
Q2 := A^2*Z1*Z2 - A*X1*X2 - 3*B*X1*Z2 - 3*B*X2*Z1;
Q3 := A*Z1*Z2 + 3*X1*X2;
Q4 := A*X1*Z2 + A*X2*Z1 + 3*B*Z1*Z2 + Y1*Y2;

P1 := [X1,Y1,Z1];
P2 := [X2,Y2,Z2];
P := Sum( P1,P2,[A,B] );

P[1] eq (X1*Y2+X2*Y1)*Q1 + (Z1*Y2+Z2*Y1)*Q2;
P[2] eq Q1*Q4 - Q2*Q3;
P[3] eq (X1*Y2+X2*Y1)*Q3 + (Z1*Y2+Z2*Y1)*Q4;


// Proposition 3.3

R<A,B,X1,Y1,Z1,X2,Y2,Z2> := PolynomialRing(Integers(),8);

P1 := [X1,Y1,Z1];
P2 := [X2,Y2,Z2];

P := Sum( P1,P2,[A,B] );

I := ideal< R | [P[1],P[3]] >;
(X1*Y2+X2*Y1)*P[2] in I;
(Y1*Z2+Y2*Z1)*P[2] in I;


// Lemma 3.4

R<A,B,X1,Y1,Z1,X2,Y2,Z2> := PolynomialRing(Integers(),8);

P := [X1,Y1,Z1];
mP := [X1,-Y1,Z1];
Q := [X2,Y2,Z2];
T := Sum( P,Sum( mP,Q,[A,B] ),[A,B] );

Minors( Matrix(R, [T,Q]), 2) eq [0,0,0];


// Lemma 4.1

R<X1,Y1,Z1,A,B> := PolynomialRing(Integers(),5);

P := [X1,Y1,Z1];
Pm := [X1,-Y1,Z1];
P2 := Sum( P,P,[A,B] );
P3 := Sum( P,P2,[A,B] );


F := X1^3 + A*X1*Z1^2 + B*Z1^3 - Y1^2*Z1;
HF := 3*A*X1^2*Z1 + 3*X1*Y1^2 + 9*B*X1*Z1^2 - A^2*Z1^3;

I := ideal<R|[F] cat Minors(Matrix(R, [Pm,P2]),2) >;
HF*P3[2] in I;


// Lemma 4.2

Rab<A,B,a,b,X1,Y1,Z1,X2,Y2,Z2> := PolynomialRing(Integers(),10);
R<x,y,z> := PolynomialRing(Rab,3);

F := x^3 + A*x*z^2 + B*z^3 - y^2*z;
HF := 3*A*x^2*z + 3*x*y^2 + 9*B*x*z^2 - A^2*z^3;
Tab := a*F+b*HF;

P1 := [X1,Y1,Z1];
P2 := [X2,Y2,Z2];

P12 := Sum( P1,P2,[A,B] );

Evaluate( Tab, P12 ) in ideal<Rab| [Evaluate(Tab,P1), Evaluate(Tab,P2)] >;


// Theorem 5.2

Rab<X1,Y1,Z1,X2,Y2,Z2,X3,Y3,Z3,A,B> := PolynomialRing(Integers(),11);
R<x,y,z> := PolynomialRing(Rab,3);

F := x^3 + A*x*z^2 + B*z^3 - y^2*z;
HF := 3*A*x^2*z + 3*x*y^2 + 9*B*x*z^2 - A^2*z^3;

P1 := [X1,Y1,Z1];
P2 := [X2,Y2,Z2];
P3 := [X3,Y3,Z3];

// i

T := Sum( P2,P3,[A,B] );

Evaluate(F,P1)*Evaluate(HF,T) - Evaluate(F,T)*Evaluate(HF,P1) in ideal<Rab | Minors( Matrix(Rab, [EV(F,[P1,P2,P3]), EV(HF,[P1,P2,P3])]), 2) >;

// ii

S := Sum( Sum( P1,P2,[A,B] ), P3, [A,B]);
T := Sum( P1, Sum( P2,P3,[A,B] ), [A,B]);

ideal< Rab | Minors( Matrix(Rab, [S,T]), 2) > subset ideal< Rab | Minors( Matrix(Rab, [EV(F,[P1,P2,P3]), EV(HF,[P1,P2,P3])]), 2) >;


// Lemma 8.1

Rab<X,Y,p,A,B> := PolynomialRing(Integers(),5);

P := [X,Y,1];
P2 := [p,1,p];
P3 := [0,1,p];

S := Sum(Sum(P,P2,[A,B]),P3,[A,B]);
T := Sum(P,Sum(P2,P3,[A,B]),[A,B]);
I := ideal< Rab | [p^3] cat Minors( Matrix(Rab, [S,T]), 2) >;

2*(4*A^3 + 27*B^2)^2*p^2*Y^3 in I;


// Lemma 8.2	

Rab<X,Y,p,A,B> := PolynomialRing(Integers(),5);

P := [X,Y,1];
Pmod := [X,Y+p,1];
Pinf := [0,1,p];

S := Sum(Sum(P,Pmod,[A,B]),Pinf,[A,B]);
T := Sum(P,Sum(Pmod,Pinf,[A,B]),[A,B]);
I := ideal< Rab | p^2 >;

F1 := A^2-3*A*X^2-9*B*X-3*X*Y^2;
F2 := A^3+6*A^2*X^2+6*A*B*X-3*A*X^4+9*B^2-18*B*X^3-Y^4;
G1 := 10*A^4*X+9*A^3*B+2*A^3*Y^2-30*A^2*B*X^2+6*A^2*X^5+6*A^2*X^2*Y^2+45*A*B^2*X+45*A*B*X^4+9*A*B*X*Y^2+54*B^3+135*B^2*X^3+18*B^2*Y^2-9*B*X^3*Y^2;
G2 := 2*A^4-15*A^2*B*X+30*A^2*X^4+6*A^2*X*Y^2+9*A*B^2+90*A*B*X^3+3*A*B*Y^2-6*A*X^3*Y^2+135*B^2*X^2-27*B*X^5-27*B*X^2*Y^2;

2*p*Y^2*F1*F2*G1 - (S[1]*T[2] - S[2]*T[1]) in I;
2*p*Y^2*F1*F2*G2 - (S[2]*T[3] - S[3]*T[2]) in I;

P3 := Sum(Sum(P,P,[A,B]),P,[A,B]);
P3[1] in ideal< Rab | [X^3+A*X+B-Y^2, F1] >;
P3[3] in ideal< Rab | [X^3+A*X+B-Y^2, F1] >;

P4 := Sum(P3,P,[A,B]);
P4[1] in ideal< Rab | [X^3+A*X+B-Y^2, F2] >;
P4[3] in ideal< Rab | [X^3+A*X+B-Y^2, F2] >;

864*Y^10*(X^3-Y^2) in ideal< Rab | [X^3+A*X+B-Y^2, G1, G2] >;
288*Y^8*(B-2*X^3+2*Y^2) in ideal< Rab | [X^3+A*X+B-Y^2, G1, G2] >;


// Lemma 8.3	

Rab<p,A,B> := PolynomialRing(Integers(),3);

P := [p,1,0];
Q := [0,1,p];

S := Sum(Sum(P,Q,[A,B]),Q,[A,B]);
T := Sum(P,Sum(Q,Q,[A,B]),[A,B]);
I := ideal< Rab | [p^6] cat Minors(Matrix(Rab, [S,T]), 2) >;

972*p^5*B^3*(B-2) in I;
36*p^5*B*(4*A-9*B^2+24*B) in I;
6*p^5*A*(2*A+3*B) in I;


// Lemma 8.4

Rab<X1,Z1,X2,Z2,X3,Z3,A,B> := PolynomialRing(Integers(),8);

P1 := [X1,1,Z1];
P2 := [X2,1,Z2];
P3 := [X3,1,Z3];

S := Sum( Sum( P1,P2,[A,B] ), P3, [A,B]);
T := Sum( P1, Sum( P2,P3,[A,B] ), [A,B]);

d := 5;
R<x1,z1,x2,z2,x3,z3> := PolynomialRing(Rab,6);
deg_d_mon := [ Evaluate(_m,[X1,Z1,X2,Z2,X3,Z3]) : _m in MonomialsOfDegree(R,d) ];
ideal< Rab | Minors( Matrix(Rab, [S,T]), 2) > subset ideal< Rab | deg_d_mon >;


// Lemma 8.6

Rab<X,Y,Z,X1,Z1,X2,Z2,A,B> := PolynomialRing(Integers(),9);
R<x,y,z> := PolynomialRing(Rab,3);

P := [X,Y,Z];
Q := [X1,1,Z1];
R := [X2,1,Z2];

S := Sum( Sum( P,Q,[A,B] ), R, [A,B]);
T := Sum( P, Sum( Q,R,[A,B] ), [A,B]);

d := 2;
R<x1,z1,x2,z2> := PolynomialRing(Rab,4);
deg_d_mon := [ Evaluate(_m,[X1,Z1,X2,Z2]) : _m in MonomialsOfDegree(R,d) ];
ideal< Rab | Minors( Matrix(Rab, [S,T]), 2) > subset ideal< Rab | deg_d_mon >;


// Lemma 8.7

Rab<X,Y,Z,m1,m2,m3,X1,Z1,X2,Z2,A,B> := PolynomialRing(Integers(),12);

m := ideal<Rab|[m1,m2,m3,X1,Z1,X2,Z2]>;
QR := Rab/(m^2);

P := [QR!X,QR!Y,QR!Z];
Q := [QR!(X+m1),QR!(Y+m2),QR!(Z+m3)];
R1 := [QR!X1,1,QR!Z1];
R2 := [QR!X2,1,QR!Z2];

QA := QR!A;
QB := QR!B;

S := Sum( Sum( P,R1,[QA,QB] ), Pinverse( Sum( Q,R2,[QA,QB] ) ), [QA,QB] );
T := Sum( Sum( P,Pinverse(Q),[QA,QB]), Sum( R1,Pinverse(R2),[QA,QB] ), [QA,QB] );

Ms := Minors( Matrix(Rab, [S,T]), 2);
QR!Ms[1] eq 0; 
QR!Ms[2] eq 0;
QR!Ms[3] eq 0;


// Lemma 8.8

Rab<X,Y,Z,m1,m2,m3,m4,m5,m6,A,B> := PolynomialRing(Integers(),11);

m := ideal<Rab|[m1,m2,m3,m4,m5,m6]>;
QR := Rab/(m^2);

P := [QR!X,QR!Y,QR!Z];
Q := [QR!(X+m1),QR!(Y+m2),QR!(Z+m3)];
R := [QR!(X+m4),QR!(Y+m5),QR!(Z+m6)];

QA := QR!A;
QB := QR!B;

S := Sum( Sum( P,Q,[QA,QB] ), Pinverse(R), [QA,QB] );
T := Sum( P, Sum( Q,Pinverse(R),[QA,QB]), [QA,QB] );

Ms := Minors( Matrix(Rab, [S,T]), 2);
QR!Ms[1] eq 0; 
QR!Ms[2] eq 0;
QR!Ms[3] eq 0;


// Proposition 8.10
// REMARK: This computation is memory intensive: a server is advised for performing the following computations.
// It may also take a long time, we provide our timing as a guidline.

Rab<m1,m2,m3,m4,m5,m6,m7,m8,X1,Z1,X2,Z2,A,B> := PolynomialRing(Integers(),14);
M := ideal<Rab|[m1,m2,m3,m4,m5,m6,m7,m8]>;
M2 := M^2;

function PolyReduce( _F )
// input: a polynomial F
// output: F mod M2, i.e. leaving all the terms of degree >1 in the mi's
	seq := [ _m : _m in Terms(_F) | not(_m in M2) ];
	if IsEmpty(seq) then
		return 0;
	else
		return &+seq;
	end if;
end function;

function PointReduce( _P )
// input: a point P = [X,Y,Z]
// output: P mod M2, i.e. leaving to X,Y,Z all the terms of degree >1 in the mi's
	return [ PolyReduce(_X) : _X in _P ];
end function;


P1 := [X1,1,Z1];
P2 := [X1+m1,1,Z1+m2];
P3 := [X1+m3,1,Z1+m4];

Q1 := [X2,1,Z2];
Q2 := [X2+m5,1,Z2+m6];
Q3 := [X2+m7,1,Z2+m8];

// First association
// We perform the differences first (it heuristically speeds the computation up)
P2m3 := Sum( P2, Pinverse(P3), [A,B] ); P2m3 := PointReduce(P2m3);
Q2m3 := Sum( Q2, Pinverse(Q3), [A,B] ); Q2m3 := PointReduce(Q2m3);

S1 := Sum( P1,P2m3,[A,B] ); S1 := PointReduce(S1);
S2 := Sum( Q1,Q2m3,[A,B] ); S2 := PointReduce(S2);
time S := Sum( S1,S2,[A,B] ); S := PointReduce(S); // 131.430

// Second association
T1 := Sum( P1,Q1,[A,B] );
T2 := Sum( P2,Q2,[A,B] ); T2 := PointReduce(T2);
T3 := Sum( P3,Q3,[A,B] ); T3 := PointReduce(T3);

T2m3 := Sum( T2, Pinverse(T3), [A,B] ); T2m3 := PointReduce(T2m3);
time T := Sum( T1, T2m3, [A,B] );  T := PointReduce(T); // 861.720

// Projective equality check
// To speed the computations up, we do not compute parts in m^2

mS := [ &+[_m : _m in Terms(S[_i]) | _m in M] : _i in [1,2,3] ];
iS := [ S[_i] - mS[_i] : _i in [1,2,3] ];
mT := [ &+[_m : _m in Terms(T[_i]) | _m in M] : _i in [1,2,3] ];
iT := [ T[_i] - mT[_i] : _i in [1,2,3] ];

for i,j in [1,2,3] do
	if i lt j then
		time iS[i]*iT[j]-iS[j]*iT[i] eq 0; // 138.110
		// Now the heavy part
		time iS[i]*mT[j]+mS[i]*iT[j] - (iS[j]*mT[i]+mS[j]*iT[i]) eq 0; // 9326.320
	end if;
end for;
