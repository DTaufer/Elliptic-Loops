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

function SF(_P)
// Input: A point P
// Output: The standard form of P
	local b, inv;
    	b,inv := IsInvertible(_P[3]);
   	if b then 
		return [_P[1]*inv, _P[2]*inv, 1];
    	else   
		b,inv := IsInvertible(_P[2]);
		if b then 
			return [_P[1]*inv, 1, _P[3]*inv];
		else
			b,inv := IsInvertible(_P[1]);
			if b then 
				return [1, _P[2]*inv, _P[3]*inv];
			else
				"Not a projective point";
				return [0,0,0];
			end if;
		end if;
   	end if;
end function;

function EV(_F,_Ps)
// Input:	A polynomial F and a sequence of points Ps = [P1,...,Pn]
// Output:	[ F(P1), ..., F(Pn) ]
	return [ Evaluate(_F,_p) : _p in _Ps ];
end function;

function AutoProd( _X, _n )
// Input:	A set _X and a positive integer n
// Output:	X x X x ... x X (n times)
    if _n eq 1 then
   	 return { [_x] : _x in _X };
    else
   	 return { _y cat [_x] : _y in AutoProd( _X, _n - 1 ), _x in _X };
    end if;
end function;

function Proj( _n, _R, _m )
// Input:	A positive integer n, a local ring R and its maximal ideal m
// Output:	P^n(R)
    local Rstar, prev, Paff, Pinf;
    Rstar := { _x : _x in R | not(_x in _m) };
    if  _n eq 0 then
   	 return { [R!1] };
    else
   	 prev := Proj( _n - 1, _R, _m );
   	 Paff := { _y cat [1] : _y in AutoProd( R, _n ) };
   	 Pinf := { _y cat [_g] : _y in prev, _g in m };
   	 return Paff join Pinf;
   end if;
end function;

function EllipticLoop( _Pr, _m, _A, _B )
// Input:	A projective plane Pr defined over a local ring, the maximal ideal m and two valid parameters A,B
// Output:	The elliptic loop L_{A,B} defined in Pr
    return {_P : _P in _Pr | _P[1]^3+_A*_P[1]*_P[3]^2+_B*_P[3]-_P[2]^2*_P[3] in _m};
end function;

function Layer( _Pr, _t, _A, _B )
// Input:	A projective plane Pr defined over a local ring, a non-invertible element t and two valid parameters A,B
// Output:	The layer L_t defined in Pr
    return {_P : _P in _Pr | _P[1]^3+_A*_P[1]*_P[3]^2+_B*_P[3]-_P[2]^2*_P[3] - _t*(_A^2*_P[3]^3 - 3*_A*_P[1]^2*_P[3] - 9*_B*_P[1]*_P[3]^2 - 3*_P[1]*_P[2]^2) eq 0};
end function;

// --------------------
// Computations
// --------------------

p := 7; e := 2;
R := Integers(p^e);					// the base local ring
m := ideal<R|p>;						// the maximal ideal
k := GF(p);							// the residue field
pi := function(_x) return k!_x; end function;	// the projection map

P2 := Proj(2,R,m); 					// &+[ (#R)^(2-i)*(#m)^i : i in [0..2] ] eq #P2;

repeat A := Random(R); B := Random(R); b,E := IsEllipticCurve([pi(A),pi(B)]); until b and IsOdd(#E);

q := #E;
L := EllipticLoop( P2,m,A,B ); 			// q*p^(2*(e-1)) eq #L;
Lays := [ Layer(P2,_g,A,B) : _g in m ]; 		// if (q mod 3) ne 0 then &meet(Lays) eq { [R!_X,1,0] : _X in &*[m : tmp in [1..e-1] ] }; end if;
