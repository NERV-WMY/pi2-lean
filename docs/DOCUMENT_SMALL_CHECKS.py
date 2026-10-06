"""Exact checks of the manuscript's small displayed rational identities."""
from pathlib import Path
import re
import sympy as S

x, q, z, h, t = S.symbols("x q z h t")
rat = S.Rational
rho = rat(729, 15625)
u = rat(27, 125)
T = S.Matrix([[-5*q/72, 0, 2*q**2*(1-q)],
              [-q/2, q*(q-1), 0], [1-q, 0, 0]])
N = S.Matrix([[0, 1, 0], [0, 0, 1],
              [5*q/(72*(1-q)), 23*q/(36*(1-q)), 3*q/(2*(1-q))]])
a, c = (1-3*q/2)/(q*(1-q)), 5/(144*q*(1-q))
A = S.Matrix([[0, 1, 0], [2*c, -a, 2], [0, c, -2*a]])
assert (T.diff(q)+N.T*T/q+T*A).applyfunc(S.cancel) == S.zeros(3)

m = 27*x*(80-99*x+27*x**2)/1000
ell = 27*x*(9*x-16)/1000
assert S.expand(m**2-rho*x**3-(1-x)*ell**2*(25-9*x)) == 0
assert 2*m.subs(x,rat(50,99)) == 1+rho*rat(50,99)**3

a3 = 243*x**3-1053*x**2+1266*x-400
a6 = (59049*x**6-511758*x**5+1724085*x**4-2860596*x**3
      +2441988*x**2-1011200*x+160000)
k, j = rat(1953125,209952), rat(244140625,944784)
v, cc = rat(3906250,6561), rat(30517578125,8503056)
RP = S.Matrix([[0,0,k*a6],[0,v*x*(99*x-50),-j*a3],
               [k*a6,-j*a3,cc]])
d = x**4*(25-9*x)*(99*x-50)**2
Mstar = T.subs(q,u)*(4*RP.subs(x,1)/d.subs(x,1))*T.subs(q,u).T
assert Mstar == S.Matrix([[-rat(1,750),rat(1,150),rat(98,1125)],
                         [rat(1,150),rat(98,1125),0],[rat(98,1125),0,0]])
g, dg = S.symbols("g dg")
ddg = rat(27,196)*dg+rat(15,1568)*g
Y = S.Matrix([g**2,2*g*dg,2*dg**2+2*g*ddg])
assert S.expand((Y.T*Mstar*Y)[0]-(3*g**2+56*g*dg)**2/4500) == 0

C = S.Matrix([[rat(49456,125),rat(153648,125),rat(113472,125),
               rat(72,5),-rat(3312,25),rat(113472,125)],
              [-rat(1576,25),-rat(4608,25),-rat(3312,25),
               0,rat(72,5),-rat(3312,25)],
              [rat(46,5),rat(108,5),rat(72,5),0,0,rat(72,5)],
              [-1,0,0,0,0,0],[0,-1,0,0,0,0],[0,0,-1,0,0,0]])
v0 = S.Matrix([0,0,0,rat(5,72),0,0])
v1 = S.Matrix([-1,-1,-1,rat(77,24),rat(77,24),rat(77,24)])
assert C*v0 == S.Matrix([1,0,0,0,0,0])
assert C*v1 == S.ones(6,1)
assert rat(5,72)**2*rho == rat(9,40000)
source = Path(__file__).with_name("CERTIFICATE_TRANSCRIPTION_CHECK.py").read_text()
literal = re.search(r"COEFFICIENTS\s*=\s*'''(.*?)'''",source,re.S).group(1)
coef = [[rat(s) for s in row.split()] for row in literal.strip().splitlines()]
assert len(coef) == 15 and all(len(row) == 6 for row in coef)
phi = [x**-1,x**-2,x**-3,x**-4,1/(99*x-50),1/(99*x-50)**2]+[x**i for i in range(9)]
xi = sum((phi[i]*S.Matrix([coef[i]]) for i in range(15)),S.zeros(1,6))
laurent = {i:S.Matrix([[S.expand(S.series(e,x,0,1).removeO()).coeff(x,i)
                        for e in xi]]) for i in range(-4,1)}
assert [(laurent[i]*v0)[0] for i in [-4,-3,-2]] == [0,0,0]
assert (laurent[-1]*v0)[0] == -rat(105800,459459)
assert rat(9,40000)*(laurent[-4]*v1)[0] == rat(105800,459459)
assert (laurent[0]*v0)[0] == rat(8464,21879)
assert rat(9,40000)*(laurent[-3]*v1)[0] == -rat(8464,21879)

sp, d1, d2 = 1+64*z, 1+16*z, 1+256*z
assert S.expand(d1**3-(1-8*z)**2*sp-1728*z**2) == 0
assert S.expand(d2**3-(1-512*z)**2*sp-1728*z) == 0
B1, B2 = z*(-8/d1+32/sp), z*(-128/d2+32/sp)
C1, C2 = -240*z**2/(sp*d1**2), -60*z/(sp*d2**2)
mu = 60/(d1*d2)
assert S.cancel(B1-B2-2*z*mu) == 0
assert S.cancel(C1-C2-z**2*(S.diff(mu,z)+mu**2)-z*(1+B2)*mu) == 0
poly = (sp*z**2*(3600-960*d2-15360*d1)+60*z*sp*d1*d2
        -7680*z**2*sp*d1+1920*z**2*d1*d2)
assert S.expand(-240*z**2*d2**2+60*z*d1**2-poly) == 0
for n in range(13):
    an = S.rf(rat(1,6),n)*S.rf(rat(1,2),n)*S.rf(rat(5,6),n)/S.factorial(n)**3
    moment = 4**(3*n)*S.factorial(3*n)**2/S.factorial(6*n+1)
    assert (6*n+1)*an**2*moment == S.factorial(6*n)/(6**(6*n)*S.factorial(n)**6)
print("All small manuscript identities and endpoint cancellations hold exactly.")
