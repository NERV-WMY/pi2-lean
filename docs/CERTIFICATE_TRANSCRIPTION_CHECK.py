"""Standalone exact transcription check for the printed rational appendix.

This file supplies its own literal inputs and never reads or executes an old
certificate, solver, or output.  No period, target fit, or rank is an input.
The printed 90 coefficients constitute a witness, not unknowns to be solved.
"""
import sympy as S
from sympy.polys.fields import field
import time

started = time.perf_counter()
X, Z, LAM = S.symbols('x s lambda')
rho = S.Rational(729, 15625)
I = S.eye(3)
J = S.Matrix([[0, 1, 0], [0, 0, 1], [0, 0, 0]])
w = S.Matrix([[S.Rational(5,72), S.Rational(23,36), S.Rational(3,2)]])
E = S.zeros(3)
E[2,:] = w
R0 = S.kronecker_product(J,I) - S.kronecker_product(I,J-E)
R1 = -S.kronecker_product(E,I)
Rl = -S.kronecker_product(I,E)
Rt = R0 + R1 + Rl
B6 = (J + LAM*E/(1-LAM)).row_join(-LAM*E/(1-LAM)).col_join(
    (-E/(1-LAM)).row_join(J + LAM*E/(1-LAM)))
C = S.Matrix([
    [S.Rational(49456,125),S.Rational(153648,125),S.Rational(113472,125),
     S.Rational(72,5),-S.Rational(3312,25),S.Rational(113472,125)],
    [-S.Rational(1576,25),-S.Rational(4608,25),-S.Rational(3312,25),
     0,S.Rational(72,5),-S.Rational(3312,25)],
    [S.Rational(46,5),S.Rational(108,5),S.Rational(72,5),0,0,S.Rational(72,5)],
    [-1,0,0,0,0,0],[0,-1,0,0,0,0],[0,0,-1,0,0,0]])

def cancel_matrix(A):
    return A.applyfunc(S.cancel)

def nf(v):
    return (S.kronecker_product(w,v[:,:3])/(Z-1)
            + S.kronecker_product(v[:,3:],w)/(Z-LAM))

N = lambda q: J + q*E/(1-q)
gauge = S.Matrix([[1,0,0],[0,LAM,0],
                 [5*LAM/(72*(1-LAM)),LAM**2/(2*(1-LAM)),2*LAM**2]])
pq,cq = (1-S.Rational(3,2)*LAM)/(LAM*(1-LAM)),5/(144*LAM*(1-LAM))
ao = S.Matrix([[0,1,0],[2*cq,-pq,2],[0,cq,-2*pq]])
jc = S.Matrix([[-5*LAM/36,-LAM/2,1-LAM],[-LAM/2,LAM-1,0],[1-LAM,0,0]])
tq = S.Matrix([[-5*LAM/72,0,2*LAM**2*(1-LAM)],
               [-LAM/2,LAM*(LAM-1),0],[1-LAM,0,0]])
assert cancel_matrix(gauge.diff(LAM)+gauge*ao-N(LAM)*gauge/LAM) == S.zeros(3)
assert cancel_matrix(jc*gauge-tq) == S.zeros(3)
Ms = S.kronecker_product(N(Z),I)/Z - S.kronecker_product(I,N(LAM/Z))/Z
Ml = S.kronecker_product(I,N(LAM/Z))
assert cancel_matrix(Ms-R0/Z-R1/(Z-1)-Rl/(Z-LAM)) == S.zeros(9)
for j in range(6):
    v = S.eye(6)[j,:]
    p = S.zeros(1,9) if j < 3 else -Z*S.kronecker_product(v[:,3:],w)/(Z-LAM)
    assert cancel_matrix(LAM*nf(v).diff(LAM)+nf(v)*Ml-nf(v*B6)
                         -p.diff(Z)-p*Ms) == S.zeros(1,9)
e00 = S.eye(9)[0,:]
anchor = e00*R0.inv()
assert cancel_matrix(e00/Z-nf(C[0,:])-anchor*Ms) == S.zeros(1,9)
for j in range(5):
    assert cancel_matrix(C[j,:]*B6-C[j+1,:]) == S.zeros(1,6)
assert C.det() == S.Rational(373248,125)

# The rational beta source, with beta_N = T_U dU + U*T_s ds.
x, s, lam = X, Z, rho*X**3
m = 27*x*(80-99*x+27*x**2)/1000
a = 27*x*(9*x-16)/1000
M = 25-9*x
D = x**4*M*(99*x-50)**2
f = s**2-2*m*s+lam
a2 = 81*x**2-198*x+80
a3 = 243*x**3-1053*x**2+1266*x-400
a6 = (59049*x**6-511758*x**5+1724085*x**4-2860596*x**3
      +2441988*x**2-1011200*x+160000)
k,jj,vv,cc = map(S.Rational, ['1953125/209952','244140625/944784',
                             '3906250/6561','30517578125/8503056'])
LP = S.Matrix([[0,0,-k*(9*x-25)*a2*a3],
               [0,0,jj*(9*x-25)*a2],
               [k*(9*x-25)*a2*a3,-jj*(9*x-25)*a2,0]])
RP = S.Matrix([[0,0,k*a6],[0,vv*x*(99*x-50),-jj*a3],
               [k*a6,-jj*a3,cc]])

# These temporary matrices are the displayed beta numerators.
# Their common scalar denominator is D*f.
Ts = cancel_matrix(2*LP*(s-m)+2*a*M*RP)
TU = cancel_matrix((-2*(1-x)*LP*S.diff(f,x)-2*RP*(
     -2*a*(1-x)*M*S.diff(m,x)+(s-m)*(
     (a-2*(1-x)*S.diff(a,x))*M+9*(1-x)*a))))

# The beta numerators are polynomials in s over Q(x).
# Clear the known connection denominator, divide by f^2 exactly, and only
# then create rational rows.  This preserves all nine source entries.
F, x = field('x',S.QQ)
K, s = field('s',F.to_domain())
z = K.zero
lam = rho*x**3
lift = K.ground_new
parse = lambda q: K.from_expr(q)
constant = lambda A: [[parse(A[i,j]) for j in range(A.cols)] for i in range(A.rows)]
ts_fraction,tu_fraction = constant(Ts),constant(TU)
assert all(q.denom.degree() == 0 for row in ts_fraction+tu_fraction for q in row)
ts = [[q.numer.mul_ground(F.one/q.denom.LC) for q in row] for row in ts_fraction]
tu = [[q.numer.mul_ground(F.one/q.denom.LC) for q in row] for row in tu_fraction]
P = K.ring
sp = s.numer
pp = P.one
zz = P.zero
u = 1-x
mfield = F.from_expr(m)
dlogD = F.from_expr(S.diff(D,X)/D)
fpoly = sp**2-2*mfield*sp+lam

def dx_polynomial(p):
    return P.from_dict({e:c.diff(x) for e,c in p.items()})

fx,fs = dx_polynomial(fpoly),fpoly.diff(sp)
angular_den = sp**2*(1-sp)*(sp-lam)
asbar = [[zz,sp*(1-sp),zz],
         [S.Rational(5,72)*pp,-pp+S.Rational(3,2)*sp,2*sp*(1-sp)],
         [zz,S.Rational(5,144)*pp,-2*pp+3*sp]]
cbbar = [[zz,lam*(sp-lam),zz],
         [S.Rational(5,72)*sp**2,-sp**2+S.Rational(3,2)*lam*sp,2*lam*(sp-lam)],
         [zz,S.Rational(5,144)*sp**2,-2*sp**2+3*lam*sp]]
scale = lift(x**5*(9*x-25)*(99*x-50)**3)
scale_over_D = -x*(99*x-50)
alpha = [[z]*3 for _ in range(3)]
for i in range(3):
    for j in range(3):
        scalar_part = (-ts[i][j]*fpoly
            +2*u*(dx_polynomial(ts[i][j])*fpoly-ts[i][j]*fx
                  -dlogD*ts[i][j]*fpoly)
            +tu[i][j].diff(sp)*fpoly-tu[i][j]*fs)
        numerator = (angular_den*scalar_part
            -sp*(sp-lam)*sum((asbar[i][k]*tu[k][j] for k in range(3)),zz)*fpoly
            +(1-sp)*sum((tu[i][k]*cbbar[j][k] for k in range(3)),zz)*fpoly
            -(6*u/x)*sp*(1-sp)*sum((ts[i][k]*cbbar[j][k] for k in range(3)),zz)*fpoly)
        quotient,remainder = numerator.div(fpoly**2)
        assert remainder == zz
        alpha[i][j] = K.new(quotient.mul_ground(scale_over_D),angular_den)
print('All nine source entries pass exact zero-remainder f^2 division.', flush=True)

def metric_gauge(q):
    return [[-5*q/72,z,2*q*q*(1-q)],
            [-q/2,q*(q-1),z],[1-q,z,z]]

b = lift(lam)/s
left,right = metric_gauge(s),metric_gauge(b)
Q = [[sum((left[i][a]*alpha[a][c]*right[j][c]
           for a in range(3) for c in range(3)),z)
      for j in range(3)] for i in range(3)]
print('Source transcribed from the complete beta formulas.', flush=True)

r0,r1,rl = map(constant,[R0,R1,Rl])
ms = [[r0[i][j]/s+r1[i][j]/(s-1)+rl[i][j]/(s-lift(lam))
       for j in range(9)] for i in range(9)]

def row_times(v,A):
    return [sum((v[i]*A[i][j] for i in range(len(v))),z)
            for j in range(len(A[0]))]

def covariant(v):
    return [v[j].diff(s)+q for j,q in enumerate(row_times(v,ms))]

def evaluate(q,a):
    def ev(p):
        return sum((c*(a**e[0] if e[0] else F.one) for e,c in p.items()),F.zero)
    return lift(ev(q.numer)/ev(q.denom))

def pole_order(q,a):
    p,linear,n = q.denom,(s-lift(a)).numer,0
    while q:
        quotient,remainder = p.div(linear)
        if remainder:
            break
        p,n = quotient,n+1
    return n

q = [Q[i][j] for i in range(3) for j in range(3)]
r, eta = q[:],[z]*9

def subtract(p):
    global r,eta
    exact = covariant(p)
    r = [r[j]-exact[j] for j in range(9)]
    eta = [eta[j]+p[j] for j in range(9)]

for a,residue in [(F.one,R1),(lam,Rl),(F.zero,R0)]:
    while True:
        order = max(pole_order(t,a) for t in r)
        if order < 2:
            break
        lead = [evaluate(t*(s-lift(a))**order,a) for t in r]
        inv = constant((residue-(order-1)*S.eye(9)).inv())
        subtract([t/(s-lift(a))**(order-1) for t in row_times(lead,inv)])
while True:
    polynomials = [t.numer.div(t.denom)[0] for t in r]
    degree = max(p.degree(0) if p else -1 for p in polynomials)
    if degree < 0:
        break
    lead = [lift(p.get((degree,),F.zero)) for p in polynomials]
    inv = constant(((degree+1)*S.eye(9)+Rt).inv())
    subtract([t*s**(degree+1) for t in row_times(lead,inv)])
subtract(row_times([evaluate(t*s,F.zero) for t in r],constant(R0.inv())))
u = [evaluate(t*(s-1),F.one) for t in r]
v = [evaluate(t*(s-lift(lam)),lam) for t in r]
normal = [u[j]/(s-1)+v[j]/(s-lift(lam)) for j in range(9)]
assert all(not (r[j]-normal[j]) for j in range(9))
exact = covariant(eta)
assert all(not (q[j]-normal[j]-exact[j]) for j in range(9))
g = [u[6+j]/parse(w[0,2])/scale for j in range(3)]
g += [v[3*j+2]/parse(w[0,2])/scale for j in range(3)]
assert all(not (u[3*i+j]-parse(w[0,i])*g[j]*scale)
           and not (v[3*i+j]-g[3+i]*parse(w[0,j])*scale)
           for i in range(3) for j in range(3))
print('Angular source identity established with its rational primitive.', flush=True)

# Literal 15 by 6 coefficient table: basis order is specified below.
COEFFICIENTS = '''
105800/459459 867560/459459 103229200/459459 -169280/51051 -1388096/51051 -2268352/51051
0 0 -472485400/459459 0 0 0
0 0 338560000/196911 0 0 0
0 0 -4232000000/4135131 0 0 0
-78890805485931260/886402053948411 -1227125311357021190/886402053948411 -70427029255928891500/6204814377638877 -607873567055897705440/74327471429736107583 -298973396640778498112/8258607936637345287 -145365088004028281168/635277533587488099
-231954922267076000/229807939912551 -331597299956488000/76602646637517 -108998157631733600/5892511279809 -39913346954892419000/917623104070816143 28252939480465998800/101958122674535127 -14427468858797595200/5997536627913831
-44128649359258592/31024071888194385 623049674458568524/31024071888194385 6660655461825680912/31024071888194385 57598947351747925330/10618210204248015369 370356988491186478316/8258607936637345287 422172179336846381488/5899005669026675205
7410960991604618219/7834361587927875000 -2244024947258679397/230422399644937500 -8368444588355333518/75330399883921875 -1674067760127596905471/469239087308940073125 -7571431721389433993041/260688381838300040625 -60217890176084166521579/1303441909191500203125
-1014783336398633/79134965534625000 99347762374288343/39567482767312500 226386615454772638/9891870691828125 1399948922915894608/4739788760696364375 6901571092120745041/2633215978164646875 59461141531221275693/13166079890823234375
-1051211136/19184234069 -440067361152/479605851725 -18358156683264/2398029258625 1031881871061389312/1196916353711203125 258130738760714016/40711440602421875 20750847913747165488/1994860589518671875
1029377673/34880425580 430927242561/872010639500 4494215281788/1090013299375 -250759381828805733/558002962103125000 -14957478836244716238/4533774067087890625 -24572653010256580956/4533774067087890625
-16224867/3170947780 -6792198219/79273694500 -70837018452/99092118125 300193629643629927/3297290230609375000 1380547922050429344/2060806394130859375 2261266906791518928/2060806394130859375
0 0 0 -223303109482368/7493841433203125 -8431993935111168/37469207166015625 -13467359214383616/37469207166015625
0 0 0 218665144746549/13625166242187500 2064215740879206/17031457802734375 3296911156760547/17031457802734375
0 0 0 -3446560950471/1238651476562500 -32535799768674/1548314345703125 -51965324712513/1548314345703125
'''
coefficients = [[F.from_expr(S.Rational(t)) for t in line.split()]
                for line in COEFFICIENTS.strip().splitlines()]
assert len(coefficients) == 15 and all(len(row) == 6 for row in coefficients)
basis = [x**(-p) for p in range(1,5)]
basis += [(99*x-50)**(-p) for p in range(1,3)] + [x**p for p in range(9)]
xi = [sum((coefficients[k][j]*basis[k] for k in range(15)),F.zero)
      for j in range(6)]
mx = [[3*F.from_expr(B6[i,j].subs(LAM,lam.as_expr()))/x
       -(F.one/(2*(1-x)) if i == j else F.zero)
       for j in range(6)] for i in range(6)]
d = list(map(S.Rational,['1/375','14/375','532/3375']))
h = [[-F.from_expr(C[k,j]+6*C[k+1,j])/(2*(1-x))
      for j in range(6)] for k in range(3)]
for j in range(6):
    residual = (-g[j].as_expr()/(2*(1-X))
                -sum(d[k]*h[k][j].as_expr() for k in range(3))
                -xi[j].diff(x).as_expr()
                -sum((xi[i]*mx[i][j]).as_expr() for i in range(6)))
    assert S.cancel(residual) == 0
assert [-81*t for t in d] == list(map(S.Rational,['-27/125','-378/125','-1596/125']))
print('All finite printed identities hold over the rational function fields.')
print('Elapsed seconds:', round(time.perf_counter()-started,3))
