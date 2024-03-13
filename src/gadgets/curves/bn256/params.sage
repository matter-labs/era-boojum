
# Finding lambda parameter such that lambda**2 + lambda + 1 = 0 in Fp...
# Defining a galois field...
p = 21888242871839275222246405745257275088696311157297823662689037894645226208583
Fp = GF(p)

q = 21888242871839275222246405745257275088548364400416034343698204186575808495617
Fq = GF(q)

# Defining a polynomial ring over Fp 
# and finding the roots of the polynomial X^2+X+1:
R.<x> = PolynomialRing(Fq)
f = x^2 + x + 1
f_roots = f.roots()
lambdas = [root[0] for root in f_roots]
print('Roots of x^2 + x + 1 are', lambdas)

# Picking one lambda out of roots
lambd = lambdas[1]
print('Picked lambda =', lambd)

# Verifying that lambd is the root of the polynomial...
assert lambd**2 + lambd + 1 == 0, 'lambd is incorrect since it is not a root of X^2+X+1'

# Finding beta parameter
# Beta should satisfy beta*3 = 1 in Fp, thus
# it is one of the roots of the polynomial Y^3 - 1
Q.<y> = PolynomialRing(Fp)
g = y^3 - 1
g_roots = g.roots()
betas = [root[0] for root in g_roots]
print('Roots of y^3 - 1 are', betas)

# Picking one beta out of roots
beta = betas[1]
print('Picked beta =', beta)

# Verifying that beta is the root of the polynomial Y^3-1...
assert beta**3 == 1, 'beta is incorrect since beta^3 != 1'

# Then, we need to verify that (beta, lambda) pair is valid.
# For that, define the BN254 curve. 
# Parameters can be found in section 5.4.9 of the paper
# https://zips.z.cash/protocol/protocol.pdf
a = Fp(0)
b = Fp(3)
E = EllipticCurve(Fp, (a, b))
G = E(1, 2) # Base point
E.set_order(q)

# Taking some random point on the curve
Q = 11 * G
# Applying endomorphism to the point
R = lambd * Q
# If lambda1 and beta are valid, then R should be equal (beta*x, y)
x_1 = beta * Q[0]
y_1 = Q[1] 

assert x_1 == R[0], 'beta is invalid since (beta*x, y) != lambda*(x, y)'
assert y_1 == R[1], 'beta is invalid since (beta*x, y) != lambda*(x, y)'
