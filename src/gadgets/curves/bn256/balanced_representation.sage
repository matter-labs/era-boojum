def find_short_vectors(q: int, lambd: int) -> tuple[GF, GF, GF, GF]:
    """
    Finds the shirt vectors for the elliptic curve. Vectors are in the form
    v1 = (a1, b1) and v2 = (a2, b2)

    Params:
        q: GF - base field
        lambd: GF - lambda parameter (root of X^2-X-1 in Fq)

    Returns:
        tuple[GF, GF, GF, GF] - short vectors
    """

    trace = _extended_euclidean_alg_trace(q, lambd)
    
    # Finding the greatest l s.t. r_l > sqrt(n)
    for i, entry in enumerate(trace):
        _, _, r = entry
        if r >= sqrt(q):
            l = i
    
    # Defining tuples of (s_l, t_l, r_l)
    sl, tl, rl = trace[l]
    sl1, tl1, rl1 = trace[l+1]
    sl2, tl2, rl2 = trace[l+2]

    a1, b1 = rl1, -tl1
    if rl**2 + tl**2 <= rl2**2 + tl2**2:
        a2, b2 = rl, -tl
    else:
        a2, b2 = rl2, -tl2

    return (a1, b1, a2, b2)


def _extended_euclidean_alg_trace(a: GF, b: GF) -> list[tuple[GF, GF, GF]]:
    """
    Extended Euclidean algorithm which outputs the trace of computations in
    a form of array (s_i, t_i, r_i) where s_i*a + t_i*b = r_i based
    on Algorithm 3.74 of:
    http://tomlr.free.fr/Math%E9matiques/Math%20Complete/Cryptography/Guide%20to%20Elliptic%20Curve%20Cryptography%20-%20D.%20Hankerson,%20A.%20Menezes,%20S.%20Vanstone.pdf
    
    Inputs:
        a: GF - first number
        b: GF - second number
    
    Returns:
        list[tuple[GF, GF, GF]] - trace of computations
    """

    # Basic parameters for the algorithm
    u, v = a, b
    x1, y1 = 1, 0
    x2, y2 = 0, 1
    r = a

    # Resultant trace of computations in a form of 
    # array (s_i, t_i, r_i)
    trace = []

    while u != 0:
        print(f's_i*n + t_i*lambd = r: {x1}*{a} + {y1}*{b} = {r}')
        trace.append((x1, y1, r))
        q = v // u
        r = v - q*u
        x = x2 - q*x1
        y = y2 - q*y1
        v = u
        u = r
        x2 = x1
        x1 = x
        y2 = y1
        y1 = y

    d = v
    x = x2
    y = y2 
    return trace

# Firstly, checking an Example 3.75 from 
# http://tomlr.free.fr/Math%E9matiques/Math%20Complete/Cryptography/Guide%20to%20Elliptic%20Curve%20Cryptography%20-%20D.%20Hankerson,%20A.%20Menezes,%20S.%20Vanstone.pdf
q = 1461501637330902918203687013445034429194588307251
lambd = 903860042511079968555273866340564498116022318806
a1, b1, a2, b2 = find_short_vectors(q, lambd)

assert a1 == 788919430192407951782190, 'a1 is incorrect'
assert b1 == -602889891024722752429129, 'b1 is incorrect'
assert a2 == 602889891024722752429129, 'a2 is incorrect'
assert b2 == 1391809321217130704211319, 'b2 is incorrect'

# Now, calculating the value for BN254 curve

# Defining base field Fq
q = 21888242871839275222246405745257275088548364400416034343698204186575808495617
# As if was shown, lambda parameter is the following:
lambd = 4407920970296243842393367215006156084916469457145843978461

# Displaying the short vectors
a1, b1, a2, b2 = find_short_vectors(q, lambd)
print('a1 =', a1) # 9931322734385697763
print('b1 =', b1) # -147946756881789319000765030803803410728
print('a2 =', a2) # 147946756881789319010696353538189108491
print('b2 =', b2) # 9931322734385697763
