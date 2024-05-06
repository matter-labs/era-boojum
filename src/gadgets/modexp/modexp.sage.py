

# This file was *autogenerated* from the file modexp.sage
from sage.all_cmdline import *   # import sage library

_sage_const_16 = Integer(16); _sage_const_8 = Integer(8); _sage_const_2 = Integer(2); _sage_const_32 = Integer(32); _sage_const_0 = Integer(0); _sage_const_1 = Integer(1); _sage_const_7 = Integer(7); _sage_const_33 = Integer(33); _sage_const_0xbbe4922f210aa886cc084106178a3e2e9048d0223acb60f55b0a0ad1458dda6a = Integer(0xbbe4922f210aa886cc084106178a3e2e9048d0223acb60f55b0a0ad1458dda6a); _sage_const_0x590298d43998ff77a6b85f70835748739f57bed0e0ef16aec7ba2628da373cc7 = Integer(0x590298d43998ff77a6b85f70835748739f57bed0e0ef16aec7ba2628da373cc7); _sage_const_0x4715ccf06b9b5602917948ec337e272e7515c3002b56f3a6324546e4c0c2410 = Integer(0x4715ccf06b9b5602917948ec337e272e7515c3002b56f3a6324546e4c0c2410)# Modexp helper file.
# Note that we use w = 64 so that n = 4. 

UINT512_LIMBS_NUMBER = _sage_const_16 
UINT256_LIMBS_NUMBER = _sage_const_8 
BASE = _sage_const_2 **(_sage_const_32 ) # UINT32 base

def gen_random_uint512() -> list[Integer]:
    """
    Generated a random uint512 number represented by 64 uint8 limbs.
    """

    return [randint(_sage_const_0 , BASE-_sage_const_1 ) for _ in range(UINT512_LIMBS_NUMBER)]

def gen_random_uint256() -> list[Integer]:
    """
    Generated a random uint256 number represented by 32 uint8 limbs.
    """

    return [randint(_sage_const_0 , BASE-_sage_const_1 ) for _ in range(UINT256_LIMBS_NUMBER)]

def convert_from_limbs(limbs: list[Integer]) -> Integer:
    """
    Converts a list of uint8 limbs to an Integer.
    """
    
    return sum([limbs[i] * BASE**i for i in range(len(limbs))])

def long_division(n: list[Integer], m: list[Integer]) -> (Integer, Integer):
    """
    Performs long division on two numbers represented by their limbs.
    """

    k = UINT512_LIMBS_NUMBER
    l = UINT256_LIMBS_NUMBER
    m = convert_from_limbs(m)

    # q <- 0, r <- first l-1 digits of n
    q = _sage_const_0 
    #r = convert_from_limbs([n[k-l+1+i] if i < l-1 else Integer(0) for i in range(k)])
    r = n[_sage_const_8 :]
    r[_sage_const_0 ] = _sage_const_0 
    r[_sage_const_0 :_sage_const_7 ] = r[_sage_const_1 :_sage_const_8 ]
    r[_sage_const_7 ] = _sage_const_0 

    r = convert_from_limbs(r)

    # Initialize current d - intermediate dividend
    for i in range(k-l+_sage_const_1 ):
        # d_i <- b*r_{i-1} + \alpha_{i+l-1}
        d = r * BASE + n[k-l-i]

        # beta_i <- next digit of quotient
        # Using binary search to find beta_i
        left, right = _sage_const_0 , BASE
        for _ in range(_sage_const_33 ):
            beta = (right + left) // _sage_const_2  + (right + left) % _sage_const_2 
            r = d - m * beta     
            if r < _sage_const_0 :
                right = beta - _sage_const_1 
            if r >= m:
                left = beta + _sage_const_1 
        
        assert _sage_const_0  <= r < m, 'r was not in the range [0, m)'

        # q_i <- b*q_{i-1} + beta_i
        q = q * BASE + beta

    return (q, r)
    
def modexp(base: Integer, exponent: Integer, modulus: Integer) -> Integer:
    """
    Computes base^exponent mod modulus.
    """

    a = _sage_const_1 
    binary_exponent = exponent.binary()
    print(binary_exponent)
    for i in range(len(binary_exponent)):
        print(f'a={a}, ei={binary_exponent[i]}')
        a = a*a % modulus
        if Integer(binary_exponent[i]) % _sage_const_2  == _sage_const_1 :
            a = a*base % modulus
    
    return a

#m[0] = 0
#m[1] = 0

#n[0] = 0
#n[-4:] = [0,0,0,0]
#n = [0, 0, 0, 7, 5, 2, 0, 6, 2, 1]
#m = [7, 3, 0]

for i in range(_sage_const_1 ):
    n = gen_random_uint512()
    m = gen_random_uint256()
    q, r = long_division(n, m)
    
    n = convert_from_limbs(n)
    m = convert_from_limbs(m)
    
    assert q == n // m
    assert r == n % m
    
    b = _sage_const_0xbbe4922f210aa886cc084106178a3e2e9048d0223acb60f55b0a0ad1458dda6a 
    e = _sage_const_0x590298d43998ff77a6b85f70835748739f57bed0e0ef16aec7ba2628da373cc7 
    m = _sage_const_0x4715ccf06b9b5602917948ec337e272e7515c3002b56f3a6324546e4c0c2410 

    assert b.powermod(e, m) == modexp(b, e, m)

