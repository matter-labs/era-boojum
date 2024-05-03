# Modexp helper file.
# Note that we use w = 64 so that n = 4. 

UINT512_LIMBS_NUMBER = 16
UINT256_LIMBS_NUMBER = 8
BASE = 2^(32) # UINT32 base
print(BASE)

def gen_random_uint512() -> list[Integer]:
    """
    Generated a random uint512 number represented by 64 uint8 limbs.
    """

    return [randint(0, BASE-1) for _ in range(UINT512_LIMBS_NUMBER)]

def gen_random_uint256() -> list[Integer]:
    """
    Generated a random uint256 number represented by 32 uint8 limbs.
    """

    return [randint(0, BASE-1) for _ in range(UINT256_LIMBS_NUMBER)]

def convert_from_limbs(limbs: list[Integer]) -> Integer:
    """
    Converts a list of uint8 limbs to an Integer.
    """
    
    return sum([limbs[i] * BASE^i for i in range(len(limbs))])

def long_division(n: list[Integer], m: list[Integer]) -> (Integer, Integer):
    """
    Performs long division on two numbers represented by their limbs.
    """

    k = UINT512_LIMBS_NUMBER
    l = UINT256_LIMBS_NUMBER
    m = convert_from_limbs(m)

    # q <- 0, r <- first l-1 digits of n
    q = 0
    #r = convert_from_limbs([n[k-l+1+i] if i < l-1 else Integer(0) for i in range(k)])
    r = n[8:]
    r[0] = 0
    r[0:7] = r[1:8]
    r[7] = 0

    print(f'Got: {r}')
    r = convert_from_limbs(r)

    # Initialize current d - intermediate dividend

    for i in range(k-l+1):
        # d_i <- b*r_{i-1} + \alpha_{i+l-1}
        d = r * BASE + n[k-l-i]

        # beta_i <- next digit of quotient
        # Using binary search to find beta_i
        left, right = 0, BASE
        for _ in range(0, 256):
            beta = (right + left) // 2 + (right + left) % 2
            r = d - m * beta
            #if 0 <= r < m:
            #    continue
            
            if r < 0:
                right = beta - 1
            if r > m:
                left = beta + 1

        assert 0 <= r < m, 'r was not in the range [0, m)'

        # q_i <- b*q_{i-1} + beta_i
        q = q * BASE + beta

    return (q, r)
    

n = gen_random_uint512()
m = gen_random_uint256()
#m[0] = 0
#m[1] = 0

#n[0] = 0
#n[-4:] = [0,0,0,0]
#n = [0, 0, 0, 7, 5, 2, 0, 6, 2, 1]
#m = [7, 3, 0]


print(f'Trying to divide {n} by {m}...')
q, r = long_division(n, m)
print('\n--- Got: ---\n')
print(f'q={q}')
print(f'r={r}')

print('\n--- Should be: ---\n')
n = convert_from_limbs(n)
m = convert_from_limbs(m)
print(f'q={n // m}')
print(f'r={n % m}')

#assert find_modulus(base, modulus) == base % modulus

