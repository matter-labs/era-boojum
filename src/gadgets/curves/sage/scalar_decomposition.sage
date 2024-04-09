# Defining vectors (a1,b1) and (a2,b2)
a1 = 0x89d3256894d213e3
b1 = -0x6f4d8248eeb859fc8211bbeb7d4f1128
a2 = 0x6f4d8248eeb859fd0be4e1541221250b
b2 = 0x89d3256894d213e3

# Precomputed b1/n and b2/n times 2**256
g1 = 0x24ccef014a773d2cf7a7bd9d4391eb18d
g2 = 0x2d91d232ec7e0b3d7

# Defining some curve parameters
n = 21888242871839275222246405745257275088548364400416034343698204186575808495617
Fq = GF(n)
lambd = Integer(4407920970296243842393367215006156084916469457145843978461)

# Regular decomposition
def decompose(k: Integer):
    c1 = b2 * k // n
    c2 = -b1 * k // n

    k1 = k - c1*a1 - c2*a2
    k2 = -c1*b1 - c2*b2
    return k1, k2

# Decomposition using precomputed g1 and g2
def decompose_aztec(k: Integer):
    c1 = (g2 * k) >> 256
    print(c1)
    c2 = (g1 * k) >> 256
    print(c2)

    q1 = c1 * b1
    print(q1)
    q2 = -c2 * b2
    print(q2)

    k2 = q2 - q1
    k2_lambda = k2 * lambd % n
    print(k2_lambda)
    k1 = k - k2_lambda

    return k1, k2

# Decomposing the scalar
print('\n--- Regular decomposition: ---')
k = Integer('0x161a87df4ee5620c75acf8cf7b2f1547183bf7368e2956fcc42ae0e439200c20')
k1, k2 = decompose(k)

# Printing results for regular decomposition
print(f'k1 = {Fq(k1)}')
print(f'-k1 = {Fq(-k1)}')
print(f'k2 = {Fq(k2)}')
print(f'-k2 = {Fq(-k2)}')

# Decomposing the scalar using Aztec Protocol's method 
# https://github.com/AztecProtocol/weierstrudel/blob/master/js_snippets/endomorphism.js#L47
print('\n--- Aztec decomposition: ---')
k1, k2 = decompose_aztec(k)

# Printing results for Aztec decomposition
print(f'k1 = {Fq(k1)}')
print(f'-k1 = {Fq(-k1)}')
print(f'k2 = {Fq(k2)}')
print(f'-k2 = {Fq(-k2)}')
