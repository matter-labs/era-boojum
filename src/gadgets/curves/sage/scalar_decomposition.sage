# Defining vectors (a1,b1) and (a2,b2)
a1 = Integer('0x89d3256894d213e3')
b1 = Integer('-0x6f4d8248eeb859fc8211bbeb7d4f1128')
a2 = Integer('0x6f4d8248eeb859fd0be4e1541221250b')
b2 = Integer('0x89d3256894d213e3')

# Defining the group order
n = Integer(21888242871839275222246405745257275088548364400416034343698204186575808495617)
Fq = GF(n)

def decompose(k: Integer):
    c1 = round(b2 * k / n)
    print(f'c1 = {c1}')
    c2 = round(-b1 * k / n)
    print(f'c2 = {c2}')

    k1 = k - c1*a1 - c2*a2
    k2 = -c1*b1 - c2*b2
    return k1, k2

# Decomposing the scalar
k = Integer('0x161a87df4ee5620c75acf8cf7b2f1547183bf7368e2956fcc42ae0e439200c20')
k1, k2 = decompose(k)

# Printing results
print(f'k1 = (hex: {hex(Fq(k1))}, decimal: {Fq(k1)}) | bits number = {k1.nbits()}')
print(f'-k1 = ({hex(Fq(-k1))}, decimal: {Fq(-k1)}) | bits number = {(-k1).nbits()}')
print(f'k2 = ({hex(Fq(k2))}, decimal: {Fq(k2)}) | bits number = {k2.nbits()}')
print(f'-k2 = ({hex(Fq(-k2))}, decimal: {Fq(-k2)}) | bits number = {(-k2).nbits()}')