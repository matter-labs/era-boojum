# Defining vectors (a1,b1) and (a2,b2)
a1 = 788919430192407951782190
b1 = -602889891024722752429129
a2 = 602889891024722752429129
b2 = 1391809321217130704211319

# Defining the group order
n = 1461501637330902918203687013445034429194588307251
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
k = 965486288327218559097909069724275579360008398257
k1, k2 = decompose(k)

# Printing results
print(f'k1 = (hex: {hex(Fq(k1))}, decimal: {Fq(k1)}) | bits number = {k1.nbits()}')
print(f'-k1 = ({hex(Fq(-k1))}, decimal: {Fq(-k1)}) | bits number = {(-k1).nbits()}')
print(f'k2 = ({hex(Fq(k2))}, decimal: {Fq(k2)}) | bits number = {k2.nbits()}')
print(f'-k2 = ({hex(Fq(-k2))}, decimal: {Fq(-k2)}) | bits number = {(-k2).nbits()}')