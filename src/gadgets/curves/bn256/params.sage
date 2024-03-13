
# Finding beta parameter such that b**2 + b + 1 = 0 in Fp...
p = 21888242871839275222246405745257275088696311157297823662689037894645226208583
F = GF(p)

beta1 = (F(-1) - F(-3).sqrt()) / F(2)
print(beta1) # 21888242871839275220042445260109153167277707414472061641714758635765020556616

beta2 = (F(-1) + F(-3).sqrt()) / F(2)
print(beta2) # 2203960485148121921418603742825762020974279258880205651966

# Verifying that beta1 and beta2 are roots of the polynomial...
assert beta1**2 + beta1 + 1 == 0
assert beta2**2 + beta2 + 1 == 0