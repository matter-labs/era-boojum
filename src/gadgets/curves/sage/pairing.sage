# Curve parameter u and the value of [log2(6x+2)] - 1:
u = 4965661367192848881
six_u_plus_2 = 6*u+2

six_u_plus_2_naf = [
    0, 0, 0, 1, 0, 1, 0, -1,
    0, 0, 1, -1, 0, 0, 1, 0,
    0, 1, 1, 0, -1, 0, 0, 1, 
    0, -1, 0, 0, 0, 0, 1, 1,
    1, 0, 0, -1, 0, 0, 1, 0, 
    0, 0, 0, 0, -1, 0, 0, 1,
    1, 0, 0, -1, 0, 0, 0, 1, 
    1, 0, -1, 0, 0, 1, 0, 1, 
    1]
print('\nCurve in WNAF format: {}', six_u_plus_2_naf)

# Verifying that the decomposition is indeed correct:
six_u_plus_2_wnaf = sum([k_i * 2**i for i, k_i in enumerate(six_u_plus_2_naf)])
assert six_u_plus_2_wnaf == six_u_plus_2