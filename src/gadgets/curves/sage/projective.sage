from __future__ import annotations

from copy import copy
from elliptic_curve import InternalEllipticCurve

class ProjectivePoint:
    def __init__(self, curve: InternalEllipticCurve, x: GF, y: GF, z: GF) -> None:
        """
        Initializes the extended short weierstrass point on the given elliptic curve.

        Args:
            - curve - InternalEllipticCurve, curve on which the point lies
            - (x, y, z) - point on E (in finite field form)
        """
        
        self._curve = curve
        self._x = x
        self._y = y
        self._z = z

    @staticmethod
    def infty(curve: InternalEllipticCurve) -> None:
        """
        Return the point at infinity
        """

        return ProjectivePoint(curve, 0, 1, 0)

    def __add__(self, other: ProjectivePoint) -> ProjectivePoint:
        """
        Defines the + operation for the point
        """
        return self._add_sub_mixed(other, False)

    def __sub__(self, other: ProjectivePoint) -> ProjectivePoint:
        """
        Defines the + operation for the point
        """
        return self._add_sub_mixed(other, True)

    def double(self) -> ProjectivePoint:
        """
        Doubles the point, returning another point.
        """
        if self._curve.a == 0:
            return self._invariant_0_exception_free_doubling()
        
        return self._generic_double()

    def normalize(self) -> ProjectivePoint:
        """
        Divides all coordinates by z
        """

        if self._z == 0:
            return self
        
        self._x = self._x / self._z
        self._y = self._y / self._z
        self._z = 1
        return self

    def mul(self, n: Integers) -> ProjectivePoint:
        """
        Multiplies the point by a scalar n

        Args:
            - n - Integer, scalar to multiply by

        Returns:
            New point on the curve
        """
    
        result = ProjectivePoint.infty(self._curve)
        temp = copy(self)
        bits = n.digits(base=2)
        for bit in bits:
            print('Before:', result)
            if bit == 1:
                result = result + temp
            
            temp = temp.double()
            print('After:', result)
        
        return result

    def _add_sub_mixed(self, other: ProjectivePoint, subtraction: bool) -> ProjectivePoint:
        """
        Adds another ProjectivePoint to the given point (basically, overiding the + operation)

        Args:
            - other - ProjectivePoint, point to add
            - subtraction - bool, whether to subtract the points
            
        Returns:
            Added point on the curve
        """

        # If one of the points is at infinity, return the other
        if self._z == 0:
            return other
        if other._z == 0:
            return self

        if self._curve.a != 0:
            return self._generic_add_sub(other, subtraction)
        
        b3 = self._curve.b + self._curve.b + self._curve.b
        b6 = b3 + b3

        x1 = self._x
        y1 = self._y
        z1 = self._z

        x2 = other._x
        y2 = other._y
        if subtraction:
            y2 = -y2
        
        t4 = y2 * z1
        t4 = t4 + y1

        y3 = x2 * z1
        y3 = y3 + x1

        z1_mul_b3 = z1 * b3
        z3 = y1 * y2
        z3 = z3 + z1_mul_b3

        t0 = x1 * x2

        a = x2 + y2
        b = x1 + y1
        t3 = a * b
        t3 = t3 - t0
        t3 = t3 - z3
        t3 = t3 + z1_mul_b3

        y3_mul_b3 = y3 * b3
        x3 = t4 * y3_mul_b3

        y3_mul_2_b3 = z1 * b6
        t1 = z3 - y3_mul_2_b3

        new_x3 = t3 * t1
        new_x3 = new_x3 - x3
        x3 = new_x3

        t0_mul_3 = t0 * three
        y3 = y3_mul_b3 * t0_mul_3

        new_y3 = t1 * z3
        new_y3 = new_y3 + y3
        y3 = new_y3

        t0 = t0_mul_3 * t3

        z3 = z3 * t4
        z3 = z3 + t0

        return ProjectivePoint(self._curve, x3, y3, z3)

    def _generic_add_sub(self, other: ProjectivePoint, subtraction: bool) -> ProjectivePoint:
        """
        Adds another ProjectivePoint to the given point (basically, overiding the + operation) 
        using generic add/sub operation

        Args:
            - other - ProjectivePoint, point to add
            - subtraction - bool, whether to subtract the points
            
        Returns:
            Added point on the curve
        """

        b3 = 3 * self._curve.b
        
        x1 = self._x
        y1 = self._y
        z1 = self._z

        x2 = other._x
        y2 = other._y
        if subtraction:
            y2 = -y2

        t0 = x1 * x2
        t1 = y1 * y2
        t3 = x2 + y2

        t4 = x1 + y1
        t3 = t3 * t4
        t4 = t0 + t1

        t3 = t3 - t4
        t4 = x2 * z1
        t4 = t4 + x1

        t5 = y2 * z1
        t5 = t5 + y1
        z3 = self._curve.a * t4

        x3 = b3 * z1
        z3 = x3 + z3
        x3 = t1 - z3

        z3 = t1 + z3
        y3 = x3 * z3
        t1 = t0 + t0

        t1 = t1 + t0
        t2 = self._curve.a * z1
        t4 = b3 * t4

        t1 = t1 + t2
        t2 = t0 - t2
        t2 = self._curve.a * t2

        t4 = t4 + t2
        t0 = t1 * t4
        y3 = y3 + t0

        t0 = t5 * t4
        x3 = t3 * x3
        x3 = x3 - t0

        t0 = t3 * t1
        z3 = t5 * z3
        z3 = z3 + t0

        return ProjectivePoint(self._curve, x3, y3, z3)        
    
    def _invariant_0_exception_free_doubling(self) -> ProjectivePoint:
        """
        Doubles the point, returning another point.
        """

        b3 = 3 * self._curve.b
        
        x = self._x
        y = self._y
        z = self._z

        t0 = y * y1
        b3_mul_z = z * b3
        t2 = b3_mul_z * Z

        y3 = t0 + t2
        t1 = y * z
        t0_mul_4 = 4 * t1
        t0_mul_8 = t0_mul_4 + t0_mul_4
        
        z3 = 8 * t0 * t1
        y3_mul_3 = 3 * y3
        t4 = t0_mul_4 - y3_mul_3
        
        y3 = t4 * y3
        new_y3 = t0_mul_8 * t2
        new_y3 = new_y3 + y3
        
        y3 = new_y3
        t1 = x * y
        t4_mul_2 = t4 + t4
        
        x3 = t4_mul_2 * t1

        return ProjectivePoint(self._curve, x3, y3, z3)

    def _generic_double(self) -> ProjectivePoint:
        if self._z == 0:
            return self

        b3 = self._curve.b * 3
        x = self._x
        y = self._y
        z = self._z

        t0 = x * x
        t1 = y * y
        t2 = z * z

        t3 = x * y
        t3 = t3 + t3
        z3 = x * z

        z3 = z3 + z3
        x3 = a * z3
        y3 = b3 * t2

        y3 = x3 + y3
        x3 = t1 - y3
        y3 = t1 + y3

        y3 = x3 * y3
        x3 = t3 * x3
        z3 = b3 * z3

        t2 = a * t2
        t3 = t0 - t2
        t3 = a * t3

        t3 = t3 + z3
        z3 = t0 + t0
        t0 = z3 + t0

        t0 = t0 + t2
        t0 = t0 * t3
        y3 = y3 + t0

        t2 = y * z
        t2 = t2 + t2
        t0 = t2 * t3 

        x3 = x3 - t0
        z3 = t2 * t1
        z3 = z3 + z3

        z3 = z3 + z3

        return ProjectivePoint(self._curve, x3, y3, z3)

    def __str__(self):
        """
        Returns the string representation of a projective point
        """

        return f"({self._x} : {self._y} : {self._z})"

if __name__ == '__main__':
    F = GF(23)
    Z = IntegerRing()

    a = 17
    b = 6
    q = 23
    
    curve = InternalEllipticCurve(F, a, b)
    E = EllipticCurve(F, [a, b])

    tests = [
        ([0, 1, 0], [10, 7, 1]),
        ([10, 7, 1], [7, 13, 1]),
    ]

    for P, Q in tests:
        print(f'We have points {P} and {Q}...')

        # Verifying addition
        P_E = E(P)
        Q_E = E(Q)
        R_E = P_E + Q_E
        P_proj = ProjectivePoint(curve, F(P[0]), F(P[1]), F(P[2]))
        Q_proj = ProjectivePoint(curve, F(Q[0]), F(Q[1]), F(Q[2]))
        R_proj = P_proj + Q_proj
        print(f'Got: P + Q = {R_proj.normalize()}, expected: P + Q = {R_E}')

        # Verifying doubling
        double_P_E = 2*P_E
        double_P_proj = P_proj.double()
        print(f'Got: 2 * P = {double_P_proj.normalize()}, expected: 2 * P = {double_P_E}')

        double_Q_E = 2*Q_E
        double_Q_proj = Q_proj.double()
        print(f'Got: 2 * Q = {double_Q_proj.normalize()}, expected: 2 * Q = {double_Q_E}')

        # Verifying scalar multiplication
        five_P_E = 5*P_E
        five_P_proj = P_proj.mul(Z(5))
        print(f'Got: 5 * P = {five_P_proj.normalize()}, expected: 5 * P = {five_P_E}')

        five_Q_E = 5*Q_E
        five_Q_proj = Q_proj.mul(Z(5))
        print(f'Got: 5 * Q = {five_Q_proj.normalize()}, expected: 5 * Q = {five_Q_E}')