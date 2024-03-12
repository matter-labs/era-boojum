from __future__ import annotations

from copy import copy
from elliptic_curve import InternalEllipticCurve

class ExtendedAffinePoint:
    def __init__(self, curve: InternalEllipticCurve, x: GF, y: GF) -> None:
        """
        Initializes the extended short weierstrass point on 
        the specified elliptic curve

        Args:
            - curve - InternalEllipticCurve, the curve the point is on
            - (x, y) - point on E (in finite field form)
        """
        
        self._curve = curve
        self._x = x
        self._y = y
        self._is_infty = False

    def get_coordinates(self) -> tuple[GF, GF]:
        """
        Returns the coordinates of the point
        """
        return (self._x, self._y)

    @staticmethod
    def infty(curve: InternalEllipticCurve) -> ExtendedAffinePoint:
        """
        Turn the point into infinity
        """

        point = ExtendedAffinePoint(curve, 0, 0)
        point._is_infty = True
        return point

    def negate(self) -> ExtendedAffinePoint:
        """
        Negates the point
        """

        if self._is_infty:
            return self

        copied_self = copy(self)
        copied_self._y = -copied_self._y
        return copied_self
        
    def __add__(self, other: ExtendedAffinePoint) -> ExtendedAffinePoint:
        """
        Adds another ExtendedAffinePoint to the given point (basically, overiding the + operation)

        Args:
            - other - ExtendedAffinePoint, point to add
            
        Returns:
            Added point on the curve
        """
        if self._is_infty:
            return other

        if self._x != other._x:
            return self._add_unequal_x(other)

        if self._y == other._y:
            return self.double()
        
        return ExtendedAffinePoint.infty(self._curve)

    def __sub__(self, other: ExtendedAffinePoint) -> ExtendedAffinePoint:
        """
        Subtracts another ExtendedAffinePoint from the given point (basically, overiding the - operation)

        Args:
            - other - ExtendedAffinePoint, point to subtract
            
        Returns:
            Subtracted point on the curve
        """

        return self + other.negate()

    def double(self) -> ExtendedAffinePoint:
        """
        Doubles the point, returning another point.
        """
        if self._is_infty:
            return self

        assert self._y != 0

        slope = (3 * self._x * self._x + self._curve.a) / (2 * self._y)
        new_x = slope * slope - 2 * self._x
        new_y = slope * (self._x - new_x) - self._y
        return ExtendedAffinePoint(self._curve, new_x, new_y)

    def mul(self, n: Integers) -> ExtendedAffinePoint:
        """
        Multiplies the point by a scalar n

        Args:
            - n - Integer, scalar to multiply by

        Returns:
            New point on the curve
        """

        result = ExtendedAffinePoint.infty(self._curve)
        temp = copy(self)
        bits = n.digits(base=2)
        
        for bit in bits:
            if bit == 1:
                result = result + temp
            
            temp = temp.double()
            
        return result
    
    def _add_unequal_x(self, other: ExtendedAffinePoint) -> ExtendedAffinePoint:
        """
        Adds another Extended Affine Point such that other.x != self.x

        Args:
            - other - ExtendedAffinePoint, point to add

        Returns:
            New point on the curve
        """
        
        assert self._x != other._x
        
        slope = (self._y - other._y) / (self._x - other._x)
        new_x = slope * slope - self._x - other._x
        new_y = slope * (self._x - new_x) - self._y

        return ExtendedAffinePoint(self._curve, new_x, new_y)

    def __str__(self):
        """
        Returns the string representation of a point
        """
        if self._is_infty:
            return "(0 : 1 : 0)"

        return f"({self._x} : {self._y} : 1)"


if __name__ == '__main__':
    F = GF(23)
    Z = IntegerRing()

    a = 17
    b = 6
    q = 23
    
    curve = InternalEllipticCurve(F, a, b)
    E = EllipticCurve(F, [a, b])

    tests = [
        ([10, 7], [7, 13]),
    ]

    for P, Q in tests:
        print(f'We have points {P} and {Q}...')

        # Verifying addition
        P_E = E(P)
        Q_E = E(Q)
        R_E = P_E + Q_E
        P_affine = ExtendedAffinePoint(curve, F(P[0]), F(P[1]))
        Q_affine = ExtendedAffinePoint(curve, F(Q[0]), F(Q[1]))
        R_affine = P_affine + Q_affine
        print(f'Got: P + Q = {R_affine}, expected: P + Q = {R_E}')

        # Verifying doubling
        double_P_E = 2 * P_E
        double_P_affine = P_affine.double()
        print(f'Got: 2 * P = {double_P_affine}, expected: 2 * P = {double_P_E}')

        double_Q_E = 2 * Q_E
        double_Q_affine = Q_affine.double()
        print(f'Got: 2 * Q = {double_Q_affine}, expected: 2 * Q = {double_Q_E}')

        # Verifying scalar multiplication
        five_P_E = 5*P_E
        five_P_affine = P_affine.mul(Z(5))
        print(f'Got: 5 * P = {five_P_affine}, expected: 5 * P = {five_P_E}')

        five_Q_E = 5*Q_E
        five_Q_affine = Q_affine.mul(Z(5))
        print(f'Got: 5 * Q = {five_Q_affine}, expected: 5 * Q = {five_Q_E}')