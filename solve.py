
##
# 2WF90 Algebra for Security -- Software Assignment 2
# Polynomial and Finite Field Arithmetic
# solve.py
##

import json
from random import randint

def RemoveZeroTerms(poly):
    i = len(poly) - 1
    while i > 0 and poly[i] == 0:
        i -= 1
    return poly[: i + 1]

# Get the degree of the polynomial
def DegreeOf(poly):
    return -1 if poly == [0] else len(poly) - 1

def AddPolynomials(f, g, base):
    n = max(len(f), len(g))
    out = [0] * n

    # Iterate through each power and add the terms
    for i in range(n):
        a = f[i] if i < len(f) else 0
        b = g[i] if i < len(g) else 0

        # Also perform a mod
        out[i] = (a + b) % base
    return RemoveZeroTerms(out)

def SubtractPolynomials(f, g, base):
    n = max(len(f), len(g))
    out = [0] * n

    # Iterate through each power and subtract the terms
    for i in range(n):
        a = f[i] if i < len(f) else 0
        b = g[i] if i < len(g) else 0

        # Also perform a mod
        out[i] = (a - b) % base

    return RemoveZeroTerms(out)

def MultiplyPolynomials(f, g, base):
    if f == [0] or g == [0]:
        return [0]
    out = [0] * (len(f) + len(g) - 1)

    # Algorithm from the lecture for multiplying polynomials
    for i, a in enumerate(f):
        if a == 0:
            continue
        for j, b in enumerate(g):
            if b == 0:
                continue

            # Perform a mod for normalization of terms
            out[i + j] = (out[i + j] + a * b) % base
    
    return RemoveZeroTerms(out)

def ComputeInverse(a, mod):
    a = a % mod
    
    # Zero has no inverse modulo anything.
    if a == 0:
        return None

    # Keep track of the current and previous remainders
    previous_remainder, current_remainder = mod, a
    previous_coeff, current_coeff = 0, 1

    while current_remainder != 0:
        quotient = previous_remainder // current_remainder

        # Update remainders: (prev, curr) <- (curr, prev - quotient * curr)
        previous_remainder, current_remainder = (
            current_remainder,
            previous_remainder - quotient * current_remainder,
        )

        # (prev_coeff_a, curr_coeff_a) <- (curr_coeff_a, prev_coeff_a - quotient * curr_coeff_a)
        previous_coeff, current_coeff = (
            current_coeff,
            previous_coeff - quotient * current_coeff,
        )

    # No inverse if gcd != 1
    if previous_remainder != 1:
        return None

    # Perform a mod for normalization of terms
    return previous_coeff % mod

def GetLeadingCoefficient(poly):
    return 0 if poly == [0] else poly[-1]

def DivModPolynomial(f, g, base):
    # Division by the zero polynomial is undefined.
    if g == [0]:
        return None, None

    f_poly = RemoveZeroTerms(f[:])
    g_poly = RemoveZeroTerms(g[:])

    deg_f = DegreeOf(f_poly)
    deg_g = DegreeOf(g_poly)

    # If degree of f is less than degree of g, quotient is 0 and remainder is f.
    if deg_f < deg_g:
        return [0], f_poly

    # Prepare remainder and quotient with the correct length.
    remainder = f_poly[:]
    quotient = [0] * (deg_f - deg_g + 1)

    # Leading coefficient of g and its modular inverse (needed to make g monic stepwise).
    leading_coeff_g = GetLeadingCoefficient(g_poly) % base
    inv_leading_coeff_g = ComputeInverse(leading_coeff_g, base)
    if inv_leading_coeff_g is None:
        # Happens only if lc_g not invertible mod p (e.g., p not prime or lc_g ≡ 0 mod p).
        return None, None

    # Perform long division from highest possible shift down to 0.
    for shift in range(deg_f - deg_g, -1, -1):
        # The coefficient we need to cancel at degree (deg_g + shift).
        factor = (remainder[deg_g + shift] * inv_leading_coeff_g) % base
        quotient[shift] = factor

        if factor != 0:
            # Subtract factor * x^shift * g_poly from the current remainder.
            # This zeros the (deg_g + shift)-th coefficient in 'remainder'.
            for j in range(deg_g + 1):
                remainder[j + shift] = (remainder[j + shift] - factor * g_poly[j]) % base

    # Normalize outputs (trim leading zero)
    remainder = RemoveZeroTerms(remainder)
    quotient = RemoveZeroTerms(quotient)
    return quotient, remainder

def ModPolynomial(f, g, base):
    # Do DivModPolynomial() and return only the remainder
    q, r = DivModPolynomial(f, g, base)
    return r if q is not None else None

def ComputeEGCD(f, g, base):
    f = RemoveZeroTerms([c % base for c in f])
    g = RemoveZeroTerms([c % base for c in g])
    r0, r1 = f, g
    s0, s1 = [1], [0]
    t0, t1 = [0], [1]

    # Following the extended eucledian algorithm
    while r1 != [0]:
        # Compute DivModPolynomial and switch the remainders
        q, r2 = DivModPolynomial(r0, r1, base)
        r0, r1 = r1, r2

        # Subtract from previous terms
        s0, s1 = s1, SubtractPolynomials(s0, MultiplyPolynomials(q, s1, base), base)
        t0, t1 = t1, SubtractPolynomials(t0, MultiplyPolynomials(q, t1, base), base)
    
    # Making sure the polynomials are monic and do not have any zero terms
    d = r0
    if d != [0]:
        leading_coeff_inv = ComputeInverse(GetLeadingCoefficient(d), base)
        d = RemoveZeroTerms([(c * leading_coeff_inv) % base for c in d])
        s0 = RemoveZeroTerms([(c * leading_coeff_inv) % base for c in s0])
        t0 = RemoveZeroTerms([(c * leading_coeff_inv) % base for c in t0])
    return s0, t0, d

def IsPolynomialIrreducible(f, base):
    # Normalize f modulo p and strip leading zeros
    f = RemoveZeroTerms([c % base for c in f])
    n = DegreeOf(f)

    # Handle small degrees
    if n <= 0:
        return n == 1
    if n == 1:
        return True

    X = [0, 1]  # the polynomial X

    # Fast exponentiation of X^exp modulo f (binary exponentiation)
    def _PowX_mod_f(exp):
        result = [1]
        base_poly = X[:]
        e = exp
        while e > 0:
            if e & 1:
                # result = (result * base_poly) mod f
                result = ModPolynomial(MultiplyPolynomials(result, base_poly, base), f, base)
            # base_poly = base_poly^2 mod f
            base_poly = ModPolynomial(MultiplyPolynomials(base_poly, base_poly, base), f, base)
            e >>= 1
        return RemoveZeroTerms(result)

    # Step (1): for i = 1..n-1, ensure gcd(f, X^{p^i} - X) == 1
    for i in range(1, n):
        # Compute X^{p^i} mod f
        x_pow = _PowX_mod_f(pow(base, i))        

        # (X^{p^i} - X) mod f (coeff-wise)  
        h_i = SubtractPolynomials(x_pow, X, base)

        # gcd via your EGCD (returns s, t, d with d monic gcd)
        _, _, gcd_i = ComputeEGCD(f, h_i, base)
        if gcd_i != [1]:
            return False

    # Step (2): check X^{p^n} ≡ X (mod f)
    x_pow_n = _PowX_mod_f(pow(base, n))
    return x_pow_n == X


def GenerateIrreduciblePolynomial(p, n):
    # Special case: degree 1 (linear polynomials) are always irreducible if leading != 0.
    # Pick a single deterministic representative: (b, a) with a from the fixed leading order, b = 1 mod p.
    if n == 1:
        seed_b = 1
        # Leading coefficient order: odds (desc), then evens (asc)
        odds = list(range(1, p, 2))[::-1]
        evens = list(range(2, p, 2))
        lead_order = odds + evens
        for a in lead_order:
            b = seed_b % p
            return [b, a]

    # Build per position rotated orders for a0..a_{n-1}.
    # Example for p=5: a position with start=2 produces order [2,3,4,0,1].
    base_seed = [1, 2, 2, 4, 0]
    orders = []
    for i in range(n):
        start = base_seed[i % len(base_seed)] % p
        pos_order = [(start + k) % p for k in range(p)]
        orders.append(pos_order)

    # Leading coefficient order: odds (desc), then even nonzero (asc); 0 is excluded.
    odds = list(range(1, p, 2))[::-1]
    evens = list(range(2, p, 2))
    lead_order = odds + evens

    # Iterate all candidates in the deterministic order described above.
    total = p ** n  # number of lower-coefficient combinations
    for an in lead_order:
        for idx in range(total):
            # Decode idx in base p, using digit i to pick the i-th coefficient from orders[i].
            x = idx
            coeffs = []
            for i in range(n):
                digit = x % p
                x //= p
                coeffs.append(orders[i][digit])

            # Full polynomial: [a0, a1, ..., a_{n-1}, an]
            f = coeffs + [an]

            # Check irreducibility; return the first hit in this fixed enumeration.
            if IsPolynomialIrreducible(f, p):
                return RemoveZeroTerms([c % p for c in f])

    return None

def IsPrimitive(element, poly, p):
    # Zero can never be a generator of the multiplicative group.
    if element == [0]:
        return False

    # Field size is p^n where n = deg(poly)
    n = DegreeOf(poly)

    # Compute p^n (field size) without pow to keep style consistent
    field_size = 1
    for _ in range(n):
        field_size *= p

    group_order = field_size - 1  # |(F_{p^n})^*|

    # Get the distinct prime factors of the group order
    prime_divisors = FactorizePolynomial(group_order)

    one = [1]
    # For each prime divisor r of the group order, test that
    # element^{group_order / r} != 1. If it equals 1 for any r,
    # then the element's order divides (group_order / r) < group_order,
    # so it is not a generator.
    for r in prime_divisors:
        exponent = group_order // r
        if FieldPower(element, exponent, poly, p) == one:
            return False

    # Passed all tests ⇒ element has full order group_order ⇒ primitive.
    return True

def GeneratePrimitiveElement(poly, p):
    degree = DegreeOf(poly)
    if degree < 1:
        return None  # field not well-formed for n < 1

    # Enumerate constants with a fixed preference:
    #   odd constants ascending first, then even constants ascending.
    def constant_candidates():
        for c in range(1, p, 2):  # odds: 1,3,5,...
            yield c
        for c in range(0, p, 2):  # evens: 0,2,4,...
            yield c

    # (1) Prefer monic linear candidates: a(x) = c + 1*x  ->  [c, 1]
    for c in constant_candidates():
        candidate = RemoveZeroTerms([c, 1])
        if IsPrimitive(candidate, poly, p):
            return candidate

    # (2) Next, any linear [c, a1] with a1 in 1..p-1; for each a1, scan constants as above.
    for leading_coeff in range(1, p):
        for c in constant_candidates():
            candidate = RemoveZeroTerms([c, leading_coeff])
            if IsPrimitive(candidate, poly, p):
                return candidate

    # (3) Finally, scan all nonzero elements of F_{p^n} in ascending base-p order
    # on their coefficient vector [a0, a1, ..., a_{degree-1}] (a0 fastest).
    total = p ** degree
    for counter in range(1, total):
        # Decode 'counter' in base p to get the coefficient vector.
        value = counter
        coeffs = []
        for _ in range(degree):
            coeffs.append(value % p)
            value //= p
        candidate = RemoveZeroTerms(coeffs)
        if IsPrimitive(candidate, poly, p):
            return candidate

    return None


# Normalize the polynomial to mod p
def Normalize(poly, p):
    return RemoveZeroTerms([c % p for c in poly])

def FieldMultiply(a, b, mod_poly, p):
    product = MultiplyPolynomials(a, b, p)
    return ModPolynomial(product, mod_poly, p)

def FieldInverse(element, mod_poly, p):
    # Zero has no multiplicative inverse.
    if element == [0]:
        return None

    # ComputeEGCD returns polynomials (s, t, d) with: s*element + t*mod_poly = d
    s_coeffs, t_coeffs, gcd_poly = ComputeEGCD(element, mod_poly, p)

    # If gcd == 1, `s` is the inverse of `element` modulo `mod_poly`.
    if gcd_poly == [1]:
        return ModPolynomial(s_coeffs, mod_poly, p)

    return None

def FieldDivide(numerator, denominator, mod_poly, p):
    inv = FieldInverse(denominator, mod_poly, p)
    if inv is None:
        return None
    return FieldMultiply(numerator, inv, mod_poly, p)

def FieldPower(base, exponent, mod_poly, p):
    result = [1]
    base = Normalize(base[:], p) # Ensure coefficients are in 0..p-1 and trimmed
    e = exponent

    # Binary exponentiation
    while e > 0:
        if e & 1:
            # If the current bit is 1, multiply result by current base
            result = FieldMultiply(result, base, mod_poly, p)
        # Square the base each iteration (advance to next bit)
        base = FieldMultiply(base, base, mod_poly, p)
        e >>= 1  # Shift to process the next bit
    return result


def FactorizePolynomial(n):
    factors = []
    # Start trial division with 2, then continue with odd numbers only.
    d = 2
    while d * d <= n:
        if n % d == 0:
            # We found a prime factor d; record it once.
            factors.append(d)

            # Remove all copies of d from n so we don't report it again.
            while n % d == 0:
                n //= d
        # Increment: after testing 2, skip even numbers
        d += 1 if d == 2 else 2
    if n > 1:
        factors.append(n)
    return factors


def solve_exercise(exercise_location: str, answer_location: str):
    with open(exercise_location, "r") as exercise_file:
        exercise = json.load(exercise_file)

    t = exercise.get("type")
    task = exercise.get("task")
    p = int(exercise.get("integer_modulus"))

    answer_obj = None

    if t == "polynomial_arithmetic":
        f = exercise.get("f")
        g = exercise.get("g")

        if task == "addition":
            res = AddPolynomials(Normalize(f, p), Normalize(g, p), p)
            answer_obj = {"answer": res}

        elif task == "subtraction":
            res = SubtractPolynomials(Normalize(f, p), Normalize(g, p), p)
            answer_obj = {"answer": res}

        elif task == "multiplication":
            res = MultiplyPolynomials(Normalize(f, p), Normalize(g, p), p)
            answer_obj = {"answer": res}

        elif task == "long_division":
            q, r = DivModPolynomial(Normalize(f, p), Normalize(g, p), p)
            if q is None:
                answer_obj = {"answer-q": None, "answer-r": None}
            else:
                answer_obj = {"answer-q": q, "answer-r": r}

        elif task == "extended_euclidean_algorithm":
            a, b, d = ComputeEGCD(Normalize(f, p), Normalize(g, p), p)
            answer_obj = {"answer-a": a, "answer-b": b, "answer-gcd": d}

        elif task == "irreducibility_check":
            is_irred = IsPolynomialIrreducible(Normalize(f, p), p)
            answer_obj = {"answer": bool(is_irred)}

        elif task == "irreducible_element_generation":
            n = int(exercise.get("degree"))
            poly = GenerateIrreduciblePolynomial(p, n)
            answer_obj = {"answer": poly if poly is not None else None}

        else:
            answer_obj = {"answer": None}

    else:  # finite_field_arithmetic
        h = Normalize(exercise.get("polynomial_modulus"), p)

        if task in ("addition", "subtraction", "multiplication", "division"):
            f = Normalize(exercise.get("f"), p)
            g = Normalize(exercise.get("g"), p)

            if task == "addition":
                res = AddPolynomials(f, g, p)
                answer_obj = {"answer": res}
            elif task == "subtraction":
                res = SubtractPolynomials(f, g, p)
                answer_obj = {"answer": res}
            elif task == "multiplication":
                res = ModPolynomial(MultiplyPolynomials(f, g, p), h, p)
                answer_obj = {"answer": res}
            elif task == "division":
                if g == [0]:
                    answer_obj = {"answer": None}
                else:
                    res = FieldDivide(f, g, h, p)
                    answer_obj = {"answer": res if res is not None else None}

        elif task == "inversion":
            f = Normalize(exercise.get("f"), p)
            if f == [0]:
                answer_obj = {"answer": None}
            else:
                inv = FieldInverse(f, h, p)
                answer_obj = {"answer": inv if inv is not None else None}

        elif task == "primitivity_check":
            f = Normalize(exercise.get("f"), p)
            is_prim = IsPrimitive(f, h, p)
            answer_obj = {"answer": bool(is_prim)}

        elif task == "primitive_element_generation":
            elem = GeneratePrimitiveElement(h, p)
            answer_obj = {"answer": elem if elem is not None else None}

        elif task == "irreducible_element_generation":
            n = int(exercise.get("degree"))
            poly = GenerateIrreduciblePolynomial(p, n)
            answer_obj = {"answer": poly if poly is not None else None}

        else:
            answer_obj = {"answer": None}

    with open(answer_location, "w") as answer_file:
        json.dump(answer_obj, answer_file, indent=4)

# You can call your function from here
# Please do not *run* code outside this block
# You can however define other functions or constants
if __name__ == '__main__':
    # Example (update paths as needed to test locally):
    solve_exercise('Realistic/Exercises/exercise1.json', 'answer.json')
    pass
