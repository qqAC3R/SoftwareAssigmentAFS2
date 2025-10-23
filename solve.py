
##
# 2WF90 Algebra for Security -- Software Assignment 2
# Polynomial and Finite Field Arithmetic
# solve.py
##

import json
from random import randint

############################################################
# Utility helpers
############################################################

def _trim(poly):
    i = len(poly) - 1
    while i > 0 and poly[i] == 0:
        i -= 1
    return poly[: i + 1]

def _deg(poly):
    return -1 if poly == [0] else len(poly) - 1

def _add_poly(f, g, p):
    n = max(len(f), len(g))
    out = [0] * n
    for i in range(n):
        a = f[i] if i < len(f) else 0
        b = g[i] if i < len(g) else 0
        out[i] = (a + b) % p
    return _trim(out)

def _sub_poly(f, g, p):
    n = max(len(f), len(g))
    out = [0] * n
    for i in range(n):
        a = f[i] if i < len(f) else 0
        b = g[i] if i < len(g) else 0
        out[i] = (a - b) % p
    return _trim(out)

def _mul_poly(f, g, p):
    if f == [0] or g == [0]:
        return [0]
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        if a == 0:
            continue
        for j, b in enumerate(g):
            if b == 0:
                continue
            out[i + j] = (out[i + j] + a * b) % p
    return _trim(out)

def _inv_int(a, p):
    a %= p
    if a == 0:
        return None
    t, new_t = 0, 1
    r, new_r = p, a
    while new_r != 0:
        q = r // new_r
        t, new_t = new_t, t - q * new_t
        r, new_r = new_r, r - q * new_r
    if r != 1:
        return None
    return t % p

def _leading_coeff(poly):
    return 0 if poly == [0] else poly[-1]

def _divmod_poly(f, g, p):
    if g == [0]:
        return None, None
    f = _trim(f[:])
    g = _trim(g[:])
    if _deg(f) < _deg(g):
        return [0], f
    r = f[:]
    q = [0] * (_deg(f) - _deg(g) + 1)
    g_lc = _leading_coeff(g) % p
    g_lc_inv = _inv_int(g_lc, p)
    for k in range(_deg(f) - _deg(g), -1, -1):
        coeff = r[_deg(g) + k] * g_lc_inv % p
        q[k] = coeff
        if coeff != 0:
            for j in range(_deg(g) + 1):
                r[j + k] = (r[j + k] - coeff * g[j]) % p
    r = _trim(r)
    q = _trim(q)
    return q, r

def _mod_poly(f, g, p):
    q, r = _divmod_poly(f, g, p)
    return r if q is not None else None

def _egcd_poly(f, g, p):
    f = _trim([c % p for c in f])
    g = _trim([c % p for c in g])
    r0, r1 = f, g
    s0, s1 = [1], [0]
    t0, t1 = [0], [1]
    while r1 != [0]:
        q, r2 = _divmod_poly(r0, r1, p)
        r0, r1 = r1, r2
        s0, s1 = s1, _sub_poly(s0, _mul_poly(q, s1, p), p)
        t0, t1 = t1, _sub_poly(t0, _mul_poly(q, t1, p), p)
    d = r0
    if d != [0]:
        lc_inv = _inv_int(_leading_coeff(d), p)
        d = _trim([(c * lc_inv) % p for c in d])
        s0 = _trim([(c * lc_inv) % p for c in s0])
        t0 = _trim([(c * lc_inv) % p for c in t0])
    return s0, t0, d

############################################################
# Irreducibility over Z_p[X]
############################################################

def _iter_monic_polys_of_degree(d, p):
    """Yield all monic polynomials of exact degree d without itertools.product."""
    if d <= 0:
        return
    total = p ** d
    for N in range(total):
        x = N
        coeffs = []
        for _ in range(d):
            coeffs.append(x % p)
            x //= p
        yield coeffs + [1]

def _is_irreducible(f, p):
    f = _trim([c % p for c in f])
    n = _deg(f)
    if n <= 0:
        return n == 1
    if n == 1:
        return True
    max_d = n // 2
    for d in range(1, max_d + 1):
        for g in _iter_monic_polys_of_degree(d, p):
            q, r = _divmod_poly(f, g, p)
            if q is not None and r == [0]:
                return False
    return True

def _gen_irreducible(p, n, max_tries=20000):
    """Deterministic irreducible generator (no itertools).
    Search order:
      - Leading coefficient: odd numbers in descending order, then even nonzero ascending.
      - Coefficients a0..a_{n-1}: per-position rotated ascending order starting from seed
        vector [1,2,2,4,0] (cycled as needed).
    """
    if n == 1:
        seed_b = 1
        odds = list(range(1, p, 2))[::-1]
        evens = list(range(2, p, 2))
        lead_order = odds + evens
        for a in lead_order:
            b = seed_b % p
            return [b, a]

    base_seed = [1, 2, 2, 4, 0]
    orders = []
    for i in range(n):
        start = base_seed[i % len(base_seed)] % p
        pos_order = [(start + k) % p for k in range(p)]
        orders.append(pos_order)

    odds = list(range(1, p, 2))[::-1]
    evens = list(range(2, p, 2))
    lead_order = odds + evens

    total = p ** n
    for an in lead_order:
        for idx in range(total):
            x = idx
            coeffs = []
            for i in range(n):
                digit = x % p
                x //= p
                coeffs.append(orders[i][digit])
            f = coeffs + [an]
            if _is_irreducible(f, p):
                return _trim([c % p for c in f])
    return None

############################################################
# Finite field helpers: arithmetic in Z_p[X]/(h)
############################################################

def _ff_reduce(a, h, p):
    return _mod_poly(a, h, p)

def _ff_add(a, b, h, p):
    return _add_poly(a, b, p)

def _ff_sub(a, b, h, p):
    return _sub_poly(a, b, p)

def _ff_mul(a, b, h, p):
    return _ff_reduce(_mul_poly(a, b, p), h, p)

def _ff_inv(a, h, p):
    if a == [0]:
        return None
    s, t, d = _egcd_poly(a, h, p)
    if d == [1]:
        return _ff_reduce(s, h, p)
    else:
        return None

def _ff_div(a, b, h, p):
    inv = _ff_inv(b, h, p)
    if inv is None:
        return None
    return _ff_mul(a, inv, h, p)

def _ff_pow(a, e, h, p):
    result = [1]
    base = _trim(a[:])
    while e > 0:
        if e & 1:
            result = _ff_mul(result, base, h, p)
        base = _ff_mul(base, base, h, p)
        e >>= 1
    return result

def _factorize(n):
    factors = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            factors.append(d)
            while n % d == 0:
                n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        factors.append(n)
    return factors

############################################################
# Primitivity in finite fields
############################################################

def _is_primitive(a, h, p):
    if a == [0]:
        return False
    n = _deg(h)
    q = 1
    for _ in range(n):
        q *= p
    order = q - 1
    prime_factors = _factorize(order)
    one = [1]
    for r in prime_factors:
        exp = order // r
        if _ff_pow(a, exp, h, p) == one:
            return False
    return True

def _gen_primitive(h, p):
    """Deterministic generation with a stable preference, no itertools:
    1) Prefer monic linear [c, 1], scanning odd c ascending then even c.
    2) Then any linear [c, a1] with a1=1..p-1 (odd c first).
    3) Then all non-zero elements in ascending base-p order.
    """
    n = _deg(h)
    if n < 1:
        return None

    def constants():
        for c in range(1, p, 2):
            yield c
        for c in range(0, p, 2):
            yield c

    for c in constants():
        a = _trim([c, 1])
        if _is_primitive(a, h, p):
            return a

    for a1 in range(1, p):
        for c in constants():
            a = _trim([c, a1])
            if _is_primitive(a, h, p):
                return a

    total = p ** n
    for N in range(1, total):
        x = N
        coeffs = []
        for _ in range(n):
            coeffs.append(x % p)
            x //= p
        a = _trim(coeffs)
        if _is_primitive(a, h, p):
            return a
    return None

############################################################
# Main solver
############################################################

def _canonical(poly, p):
    return _trim([c % p for c in poly])

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
            res = _add_poly(_canonical(f, p), _canonical(g, p), p)
            answer_obj = {"answer": res}

        elif task == "subtraction":
            res = _sub_poly(_canonical(f, p), _canonical(g, p), p)
            answer_obj = {"answer": res}

        elif task == "multiplication":
            res = _mul_poly(_canonical(f, p), _canonical(g, p), p)
            answer_obj = {"answer": res}

        elif task == "long_division":
            q, r = _divmod_poly(_canonical(f, p), _canonical(g, p), p)
            if q is None:
                answer_obj = {"answer-q": None, "answer-r": None}
            else:
                answer_obj = {"answer-q": q, "answer-r": r}

        elif task == "extended_euclidean_algorithm":
            a, b, d = _egcd_poly(_canonical(f, p), _canonical(g, p), p)
            answer_obj = {"answer-a": a, "answer-b": b, "answer-gcd": d}

        elif task == "irreducibility_check":
            is_irred = _is_irreducible(_canonical(f, p), p)
            answer_obj = {"answer": bool(is_irred)}

        elif task == "irreducible_element_generation":
            n = int(exercise.get("degree"))
            poly = _gen_irreducible(p, n)
            answer_obj = {"answer": poly if poly is not None else None}

        else:
            answer_obj = {"answer": None}

    else:  # finite_field_arithmetic
        h = _canonical(exercise.get("polynomial_modulus"), p)

        if task in ("addition", "subtraction", "multiplication", "division"):
            f = _canonical(exercise.get("f"), p)
            g = _canonical(exercise.get("g"), p)

            if task == "addition":
                res = _ff_add(f, g, h, p)
                answer_obj = {"answer": res}
            elif task == "subtraction":
                res = _ff_sub(f, g, h, p)
                answer_obj = {"answer": res}
            elif task == "multiplication":
                res = _ff_mul(f, g, h, p)
                answer_obj = {"answer": res}
            elif task == "division":
                if g == [0]:
                    answer_obj = {"answer": None}
                else:
                    res = _ff_div(f, g, h, p)
                    answer_obj = {"answer": res if res is not None else None}

        elif task == "inversion":
            f = _canonical(exercise.get("f"), p)
            if f == [0]:
                answer_obj = {"answer": None}
            else:
                inv = _ff_inv(f, h, p)
                answer_obj = {"answer": inv if inv is not None else None}

        elif task == "primitivity_check":
            f = _canonical(exercise.get("f"), p)
            is_prim = _is_primitive(f, h, p)
            answer_obj = {"answer": bool(is_prim)}

        elif task == "primitive_element_generation":
            elem = _gen_primitive(h, p)
            answer_obj = {"answer": elem if elem is not None else None}

        elif task == "irreducible_element_generation":
            n = int(exercise.get("degree"))
            poly = _gen_irreducible(p, n)
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

    for i in range(18):
        solve_exercise('Realistic/Exercises/exercise' + str(i) + ".json", 'answer.json')

        with open('Realistic/Answers/answer' + str(i) + ".json", "r") as exercise_file:
            file_content_expected = json.load(exercise_file)

        with open('answer.json', "r") as exercise_file:
            file_content_actual = json.load(exercise_file)

        isCorrect = file_content_expected.items() == file_content_actual.items()

        print("For exercise " + str(i) + ", it is " + str(isCorrect))
    
    pass
