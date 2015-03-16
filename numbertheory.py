#
# A Collection of Number Theory Algorithms
#
# (C) Copyright 2010-2014, Brian Gladman
#

from random import randrange
from itertools import product
from functools import reduce
from operator import mul

def gcd(a, *r):
  '''
  Greatest Common Divisor for a sequence of values

  >>> gcd(1701, 13979)
  7

  >>> gcd(117, -17883411)
  39

  >>> gcd(3549, 70161,  336882, 702702)
  273
  '''
  for b in r:
    while b:
      a, b = b, a % b
  return abs(a)

def xgcd(a, b):
  '''
  Euclid's Extended GCD Algorithm

  >>> xgcd(314159265, 271828186)
  (-18013273, 20818432, 7)
  '''
  u, u1 = 1, 0
  v, v1 = 0, 1
  while b:
    q, r = divmod(a,  b)
    a, b = b, r
    u, u1 = u1, u - q * u1
    v, v1 = v1, v - q * v1
  return (u, v, a) if a > 0 else (-u, -v, -a)

def lcm(a, b):
  '''
  Least Common Multiple (LCM)
  '''
  g = gcd(a, b)
  return abs(a * b) // g if g else 0

def cong(a, p, n):
  '''
  Solve the congruence a * x == p (mod n)

  >>> cong(13, 17, 19)
  13

  >>> cong(17, 19, 23)
  16

  >>> cong(14, 6, 91) is None
  True
  '''
  g = gcd(a, n)
  if p % g > 0:
    return None
  return (xgcd(a, n)[0] * (p // g)) % (n // g)

def inv(a, n):
  '''
  Find the modular inverse of a (mod n)

  >>> inv(271828, 314159)
  898

  >>> inv(314159, 271828)
  271051
  '''
  return None if gcd(a, n) > 1 else xgcd(a, n)[0] % n

def crt(a, m):
  '''
  The Chinese Remainder Theorem (CRT)

  Solve the equations x = a[i] mod m[i] for x

  >>> crt((2, 3, 5, 7), (97, 101, 103, 107))
  96747802
  '''
  def _crt(a, b, m, n):
    d = gcd(m, n)
    if (a - b) % d:
      return None
    x, y, z = m // d, n // d, (m * n) // d
    p, q, r = xgcd(x, y)
    return (b * p * x + a * q * y) % z

  if len(a) == len(m):
    x, mm = a[0], m[0]
    for i in range(1, len(a)):
      x = _crt(a[i], x, m[i], mm)
      if not x:
        break
      mm = lcm(m[i], mm)
  else:
    raise IndexError
  return x

def miller_rabin(n, r = 10):
  '''
  Probable Prime Test.

  If this test returns False, the input number is
  definitely composite.  If it returns True it is
  likely to be a prime but there is a probability
  p < (1/4)^r after r tests that it is composite.

  >>> miller_rabin(1000001)
  False

  >>> miller_rabin(1000003)
  True

  >>> miller_rabin(1000007)
  False
  '''
  if n < 10 or n % 2 == 0:
    return n in (2, 3, 5, 7)
  d, s = n - 1, 0
  while d % 2 == 0:
    d //= 2
    s += 1
  for i in range(r):
    a = randrange(2, n - 1)
    x = pow(a, d, n)
    if x != 1 and x != n - 1:
      for j in range(s - 1):
        x = (x * x) % n
#       if x == 1:
#         return False
        if x == n - 1:
          break
      else:
        return False
  return True

# A Prime Class based on Jim Randell's version  (see his
# version at http://www.magwag.plus.com/jim/enigma.html)
#
# Author:   Brian Gladman <riemannic@gmail.com>
# Credits:  Jim Randell <jim.randell@gmail.com>

class Primes(object):
  '''
    A simple prime sieve.

    len(Primes(1000000))
    78498

    >>> Primes(43).list()
    [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]

    >>> primes = Primes(1000000)
    >>> 10007 in primes
    True

    >>> sum(primes.generate()) == 37550402023
    True

    >>> sum(primes) == 37550402023
    True
  '''
  # the sieve array in list form (these are class
  # variables to avoid re-creating the sieve for
  # each instance
  sieve = []
  # the length of the sieve (but note that self.hi
  # may be less than this if the sieve 'seen' by
  # an instance is of lesser length)
  hi = 0

  def __init__(self, n=None, extend=False, exf=lambda x:x + x // 2):
    '''
    Initialise the sieve for primes up to n - 1.

    If n is larger than the existing sieve, it will
    be extended to match n.
    '''
    if n is None or extend:
      self.exf = exf
      self.hi = Primes.hi
    if n is not None:
      self.exf = exf if extend else None
      if n > Primes.hi:
        self.extend(n)
      elif n < Primes.hi:
        # don't truncate the sieve but set the instance
        # limit below the top of the full sieve
        self.hi = n

  def extend(self, n):
    '''
    Extends the sieve for primes up to n - 1.
    '''
    if n > Primes.hi:
      s = Primes.sieve
      h = (n - 2) // 2
      l = len(s)
      if h <= l:
        return
      s += [True] * (h - l)
      for i in range((round(n ** 0.5) - 1) // 2):
        if s[i]:
          j = i + i + 3
#         a = i + j * ((l + i + 2) // j + (0 if l else 1))
          a = (j * max(j, ((2 * l + 2 + j) // j) | 1) - 3) // 2
          s[a:h:j] = [False] * ((h - a + j - 1) // j)
      Primes.hi = n
    self.hi = n

  def __len__(self):
    '''
    Find how many primes are in the sieve region.

    >>> len(Primes(100000))
    9592

    >>> len(Primes(1000000))
    78498
    '''
    if self.hi == Primes.hi:
      return 1 + Primes.sieve.count(True)
    else:
      return 1 + Primes.sieve[:(self.hi - 2) // 2].count(True)

  def end(self):
    '''
    Return the current end values for the sieve
    '''

    return self.hi, Primes.hi

  def __contains__(self, n):
    '''
    Check if a number within the sieve range is prime.

    >>> 1000031 in Primes()
    False

    >>> 1000033 in Primes()
    True

    >>> 1000037 in Primes()
    True

    >>> 1000039 in Primes()
    True
    '''
    if n <= 2 or not (n & 1):
      return n == 2
    if n >= self.hi and self.exf:
        self.extend(n + 1)
    try:
      return Primes.sieve[(n - 3) //2]
    except IndexError:
      return False

  def list(self, start=0, end=0):
    '''
    Return a list of primes in the specified range.

    >>> Primes(47).list()
    [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]

    >>> Primes().list(1000000, 1000100)
    [1000003, 1000033, 1000037, 1000039, 1000081, 1000099]
    '''

    if not end:
      end = self.hi
    elif Primes.hi < end:
      self.extend(end)
    s = Primes.sieve
    lo, hi = max(start // 2 - 1, 0), (end - 2) // 2
    return ( ([2] if start < 3 and end > 2 else []) +
             [2 * i + 3 for i in range(lo, hi) if s[i]] )

  def generate(self, start=0, end=0):
    '''
    Generate primes in the range(start, end).

    If end is set to 'None' the generator continues until
    it is terminated by the caller

    >>> sum(x for x in Primes(1000))
    76127

    >>> sum(x for x in Primes(1000000))
    37550402023
    '''

    s, hi = Primes.sieve, self.hi
    if end == 0:
      end = None if self.exf else hi
    if end is None:
      if not self.exf:
        raise ValueError
      while True:
        end = max(100, self.exf(start))
        yield from self.generate(start, end)
        start = end
    else:
      if start < 3:
        start = 0
        if end is None or end > 2:
          yield 2
      else:
        start = (start - 3) // 2
      if end > hi:
        self.extend(end)
      for i in range(start, (end - 3) // 2):
        if s[i]:
          yield 2 * i + 3
      # possibly better alternative for large sieves
      # i, top = start, end // 2
      # try:
      #  i = s.index(True, i) + 1
      #  while i < top:
      #    yield 2 * i + 1
      #    i = s.index(True, i) + 1
      # except ValueError:
      #  pass

  def produce(self, start, end, block_len=10000):
    '''
    Generate primes in the range(start, end).

    This generator is intended for situations where a
    few large primes are needed. It is slower than the
    earlier version but uses a lot less memory by only
    keeping a part of the sieve in memory at any time.

    The start and stop values must be given and the
    optional parameter block_len can be set to give
    the minimum size of the blocks in the sieve.

    >>> b = 100000000
    >>> print(sum(x for x in Primes().produce(b, b + 1000)))
    5400026920
    '''
    if start < 3 and end > 2:
      yield 2

    b_len = max(block_len, round(end ** 0.5 + 1))
    self.extend(b_len)
    b_len, hi = (b_len - 3) // 2, (end - 3) //2
    base, pos = divmod(max(start // 2 - 1, 0), b_len)
    base, lo_blk = base * b_len, Primes.sieve

    while True:
      if not base:
        hi_blk = lo_blk[0:b_len]
      else:
        b_len = min(b_len, hi - base)
        hi_blk = [True] * b_len
        for i in range((round((2 * (base + b_len) + 1) ** 0.5) - 1) // 2):
          if lo_blk[i]:
            j = i + i + 3
            a = i + j * ((base + i + 2) // j) - base
#           a = max(i + j * ((base + i + 2) // j), (j * j - 3) // 2) - base
            hi_blk[a:b_len:j] = [False] * ((b_len - a + j - 1) // j)
      try:
        while True:
          pos = hi_blk.index(True, pos) + 1
          yield 2 * (base + pos) + 1
      except ValueError:
        pos = 0
        base += b_len
        if base >= hi:
          break

  __iter__ = generate

def is_prime(n):
  '''
  Test whether a positive integer is prime

  >>> all(is_prime(n) for n in (2, 3, 5, 7, 97, 101, 191, 193, 197, 199))
  True

  >>> all(not is_prime(x) for x in (25, 49, 121, 169, 289))
  True
  '''
  return n == 2 or all(n % i for i in Primes(int(n ** 0.5 + 2)))

def factor(n, p_max=None):
  '''
  Generate the prime factors (and units) of n as (prime, multiplicity)
  tuples (p_max is the maximum prime to be considered and is unlimited
  by default)

  >>> tuple(factor(9973 * 1010203 * 123456789))
  ((3, 2), (3607, 1), (3803, 1), (9973, 1), (1010203, 1))
  '''
  if n == 0:
    yield ()
  elif n == 1:
    yield (1, 0)
  else:
    if n < 0:
      yield (-1, 1)
      n = abs(n)
    if n in (2, 3, 5, 7):
      yield (n, 1)
    else:
      pr = Primes()
      pg  = pr.generate(0, 100)
      for p in pg:
        cnt = 0
        while not n % p:
          cnt += 1
          n //= p
        if cnt:
          yield (p, cnt)
        if n < p * p:
          break
      if n > 1:
        if n < 10000 or miller_rabin(n):
          yield (n, 1)
        else:
          pr.extend(1000)
          pg  = pr.generate(100, p_max)
          for p in pg:
            cnt = 0
            while not n % p:
              cnt += 1
              n //= p
            if cnt:
              yield (p, cnt)
            if n < p * p:
              break
          else:
            if not miller_rabin(n):
              raise ValueError
          if n > 1:
            yield (n, 1)

def factors(n):
    '''
    Return a list of the prime factors of a positive integer n with
    primes occurring multiple times according to their multiplicity

    >>> tuple(factors(8 * 81 * 343 * 1331))
    (2, 2, 2, 3, 3, 3, 3, 7, 7, 7, 11, 11, 11)
    '''
    if abs(n) < 2:
      yield (0, 1) if not n else (1, 0)
    else:
      for p, e in factor(n):
        for i in range(e):
          yield p

def divisors(n):
  '''
  Return the divisors of the positive integer n

  >>> divisors(11 * 13 * 17)
  (1, 11, 13, 17, 143, 187, 221, 2431)
  '''
  if n == 0:
    return tuple()
  f = [1]
  for p, e in factor(n):
    f += [x * p ** (k + 1) for k in range(e) for x in f]
  f.sort()
  return tuple(f)

def divisor_pairs(n):
  '''
  Return the divisor pairs for the positive integer n

  >>> divisor_pairs(23 * 37 * 49)
  ((1, 41699), (7, 5957), (23, 1813), (37, 1127), (49, 851), (161, 259))
  >>> divisor_pairs(25 * 49)
  ((1, 1225), (5, 245), (7, 175), (25, 49), (35, 35))
  '''
  d = divisors(n)
  return tuple(zip(d[:(len(d) + 1) // 2], d[::-1]))

def tau(n):
  '''
  return tau(n) - the number of divisors of a positive integer n

  >>> tau(3 ** 4 * 35 ** 5)
  180

  >>> tau(2 ** 2 * 3 ** 3 * 5 ** 5 * 7 ** 7)
  576
  '''
  return reduce(mul, ((e + 1) for p, e in factor(n)))

def omega(n):
  '''
  return omega(n) - the sum of the divisors of a positive integer n

  >>> omega(3 ** 4 * 35 ** 5)
  9267250608

  >>> omega(2 ** 2 * 3 ** 3 * 5 ** 5 * 7 ** 7)
  1050807744000
  '''
  if n < 2:
    return n
  return reduce(mul, ((p ** (e + 1) - 1) // (p - 1) for p, e in factor(n)))

def phi(n):
  '''
  Return phi(n) - the Euler phi function for a positive integer n

  >>> phi(3 ** 4 * 35 ** 5)
  1944810000

  >>> phi(2 ** 2 * 3 ** 3 * 5 ** 5 * 7 ** 7)
  63530460000

  >>> phi(1234567890)
  329040288
  '''
  if n < 2:
    return n
  return reduce(mul, ((p - 1) * p ** (e - 1) for p, e in factor(n)))

def mu(n):
  '''
  return mu(n) - the Mobius function for n defined as:

      1          if n == 1
      0          if p ** 2 divides n for some p
      (-1) ** r  if n is the product of r distinct primes

  >>> mu(1234567894)
  -1

  >>> mu(1234567895)
  1

  >>> mu(1234567896)
  0
  '''
  if n == 1:
    return 1
  f = tuple(factor(n))
  if any(e > 1 for p, e in f):
    return 0
  else:
    return -1 if len(f) % 2 else 1

def jacobi(a, n):
  '''
  The Jacobi symbol (for odd n).  Algorithm 2.3.5 from
  Prime Numbers by Richard Crandall and Carl Pomerance

  >>> jacobi(5, 97)
  -1

  >>> jacobi(6, 96)
  0

  >>> jacobi(6, 97)
  1
  '''
  a %= n
  t = 1
  while a:
    while not a % 2:
      a //= 2
      if n % 8 in (3, 5):
        t = -t
    a, n = n, a
    if a % 4 == n % 4 == 3:
      t = -t
    a %= n
  return t if n == 1 else 0

def sqrt_mod_p(a, p):
  '''
  The Tonelli-Shanks algorithm for modular square roots
  for prime moduli.  This is Algorithm 2.3.8 from Prime
  Numbers by Richard Crandall and Carl Pomerance.

  >> sqrt_mod_p(53, 97)
  76

  >>> sqrt_mod_p(54, 97)
  65

  >>> sqrt_mod_p(55, 97) is None
  True
  '''
  a = a % p
  if jacobi(a, p) != 1:
    return None
  if p % 8 in (3, 7):
    pow(a, (p + 1) // 4, p)
  elif p % 8 == 5:
    x = pow(a, (p + 3) // 8, p)
    c = (x * x) % p
    if c != a % p:
      x *= pow(2, (p - 1) //4, p)
    return x

  d = 2
  while jacobi(d, p) != -1:
    d += 1

  s, t = 0, p - 1
  while not t % 2:
    t //= 2
    s += 1

  at, dt, m = pow(a, t, p), pow(d, t, p), 0
  for i in range(s):
    if pow(at * pow(dt, m), pow(2, s - 1 - i), p) == (p - 1):
      m += pow(2, i)
  return (pow(a, (t + 1) // 2, p) * pow(dt, m // 2, p)) % p

def hensel_lift_2(a, e):
  '''
  Hensel root lifting for powers of two

  Return a tuple giving the roots s such
  that s ** 2 == a mod (2 ** e)

  >>> hensel_lift_2(17, 10)
  (233, 279, 745, 791)

  >>> hensel_lift_2(25, 12)
  (5, 2043, 2053, 4091)
  '''
  if e == 1:
    return 1,
  elif e == 2 and a % 4 == 1:
    return 1, 3
  elif e == 2 or a % 8 != 1:
    return None
  tpk, ss = 4, {1, 3, 5, 7}
  for k in range(4, e + 1):
    sr = set()
    tpk *= 2
    for r in ss:
      t = ((r * r - a) // tpk) % 2
      rr = r + t * tpk // 2
      sr |= {rr, 2 * tpk - rr}
    ss = sr
  return tuple(sorted(ss))

def hensel_lift(r, a, p, e):
  '''
  Hensel root lifting for powers of odd primes

  Given the root r such that r ** 2 == a mod p, return a tuple
  giving the two roots s such that s ** 2 == a mod (p ** e)

  >>> hensel_lift(24, 56, 13, 2)
  (15, 154)

  >>> hensel_lift(24, 56, 13, 3)
  (522, 1675)
  '''
  for n in range(e - 1):
    r += (a - r * r) * inv(2 * r, p)
  t = p ** e
  return tuple(sorted((r % t, t - r % t)))

# My thanks to Keith Matthews (http://www.numbertheory.org/keith.html)
# for his help with the principles on which this function is based

def sqrt_mod_pn(a, p, n):
  '''
  Square roots mod prime powers - x^2 = a (mod p ** n)

  It returns a tuple (ret) of the form ((r1, r2, ...), e)
  where r1, r2, .. are the roots and e is the exponent of
  the prime p in the modulus, which may be less than n.
  In the latter case the roots for the modulus n can be
  calculated if needed by the expression:

  [x + y for x in ret[0] for y in range(0, p ** n, p ** e)]

  >>> sqrt_mod_pn(1872, 2, 6)
  ((4, 12), 4)
  >>> sqrt_mod_pn(1872, 3, 5)
  ((30, 51), 4)
  >>> sqrt_mod_pn(208, 3, 3)
  ((10, 17), 3)
  '''
  ret = None, None
  if a % p:
    # the easier case when a and p are co-prime
    if p == 2:
      ret = hensel_lift_2(a, n), n
    else:
      r = sqrt_mod_p(a, p)
      if r:
        ret = hensel_lift(r, a, p, n), n
  else:
    if a % (p ** n) == 0:
      # if a is a multiple of p ** n
      ret = (0,), (n + 1) // 2
    else:
      # if gcd(a, p ** n) = p ** (2.m) with 0 < 2.m < n the
      # original congruence x^2 = a (mod p^n) can be put in
      # the form X^2 = A (mod p^(n-2.m)) where X = x // p^m
      # and A = a // p^m  --- if t (mod p^{n - 2.m}) solves
      # this congruence, then x (mod p^{n - m}) will solve
      # original congruence
      aa, m = a, 0
      while aa % p == 0:
        aa, m = aa // p, m + 1
      if m % 2 == 0:
        r, e = sqrt_mod_pn(aa, p, n - m)
        if r:
          ret = tuple(x * p ** (m // 2) for x in r), e + m // 2
  return ret

def sqrt_mod_m(a, m):
  '''
  Modular Square Root for a composite modulus

  return a tuple giving the square roots of a (mod m)

  >>> sqrt_mod_m(67, 462)
  (23, 65, 89, 131, 331, 373, 397, 439)

  >>> sqrt_mod_m(9, 5488)
  (3, 683, 2061, 2741, 2747, 3427, 4805, 5485)
  >>> t = sqrt_mod_m(468, 3888); t[:len(t)//2]
  (66, 258, 390, 582, 714, 906, 1038, 1230, 1362, 1554, 1686, 1878)
  '''
  if not m:
    return 0,

  rm, roots = 1, []
  for p, e in factor(m):
    r, ee = sqrt_mod_pn(a, p, e)
    if r:
      t = p ** ee
      rm *= t
      roots.append([(x, t) for x in r])
    else:
      return ()

  if roots:
    rx = [crt(*zip(*pr)) for pr in product(*roots)]
    return tuple(sorted(x + y for x in rx for y in range(0, m, rm)))
  else:
    return ()

def PQa(p, q, D):
  '''
  The PQa algorithm for computing the continued fraction expansion
  of the quadratic irrational (p + sqrt(d)) / q.  See 'Solving the
  generalised Pell equations x^2 - D.y^2 = N' by John P. Robertson

  >>> next(PQa(0, 1, 11))
  (2, (3, 3, 6), (3, 10, 63), (1, 3, 19), (3, 10, 63), (0, 3, 3), (1, 2, 1))

  print(next(PQa(0, 3, 7)))
  (2, (0, 1, 7, 2), (0, 1, 7, 15), (1, 1, 8, 17), (0, 9, 63, 135), (0, 0, 7, 7), (9, 7, 2, 7))
  '''
  # if p^2 != D mod q, make it so
  t = abs(q)
  if (D - p ** 2) % t:
    p *= t
    q *= t
    D *= t ** 2

  sq = D ** 0.5
  a, A, B, G = ([] for i in range(4))
  a0, a1, b0, b1, g0, g1 = 0, 1, 1, 0, -p, q
  p1, q1, P, Q = p, q, [p], [q]

  period = pe = ps = 0
  while True:

    # compute the next partial quotient
    t = int((p1 + sq) // q1)
    a.append(t)

    # the convergents
    a0, a1 = a1, t * a1 + a0
    b0, b1 = b1, t * b1 + b0
    g0, g1 = g1, t * g1 + g0
    A.append(a1)
    B.append(b1)
    G.append(g1)

    p1 = t * q1 - p1
    q1 = (D - p1 ** 2) // q1
    P.append(p1)
    Q.append(q1)

    if period:
      # we are in a periodic part of the continued fraction
      # check for the start of the next period
      if p1 == pr and q1 == qr:
        # record the end of the period
        pe = len(a)
        # output the values for the completed period
        u = slice(ps, pe)
        yield (period,) + tuple(tuple(x[u]) for x in (a, A, B, G, P, Q))
        # move on to the next period
        ps = pe
      elif ps == 0:
        period += 1
    # check if (P[i] + sqrt(D)) / Q[i] is reduced
    elif (p1 + sq) / q1 > 1 and -1 < (p1 - sq) / q1 < 0:
      # record the first occurrence, which is the start of
      # of the first repeating period
      pr, qr = p1, q1
      period = 1

class Qde(object):
  '''
  A class for solving the quadratic diophantine equation x^2 - D.y^2 = N
  for  (x, y) for  integers D and N with D positive and not square and N
  positive or negative. Solutions fall into a number of classes for each
  of which the minimum non-negative solution (x, y) is computed. Each of
  these solutions give rise to four sub-solutions

    (x, y), (-x, y), (x, -y), (-x, -y)

  Each  solution class (or sub-class) also gives an infinite sequence of
  solutions using the iteration:

    x[n + 1], y[n + 1] = v * x[n] - d * w * y[n], w * x[n] - v * y[n]

  where (v, w) is the solution to the equation x^2 - D.y^2 = 1.

  The following properties are supported:

    iter_parms:    returns the tuple (v, w)
    len(instance): returns the number of solution classes

  The following methods are supported

    qde(d, n, pos_xy):
        create an instance for d and n (this also supports iteration
        giving the (x, y) values for each class of solutions); if
        pos_xy = 1 solutions are returned with x non-negative, if
        pos_xy = 2 solutions are  returned with both x and y non-negative

    qde_instance[i]:
        return (x, y) for the i'th class (0 <= i <= classes - 1)

  The following auxiliary function is provided:

    iterate(xy, limit=0, back=False, first=False)
        iterate a class solution (xy) forward (back = True) or backwards
        (back = False), returning 'limit' values (unlimited if limit = 0),
        returning the initial value as the first if first = True

    >>> t = Qde(7, 261); t.iter_parms, tuple(t)
    ((8, 3), ((17, 2), (18, 3), (31, 10), (38, 13), (81, 30), (94, 35)))

    >>> t = Qde(157, 12); t.iter_parms, tuple(t)
    ((46698728731849, 3726964292220), ((13, 1), (10663, 851), (579160, 46222), (483790960, 38610722), (26277068347, 2097138361), (21950079635497, 1751807067011)))

    >>> t = Qde(167, 173); t.iter_parms, tuple(t)
    ((168, 13), ((29, 2), (530, 41)))

    >>> t = Qde(157, 12); u = tuple(t)[0]; v = next(t.iterate(u)); w = next(t.iterate(v)); u, v, w
    ((13, 1), (1192216867392577, 95149264530709), (111350024159801489452892169733, 8886699386709042671373701881))
  '''

  def __init__(self, d, n, pos_xy=2):
    # d must not be a square
    if round(d ** 0.5) ** 2 == d:
      raise ValueError
    self.d, self.n = d, n
    # find solutions to t^2 - d.u^2 = -1 and v^2 - d.w^2 = 1
    tu = None
    seq = next(PQa(0, 1, d))
    ln = -2 if len(seq[4]) > 1 else -1
    # if the period (seq[0]) is even this solves v^2 - d.w^2 = 1
    vw = seq[4][ln], seq[3][ln]
    if seq[0] % 2:
      # otherwise if solves t^2 - d.u^2 = -1, 'square' this to
      # obtain the solution of v^2 - d.w^2 = 1
      tu, vw = vw, self.__forward(vw, vw)
    else:
      # t^2 - d.u^2 = -1 has no solution
      tu = None

    self.vw = vw
    sol, f2 = set(), 1
    # we need to express abs(n) as f^2.g where g is square-free
    factors = factor(abs(n))
    # compute the product of all primes that contribute to f
    for p, e in factors:
      if e // 2:
        f2 *= p ** (e // 2)

    # for each of the divisors of f
    for f in divisors(f2):
      # solve p^2 - d.q^2 = |n| / f^2
      m = abs(n) // f ** 2

      # compute the modular square roots of d mod m
      for rt in sqrt_mod_m(d, m):

        # compute the first period of the continued fraction
        # expansion of {rt - sqrt(d)} / m
        seq = next(PQa(rt if rt <= m // 2 else rt - m, m, d))
        # find a Q value that is +/- 1
        for i, q in enumerate(seq[6]):
          if i and abs(q) == 1:
            rs = f * seq[4][i - 1], f * seq[3][i - 1]
            tm = rs[0] ** 2 - d * rs[1] ** 2
            # check if we have a solution (convert any solutions to
            # minimum non-negative form)
            if tm == n or tu:
              if tm != n:
                # we have a solution only if t^2 - d.u^2 = -1 does
                rs = self.__forward(rs, tu)
              # here solutions can be stored in minimum non-negative x
              # and y form (with __non_neg) or in minimum non-negative
              # x form (with __min_posx)
              sol.add(self.__minp_xy(rs) if pos_xy - 1 else self.__minp_x(rs))

    self.sol = tuple(sorted(sol))

  def __minp_x(self, xy):
    '''
    Convert a solution into its equivalent minimum
    non-negative x solution
    '''
    v, w = self.vw[0], -self.vw[1]
    x, y = abs(xy[0]), xy[1]
    while True:
      x_min, y_min = x, y
      x, y = x * v + self.d * y * w, x * w + y * v
      if x >= x_min or x < 0:
        break
    return x_min, y_min

  def __minp_xy(self, xy):
    '''
    Convert a solution into its equivalent minimum
    non-negative solution
    '''
    v, w = self.vw[0], -self.vw[1]
    x, y = abs(xy[0]), abs(xy[1])
    while True:
      x_min, y_min = x, y
      x, y = x * v + self.d * y * w, x * w + y * v
      if (x, y) == (x_min, y_min) or x < 0 or y < 0:
        break
    return x_min, y_min

  def __forward(self, xy, vw):
    x, y = xy
    v, w = vw
    return x * v + self.d * y * w, x * w + y * v

  @property
  def iter_parms(self):
    return self.vw

  def __len__(self):
    return len(self.sol)

  def __getitem__(self, i):
    if i < 0:
      i += len(self.sol)
    if 0 <= i < len(self.sol):
      return self.sol[i]
    else:
      raise IndexError

  def __iter__(self):
    for s in self.sol:
      yield s

  def iterate(self, xy, limit=0, back=False, first=False):
    '''
    Iterate a quadratic diophantine solution
    (default is forward)
    '''
    vw = self.vw
    if back:
      vw = vw[0], -vw[1]
    if first:
      yield xy
      i = 1
    else:
      i = 0
    while limit and i < limit or not limit:
      i, xy = i + 1, self.__forward(xy, vw)
      yield xy

def frobenius_number(a):
  '''
  For the integer sequence (a[0], a[1], ...) with a[0] < a[1] < ... < a[n],
  return the largest number, N, that cannot be expressed in the form:
  N = sum(m[i] * x[i]) where all m[i] are non-negative integers.

  >>> frobenius_number((9949, 9967, 9973))
  24812836

  >>> frobenius_number((6, 9, 20))
  43

  >>> frobenius_number((5, 8, 15))
  27

  frobenius_number((5, 8, 9, 12))
  11
  '''
  def __residue_table(a):
    n = [0] + [None] * (a[0] - 1)
    for i in range(1, len(a)):
      d = gcd(a[0], a[i])
      for r in range(d):
        try:
          nn = min(n[q] for q in range(r, a[0], d) if n[q] is not None)
        except ValueError:
          continue
        if nn is not None:
          for c in range(a[0] // d):
            nn += a[i]
            p = nn % a[0]
            nn = min(nn, n[p]) if n[p] is not None else nn
            n[p] = nn
    return n

  return max(__residue_table(sorted(a))) - min(a)

def frobenius_solve(a, m):
  '''
  Given integer sequence (a[0], a[1], ...) with a[0] < a[1] < .. < a[n]
  return the number of ways in which the number m can be expressed as
  m = sum(n[i] * x[i]) where all n[i] are non-negative integers.

  >>> tuple(frobenius_solve((5, 8, 9, 12), 29))
  ((1, 3, 0, 0), (4, 0, 1, 0), (0, 1, 1, 1), (1, 0, 0, 2))

  >>> tuple(frobenius_solve((9949, 9967, 9973), 17560051))
  ((1762, 1, 2),)
  '''
  def __extended_residue_table(a):
    n = [[0] + [None] * (a[0] - 1)]
    for i in range(1, len(a)):
      n.append(n[-1][:])
      d = gcd(a[0], a[i])
      for r in range(d):
        try:
          nn = min(n[-1][q] for q in range(r, a[0], d) if n[-1][q] is not None)
        except ValueError:
          continue
        if nn is not None:
          for c in range(a[0] // d):
            nn += a[i]
            p = nn % a[0]
            nn = min(nn, n[-1][p]) if n[-1][p] is not None else nn
            n[-1][p] = nn
    return n

  def __frobenius_recurse(a, m, ert, c, i):
    if i == 0:
      c[0] = m // a[0]
      yield tuple(c)
    else:
      lc = lcm(a[0], a[i])
      l = lc // a[i]
      for j in range(l):
        c[i] = j
        mm = m - j * a[i]
        r = mm % a[0]
        lb = ert[i - 1][r]
        if lb is not None:
          while mm >= lb:
            yield from __frobenius_recurse(a, mm, ert, c, i - 1)
            mm -= lc
            c[i] += l

  a = sorted(a)
  ert = __extended_residue_table(a)
  c = [0] * len(a)
  yield from __frobenius_recurse(a, m, ert, c, len(a) - 1)

if __name__ == "__main__":

  import doctest
  doctest.testmod(verbose=True)