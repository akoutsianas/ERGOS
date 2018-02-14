def trivial_Tp_infinite_place(bounds, place, Gens, delta):
    r"""

    INPUT:
        - ``bounds`` : a list of upper bounds for the exponents of the generators
        - ``place`` (ring morphism): an infinite place `\mathfrak p` of a number field `K`
        - ``Gens`` : a list `[g_1,g_2,\cdots,g_n]` of elements of `K^*` which are linear independent
        - ``delta`` : a real positive number

    OUTPUT:
        True, if we are able to prove that the inequality `\mid \zeta\displaystyle\prod_{i=1}^{n}g_i^{a_i}-1
        \mid_{\mathfrak p}<\delta` does not have a non-trivial solution( as it is defined in the paragraph
        3.1 of the reference) with `\max(\mid a_i\mid)\leq B` and `\zeta` a root of unity, otherwise False.

    REFERENCE:
        SMART, N. , Determine the small solutions to S-unit equations, Mathematics of Computations 68(228):1687-1699,1999

    EXAMPLE::

        sage: t = polygen(QQ)
        sage: L.<a> = (t^3+45*t+135).splitting_field()
        sage: SL = sum([L.primes_above(p) for p in [2,5,7]],[])
        sage: G = [247/4433463*a^5+2044/4433463*a^4+38657/4433463*a^3+253334/4433463*a^2+175325/1477821*a-61106/492607]
        sage: finite,real,complex = support_of_G(Gl,100)
        sage: R0 = evaluate_R0(88,Gl,finite+real+complex,100)
        sage: R1 = R0^(1/20)
        sage: trivial_Tp_infinite_place(88,complex[0],G,1/R1)
            True
    """
    precision = place.codomain().precision()

    if is_real_place(place):
        if len([1 for g in Gens if place(g).abs() != RR(1)]) == 0:
            return True
        delta_prime = -log(1 - delta)
    else:
        if len([1 for g in Gens if place(g).abs() != RR(1)]) == 0:
            return trivial_Tp_complex_place_not_in_support(bounds,place,Gens,delta)
        delta_prime = -log(1 - sqrt(delta)) / 2
        phi_prime = arcsin(sqrt(delta))

    C = 1
    if is_real_place(place):
        t = len(Gens)
    else:
        t = len(Gens)+1
        g0 = Gens[0].parent().roots_of_unity()[0]
        phi0 = place(g0).argument()
        tor_order = g0.multiplicative_order()

    C_upper = 2 ** 1000  # arbitrary choice
    A = copy(identity_matrix(ZZ, t))

    if precision < log(C) / log(2):
        place = higher_precision(place, 2 * precision)

    finish = False
    while not finish:
        if is_real_place(place):
            y = zero_vector(ZZ, t)
            A[t - 1] = vector([(log(place(g).abs()) * C).round() for g in Gens])
            if A[t - 1, t - 1].is_zero():
                i, x = [[i, a] for i, a in enumerate(A[t - 1]) if not a.is_zero()][0]
                A[t - 1, t - 1] = x
                A[t - 1, i] = 0
                temp = bounds[i]
                bounds[i] = bounds[t - 1]
                bounds[t - 1] = temp
            if not A.is_singular():
                l = minimal_vector(A.transpose(), y)
                if l <= sum([b**2 for b in bounds[:t - 1]]) + (sum(bounds) / place(2) + C * delta_prime) ** 2:
                    C *= 2
                    if precision < log(C) / log(2):
                        precision *= 2
                        place = higher_precision(place, precision)
                        return False
                    if C > C_upper:
                        return False
                else:
                    return True
            else:
                C += 1
        else:
            A[t - 2] = vector([(2 * log(place(g).abs()) * C).round() for g in Gens]+[0])
            A[t - 1] = vector([(place(g).argument() * C).round() for g in Gens] + [(C * 2 * pi).round()])
            if A[t - 2, t - 2].is_zero():
                i, x = [[i, a] for i, a in enumerate(A[t - 2]) if not a.is_zero()][0]
                A[t - 2, t - 2] = x
                A[t - 2, i] = 0
                temp = bounds[i]
                bounds[i] = bounds[t - 2]
                bounds[t - 2] = temp

            if not A.is_singular():
                y = zero_vector(ZZ, t)
                #we deal with all torsion elements at once
                l = minimal_vector(A.transpose(), y)
                for n in range(1,tor_order):
                    y[t-1] = - (C * n * phi0).round()
                    l = min(l,minimal_vector(A.transpose(), y))

                if l <= sum([b**2 for b in bounds[:t-2]]) + (2 * sum([b for b in bounds]) +1 + C* (delta_prime + phi_prime))**2:
                    C *= 2
                    if precision < log(C) / log(2):
                        precision *= 2
                        place = higher_precision(place, precision)
                        return False
                    if C > C_upper:
                        return False
                else:
                    return True
            else:
                C += 1
    return False


def trivial_Tp_complex_place_not_in_support(Bounds,place,Gens,delta):
    r"""

    INPUT:
        - ``Bounds`` : a list of upper bounds for the exponents of the generators
        - ``place`` (ring morphism): an infinite place `\mathfrak p` of a number field `K`
        - ``Gens`` : a list `[g_1,g_2,\cdots,g_n]` of elements of `K^*` which are linear independent
        - ``delta`` : a real positive number

    OUTPUT:
        True, if we are able to prove that the inequality `\mid \zeta\displaystyle\prod_{i=1}^{n}g_i^{a_i}-1
        \mid_{\mathfrak p}<\delta` does not have a non-trivial solution while ``place`` is a complex infinite
         place and is not in the support of ``Gens`` with `\max(\mid a_i\mid)\leq B` and `\zeta` a root of
         unity, otherwise False. We use only the arguments of ``Gens``

    REFERENCE:
        SMART, N. , Determine the small solutions to S-unit equations, Mathematics of Computations 68(228):1687-1699,1999

    """

    phi0 = arcsin(delta)
    C = 1
    C_upper = 2 ** 1000  # arbitrary choice

    A = copy(identity_matrix(ZZ, len(Gens)+1))
    y = zero_vector(ZZ, len(Gens)+1)
    finish = False

    while not finish:
        A[len(Gens)] = vector([(C * place(g).arg()).round() for g in Gens] + [(2*pi*C).round()])
        if not A.is_singular():
            l = minimal_vector(A.transpose(), y)
            if l <= sum([b**2 for b in Bounds]) + (sum(Bounds) + C*phi0)**2:
                C *= 10
                if C > C_upper:
                    return False
            else:
                return True
        else:
            C += 1
    return False


def trivial_Tp_finite_place(B, prime, M0, M, M0_logp, M_logp, delta, precision):
    r"""

    INPUT:
        - ``B`` : an upper bound for the exponents
        - ``prime`` : a prime ideal `\mathfrak p` of a number field `K`
        - ``M0`` : a list of elements in `K^*`
        - ``M`` : a list `[m_1,m_2,\cdots,m_n]` of elements of `K^*` which are linear independent
        - ``delta`` : a real positive number
        - ``precision`` : the precision

    OUTPUT:
         True, if we are able to prove that the inequality `\mid m_0\displaystyle\prod_{i=1}^{n}m_i^{a_i}-1\mid_{\mathfrak p}<\delta`
         does not have a non-trivial solution( as it is defined in the paragraph 3.2 of the reference) with
         `\max(\mid a_i\mid)\leq B` for all `m_0` in ``M0``, otherwise False.

    COMMENT:
        Should hold `\mid m_i\mid_{\mathfrak p}=1` for all `i=0,1,\cdots,n`.

    REFERENCE:
        SMART, N. , Determine the small solutions to S-unit equations, Mathematics of Computations 68(228):1687-1699,1999

    EXAMPLE::

        sage: t = polygen(QQ)
        sage: L.<a> = (t^3-45*t+135).splitting_field()
        sage: R0 = 1.4219031303e69
        sage: R1 = 1.9418581520e17
        sage: prime = L.ideal(7,3734/40719*a^5+10174/17451*a^4-670069/122157*a^3-1069720/122157*a^2+22387486/122157*a-52724345/122157)
        sage: M = [-347/122157*a^5-293/17451*a^4+2451/13573*a^3+29717/122157*a^2-82063/13573*a+1806725/122157,-1510/122157*a^5-458/5817*a^4+89627/122157*a^3+50500/40719*a^2-2974004/122157*a+6910454/122157]
        sage: trivial_Tp_finite_place(88,prime,-1,M,1/R1,40)
            True
    """
    if len([m for m in M + M0 if m.valuation(prime) != 0]) > 0:
        raise ValueError('There is an element without non zero valuation at prime')
    K = prime.ring()
    theta = K.gen()
    e = prime.absolute_ramification_index()
    p = prime.absolute_norm().factor()[0][0]
    f = prime.residue_class_degree()

    delta_prime = -log(delta) / (e * f * log(p))
    if delta_prime < 1:
        return False, M0_logp, M_logp, precision
    M_logp_emb = [embedding_to_Kp(m, prime, precision) for m in M_logp]
    M0_logp_emb = [embedding_to_Kp(m0_logp, prime, precision) for m0_logp in M0_logp]
    n = e * f
    s = len(M)
    u = round((1 + s / n) * log(B) / log(p))

    # nothing changes if we take the valuation of the global field instead of its completion
    ordp_Disc = (K.disc([theta ** i for i in range(K.degree())])).valuation(p)

    c5 = delta_prime - ordp_Disc/2

    for k in range(len(M0_logp_emb)):
        m0_logp_emb = M0_logp_emb[k]
        c6 = min([min([a.valuation(p) for a in v]) for v in M_logp_emb + [m0_logp_emb]])
        c7 = c5 - c6
        lam = p ** c6
        T = [[v[i] / lam for i in range(n)] for v in M_logp_emb]
        T0 = [m0_logp_emb[i] / lam for i in range(n)]

        finish = False
        while not finish:
            if u <= precision:
                if u > c7:
                    return False, M0_logp, M_logp, precision
                A11 = copy(identity_matrix(ZZ, s))
                A12 = copy(zero_matrix(ZZ, s, n))
                A21 = copy(zero_matrix(s, n))
                A22 = p ** u * copy(identity_matrix(ZZ, n))
                y = vector(ZZ, n + s)
                for i in range(s):
                    A21[i] = vector([mod(a, p ** u) for a in T[i]])
                for i in range(n):
                    y[s + i] = -mod(T0[i], p ** u)
                A = block_matrix([[A11, A12], [A21.transpose(), A22]])
                l = minimal_vector(A.transpose(), y)
                if l > s * B ** 2:
                    finish = True
                else:
                    u += 1
            else:
                precision *= 2
                M_logp = [log_p(m, prime, precision) for m in M]
                M_logp_emb = [embedding_to_Kp(m, prime, precision) for m in M_logp]
                M0_logp = [log_p(m0, prime, precision) for m0 in M0]
                M0_logp_emb = [embedding_to_Kp(m0_logp, prime, precision) for m0_logp in M0_logp]
                m0_logp_emb = M0_logp_emb[k]
                c5 = delta_prime - ordp_Disc / 2
                c6 = min([min([a.valuation(p) for a in v]) for v in M_logp_emb + [m0_logp_emb]])
                c7 = c5 - c6
                lam = p ** c6
                T = [[v[i] / lam for i in range(n)] for v in M_logp_emb]
                T0 = [m0_logp_emb[i] / lam for i in range(n)]

    return True, M0_logp, M_logp, precision


def find_sigma(L):
    r"""
    INPUT:
        - ``L`` : a relative `p` degree Galois extension `L/M`, where `p` is a prime number

    OUTPUT:
        An generator `\sigma` of `Gal(L/M)`.

    EXAMPLE::

        sage: M.<a> = QuadraticField(-7)
        sage: t = polygen(M)
        sage: L.<b> = M.extension(t^3 - 15*t - 5*a)
        sage: find_sigma(L)
            Relative number field endomorphism of Number Field in b with defining
            polynomial x^3 - 15*x - 5*a over its base field
              Defn: b |--> -1/3*b^2 + (1/6*a - 1/2)*b + 10/3
                    a |--> a
    """
    if L.relative_degree() not in Primes():
        raise ValueError('The degree of the relative extension is not a prime number.')
    if not L.is_galois_relative():
        raise ValueError('The relative extension is not galois')
    M = L.base_field()
    temp = [s for s in L.embeddings(L) if len([1 for g in M.gens() if s(g) == g]) == len(M.gens())]

    return [s for s in temp if not len([1 for g in L.gens() if s(g) == g]) == len(L.gens())][0]


def find_tau(L):
    r"""

    INPUT:
        ``L``: a relative quadratic extension

    OUTPUT:
        A generator of the Galois group of ``L`` over its base field

    EXAMPLE::

        sage: L.<l1> = QuadraticField(2)
        sage: find_tau(L)
            Ring endomorphism of Number Field in l1 with defining polynomial x^2 - 2
                Defn: l1 |--> -l1
    """

    if L.relative_degree() != 2:
        raise ValueError('L is not a relative quadratic extension')
    K = L.base_field()
    for s in L.automorphisms():
        if len([g for g in L.base_field().gens() if s(g) == g]) == len(L.base_field().gens()):
            if len([g for g in L.gens() if s(g) == g]) != len(L.gens()):
                return s


def final_loop_with_Fincke_Pohst_all_cases(Gl,bound_Gl,R,Sm,proof = True):
    r"""


    """

    infinite_primes = sum(support_of_G(Gl,200)[1:],[])
    A = matrix(RR,[[log((s(g)).abs()) if is_real_place(s) else 2*log((s(g)).abs()) for g in Gl[1:]] for s in infinite_primes])
    A /= log(R)
    # print 'A',A
    # return 1
    V0 = pari(A.transpose() * A).qfminim(len(infinite_primes), flag=2).python()[2].columns()

    print 'len(V0)',len(V0)
    torsion = [g**e for e in range(Gl[0].multiplicative_order()/2)]
    solutions = []
    Smunit_group = Gl[0].parent().S_unit_group(proof,S=Sm)
    vec = vector(bound_Gl[1:])
    for v0 in V0:
        if len([1 for a,b in zip(v0,vec) if a.abs()>b]) == 0:
            l1 = prod([g**e for g,e in zip(Gl[1:],v0)])
            for l0 in torsion:
                if is_S_unit_element(Smunit_group, 1 - l1*l0):
                   solutions.append(l0*l1)
    return solutions


def bounds_for_exponents_from_bounds_of_absolute_values(G, primes, primes_bounds, places, places_bounds):
    r"""

    INPUT:
        - ``G`` : a list of generators of a finitely generated subgroup of `K^*`
        - ``primes`` : a list of primes which lie in the support of ``G``
        - ``primes_bounds`` : a list of upper bounds of `|\log (|g|_{\frak p})|` for the primes in ``primes``
        - ``places`` : a list of infinite places in the support of ``G``
        - ``places_bounds`` : a list of upper bounds of `|\log (|g|_{\frak p})|` for the places in ``places``

    OUTPUT:
        A list with new upper bounds for the absolute value of the exponents of the generators ``G``

    EXAMPLE::

        sage:
    """

    precision = places[0].codomain().precision()
    A = zero_matrix(RealField(precision),len(primes)+len(places),len(G))

    for i,prime in enumerate(primes):
        fp = prime.residue_class_degree()
        p = prime.smallest_integer()
        A[i] = [(fp * g.valuation(prime) * log(p)).abs() for g in G]
    i = len(primes)-1
    for p in places:
        i += 1
        if is_real_place(p):
            A[i] = [log(p(g).abs()).abs() for g in G]
        else:
            A[i] = [2*log(p(g).abs()).abs() for g in G]

    # we find the new exponents and return a list with the new exponents
    # if X is empty we use simply inequalities to reduce the bound


    X = Set(range(A.dimensions()[0])).subsets(len(G)).list()
    # print X
    bounds = vector(primes_bounds+places_bounds)
    exp_bounds = len(G)*[+Infinity]
    for g in X:
        M = A[g.list(), :]
        vM = vector([bounds[i] for i in g])
        if M.rank() == len(G):
            Minv_abs = M.inverse().apply_map(abs)
            new_exp = [RR(a).floor() for a in Minv_abs * vM]

            exp_bounds = [min(a,b) for a,b in zip(exp_bounds,new_exp)]
    return exp_bounds


def bounds_for_exponents_from_bounds_for_primes(G, primes, primes_bounds, exp_bounds):
    r"""

    INPUT:
        - ``G`` : a list of generators of a finitely generated subgroup of `K^*`
        - ``primes`` : a list of primes which lie in the support of ``G``
        - ``primes_bounds`` : a list of upper bounds for the absolute value of the valuation of the elements of ``G`` with respect to each prime in ``P``
        - ``exp_bounds`` : a list of initial bounds for the generators

    OUTPUT:
        A list with new upper bounds for the absolute value of the exponents of the generators ``G`` taking into account ``BP``

    EXAMPLE::

        sage:
    """

    # we find for which generators the exponents will change
    GS = [g for g in G if len([1 for p in primes if g.valuation(p) != 0]) > 0]
    GSenu = [G.index(g) for g in GS]
    A = matrix(ZZ, len(primes), [[g.valuation(p) for g in GS] for p in primes])


    # we find the new exponents and return a list with the new exponents
    # if X is empty we use simply inequalities to reduce the bound

    X = Set(range(A.dimensions()[0])).subsets(len(GS)).list()

    if X == []:
        return exp_bounds

    # if X is not empty we use a submatrix of A

    new_exponents = copy(exp_bounds)
    min_exp_bounds = +Infinity
    for g in X:
        M = A[g.list(), :]
        if M.rank() == len(GS):
            Minv_abs = M.inverse().apply_map(abs)
            x = matrix(primes_bounds)[:, g.list()]
            x = x.transpose()
            v = (Minv_abs * x).apply_map(floor)
            for i in range(len(exp_bounds)):
                if i in GSenu:
                    exp_bounds[i] = min(v[GSenu.index(i)][0], exp_bounds[i])
            if sum(exp_bounds) < min_exp_bounds:
                new_exponents = exp_bounds
    return new_exponents


def relative_discriminant_element(K):
    """

    INPUT:
        - ``K``: a number field

    OUTPUT:
    The relative discriminant as an element its base field.
    """

    base = K.base_field()
    nf = base.pari_nf()
    return base(nf.rnfdisc(K.pari_relative_polynomial())[1])
##Quadratic case


def choice_of_delta(place, G, bounds):
    r"""

    INPUT:
        - ``place`` (ring morphism) : an inifinite prime of a number field `K`
        - ``G`` : a list of generators of a multiplicative subgroup of `K^*`
        - ``bounds`` : a list of upper bounds for each generator

    OUTPUT:
        The value of the expression `e^{-\mid\Sum_ib_i\mid\log\mid g_i\mid_{\mathfrak p}\mid}` for `g_i` and `b_i` in ``G``
        and ``bounds`` respectively.

    EXAMPLE::

        sage
    """

    # return exp(-sum([(log(place(g).abs())).abs() * b for g,b in zip(G,bounds) if place(g).abs() != 1]))
    return exp(-sum([(log(place(g).abs())).abs() * b for g, b in zip(G, bounds) if
                     g.is_integral() and g.absolute_norm().abs() == 1]))


def reduce_bound_for_unit_generators_C2(Gl, Gm, bound_Gl, bound_Gm, R):
    r"""

    INPUT:
        - ``Gl`` : a list of generators of the group where `\lambda` lies
        - ``Gm`` : a list of generators of the group where `\mu` lies
        - ``bound_Gl`` : a list of upper bounds for each generator of ``Gl``
        - ``bound_Gm`` : a list of upper bounds for each generator of ``Gm``
        - ``R`` : a real number greater than `1`

    OUTPUT:
        A list of upper bounds for each generator such that the bounds are smaller for the generators which are units

    COMMENT:
        We use Smart's ideas to prove that the inequality `\mid\mu -1\mid_{\mathfrak p}\leq\delta` has not nontrivial
        solutions for `\mathfrak p` be an infinite prime

    EXAMPLE::

        sage:

    """
    L = Gl[0].parent()
    infinite_primes = sum(support_of_G(Gl, 200)[1:], [])

    # we find which generators are units
    units_index = [i for i, g in enumerate(Gl) if
                   g.is_integral() and g.absolute_norm().abs() == 1 and g.multiplicative_order() == Infinity]
    Glunit = [g for i, g in enumerate(Gl) if i in units_index]
    if Glunit == []:
        return bound_Gl, R
    c1_inf = c_constants(Glunit, 200)[0]

    # we are going to reduce the bound for units using Smart's ideas

    Bold = max([b for i, b in enumerate(bound_Gl) if i in units_index])

    # we find logRlprime
    c2_inf = max([sum(
            [b * log(p(g).abs()).abs() for b, g in zip(bound_Gl, Gl) if g not in Glunit]) if is_real_place(p) else sum(
            [2 * b * log(p(g).abs()).abs() for b, g in zip(bound_Gl, Gl) if g not in Glunit]) for p in infinite_primes])

    # we make an arbitrary choice of an initial delta
    delta_old = 1 / R
    delta_new = sqrt(delta_old)

    # we reduce the bounds for the units
    reduce_bounds = bound_Gl

    while True:
        if len([1 for place in infinite_primes if
                trivial_Tp_infinite_place(bound_Gm[1:], place, Gm[1:], delta_new)]) == len(infinite_primes):
            Bold = min((c1_inf * log(delta_new).abs() + c1_inf * c2_inf).floor(), Bold)
            delta_old = delta_new
            delta_new = sqrt(delta_old)
            reduce_bounds = [min(b, Bold) if i in units_index else b for i, b in enumerate(bound_Gl)]
        else:
            return reduce_bounds, 1 / delta_old ** 2


def sieve_in_C2(Gl, Gm, B):
    r"""

    INPUT:
        - ``Gl`` : a list of generators of the group where `\lambda` lies
        - ``Gm`` : a list of generators of the group where `\mu` lies
        - ``B`` : an upper bound for the absolute value of the exponents of the solutions

    OUTPUT:
        A listof `\lambda` of the solutions of the `S`-unit equation `\lambda +\mu = 1` up to the action of `S_3` whose
        absolute value of the exponents is less than ``B``.

    EXAMPLE::

        sage:
    """
    if Gl == [] or Gm == []:
        raise ValueError('Either Gl or Gm is empty')

    L = Gl[0].parent()
    tau = find_tau(L)
    Sl = support_of_G(Gl, 40)[0]
    Sm = support_of_G(Gm, 40)[0]
    SmnotSl = [p for p in Sm if p not in Sl]
    infinite_primes = L.places(prec=200)

    # we make lists of upper bounds for each generator
    bound_Gl = [Gl[0].multiplicative_order()] + [B] * (len(Gl) - 1)
    bound_Gm = [Gm[0].multiplicative_order()] + [B] * (len(Gm) - 1)

    Sunits = []
    Smunit_group = L.S_unit_group(S=Sm)

    #the case Gl has at most one generator of the free part

    if len(Gl) == 1:
        for i in range(bound_Gl[0]):
            l = Gl[0]**i
            if is_S_unit_element(Smunit_group, 1 - l):
                if l not in Sunits:
                    Sunits.append(l)
        return Sunits

    if len(Gl) == 2:
        for v in cartesian_product_iterator([xrange(bound_Gl[0]), xrange(-bound_Gl[1], bound_Gl[1] + 1)]):
            l = prod([g ** e for g, e in zip(Gl, v)])
            if is_S_unit_element(Smunit_group, 1 - l):
                if l not in Sunits:
                    Sunits.append(l)
        return Sunits
    print 'bound_Gl-1', bound_Gl
    print 'bound_Gm-1', bound_Gm

    # we pick only one of the two split primes
    Slreduce = []
    for p in Sl:
        if (not p in Slreduce) and not (tau(p) in Slreduce):
            Slreduce.append(p)

    # for each prime in Slreduce we get a reduced upper bound for the valuation of lambda using Smart's idea

    bound_Slreduce = []
    for p in Slreduce:
        bound_Slreduce.append(reduce_the_bound_for_p_in_support_of_Gl(p, Gm, B))

    # we get new upper bounds for the exponents

    bound_Sm = [0] * len(Sm)
    for i, p in enumerate(Sm):
        if p in Slreduce:
            bound_Sm[i] = bound_Slreduce[Slreduce.index(p)]
        elif tau(p) in Slreduce:
            bound_Sm[i] = bound_Slreduce[Slreduce.index(tau(p))]
        else:
            bound_Sm[i] = reduce_the_bound_for_p_in_support_of_Gl(p, Gl, B)

    bound_Gl = bounds_for_exponents_from_bounds_for_primes(Gl, Slreduce, bound_Slreduce, bound_Gl)
    bound_Gm = bounds_for_exponents_from_bounds_for_primes(Gm, Sm, bound_Sm, bound_Gm)
    print 'bound_Gl-2', bound_Gl
    print 'bound_Gm-2', bound_Gm

    R = max([exp(sum([(log(s(g).abs())).abs() * b if is_real_place(s) else (2 * log(s(g).abs())).abs() * b for g, b in
                      zip(Gl, bound_Gl)])) for s in infinite_primes])

    bound_Gl, R = reduce_bound_for_unit_generators_C2(Gl, Gm, bound_Gl, bound_Gm, R)

    print 'bound_Gl-3', bound_Gl
    print 'bound_Gm-3', bound_Gm

    Sunits = []

    #In case the number of generators of the free part is two then we do a simple loop

    if len(Gl) == 3:
        for v in cartesian_product_iterator([xrange(bound_Gl[0]), xrange(-bound_Gl[1], bound_Gl[1] + 1)]):
            l = prod([g ** e for g, e in zip(Gl, v)])
            if is_S_unit_element(Smunit_group, 1 - l):
                if l not in Sunits:
                    Sunits.append(l)

    #we find solutions which are divisible by suitable high powers of prime ideals

    for p,b in zip(Slreduce,bound_Slreduce):
        solutions, prime_exp = solutions_with_high_valuation_at_p_C2(Gl,bound_Gl,p,b,Sm)
        Sunits += solutions
        bound_Slreduce[Slreduce.index(p)] = prime_exp
        bound_Sm[Sm.index(p)] = prime_exp
        bound_Sm[Sm.index(tau(p))] = prime_exp


    bound_Gl = bounds_for_exponents_from_bounds_for_primes(Gl, Slreduce, bound_Slreduce, bound_Gl)
    bound_Gm = bounds_for_exponents_from_bounds_for_primes(Gm, Sm, bound_Sm, bound_Gm)

    print 'bound_Gl-4', bound_Gl
    print 'bound_Gm-4', bound_Gm

    bound_Gl, R = reduce_bound_for_unit_generators_C2(Gl, Gm, bound_Gl, bound_Gm, R)

    print 'bound_Gl-5', bound_Gl
    print 'bound_Gm-5', bound_Gm

    if len(Gl) == 3:
        Sunits = []
        for v in cartesian_product_iterator([xrange(bound_Gl[0]), xrange(bound_Gl[1] + 1),xrange(-bound_Gl[2],bound_Gl[2]+1)]):
            l = prod([g ** e for g, e in zip(Gl, v)])
            if is_S_unit_element(Smunit_group, 1 - l):
                if l not in Sunits:
                    Sunits.append(l)
        return Sunits

    # Since we have reduced as much as we can, we find solutions using Fincke-Pohst algorithm
    else:
        Sunits = final_loop_with_Fincke_Pohst_all_cases(Gl,bound_Gl,R,Sm,proof)


    # we throw away 0 and 1

    while 0 in Sunits:
        Sunits.remove(0)
    while 1 in Sunits:
        Sunits.remove(1)

    return Sunits


def solutions_with_high_valuation_at_p_C2(Gl,bound_Gl,prime,bound_prime,Sm):
    """

    INPUT:
        - ``Gl`` : a list of generators of the group where `\lambda` lies
        - ``bound_Gl`` : a list of upper bounds for each generator of ``Gl``
        - ``prime`` : a prime ideal in the support of ``Gl``
        - ``bound_prime`` : a upper bound of the absolute value of the valuation of solutions at ``prime``

    OUTPUT:

    A list of `\lambda` which satisfy the proposition 6.17 of the reference and a suitable choice of e.

    REFERENCE:
        Angelos Koutsianas, Applications of S-unit Equations to the Arithmetic of Elliptic Curves,
        PhD thesis, University of Warwick, 2016.
    """

    solutions1, exp1 = solutions_with_high_valuation_at_p_C2_case_1(Gl,bound_Gl,prime,bound_prime,Sm)
    solutions2, exp2 = solutions_with_high_valuation_at_p_C2_case_2(Gl,bound_Gl,prime,bound_prime,Sm)

    return solutions1+solutions2,max(exp1,exp2)


def solutions_with_high_valuation_at_p_C2_case_1(Gl,bound_Gl,prime,bound_prime,Sm):
    """

    INPUT:
        - ``Gl`` : a list of generators of the group where `\lambda` lies
        - ``bound_Gl`` : a list of upper bounds for each generator of ``Gl``
        - ``prime`` : a prime ideal in the support of ``Gl``
        - ``bound_prime`` : a upper bound of the absolute value of the valuation of solutions at ``prime``
        - ``Sm`` : a list of all primes of ``Gm``

    OUTPUT:

    A list of `\lambda` which satisfy the first congruence equation of proposition 6.17 of
    the reference and a suitable choice of e.

    REFERENCE:
        Angelos Koutsianas, Applications of S-unit Equations to the Arithmetic of Elliptic Curves,
        PhD thesis, University of Warwick, 2016.
    """

    #we find a new basis of Gl such that each generator is not divisible by prime
    new_Gl0, new_Gl, k = a_basis_with_0_order_at_p(prime, Gl)
    new_bounds = [b for i, b in enumerate(bound_Gl) if i != k]


    #we make an arbitrary choice of the bound of the prime

    prime_exp = 2
    I = prime ** 2
    while I.idealstar().order() == 1 and prime_exp < bound_prime:
        prime_exp += 1
        I *= prime
    while I.idealstar().exponent() < max(bound_Gl)/4 and prime_exp < bound_prime:
        prime_exp += 1
        I *= prime

    if (I/prime).idealstar().exponent() != 1:
        prime_exp -=1
        I /= prime

    if prime_exp > bound_prime:
        return [], bound_prime

    #we find which elements satisfy the congruence relation
    OI = I.idealstar()
    OI_gens_orders = OI.gens_orders()
    M = matrix(ZZ,[I.ideallog(g) for g in new_Gl])
    SunitL = prime.ring().S_unit_group(S = Sm)
    solutions = []

    #we find solutions with respect to each element in new_Gl0
    for g0 in new_Gl0:

        #we find congruence solutions
        M0 = matrix(ZZ,I.ideallog(g0)).list()
        L0 = []
        for v in cartesian_product_iterator([xrange(OI.exponent())]*len(new_Gl)):
            if len([1 for v0,m0,e0 in zip(vector(v)*M,M0,OI_gens_orders) if (v0+m0)%ZZ(e0) != 0]) == 0:
                L0.append(g0*prod([g**ei for g,ei in zip(new_Gl,v)]))

        #we lift congruence solutions
        new_Gl_powers = [g**OI.exponent() for g in new_Gl]
        L1 = []
        B = [(b/OI.exponent()).floor()+1 for b in new_bounds]
        for v in cartesian_product_iterator([xrange(-b,b+1) for b in B]):
            L1.append(prod([g**ei for g,ei in zip(new_Gl_powers,v)]))
        for l0 in L0:
            for l1 in L1:
                if is_S_unit_element(SunitL, 1 - l1*l0):
                    solutions.append(l0*l1)

    return solutions,prime_exp


def solutions_with_high_valuation_at_p_C2_case_2(Gl,bound_Gl,prime,bound_prime,Sm):
    """

    INPUT:
        - ``Gl`` : a list of generators of the group where `\lambda` lies
        - ``bound_Gl`` : a list of upper bounds for each generator of ``Gl``
        - ``p`` : a prime ideal in the support of ``Gl``
        - ``bound_prime`` : a upper bound of the absolute value of the valuation of solutions at ``prime``
        - ``Sm`` : a list of all primes of ``Gm``

    OUTPUT:

    A list of `\lambda` which satisfy the second congruence equation of proposition 6.17 of
    the reference and a suitable choice of e.

    REFERENCE:
        Angelos Koutsianas, Applications of S-unit Equations to the Arithmetic of Elliptic Curves,
        PhD thesis, University of Warwick, 2016.
    """

    #we make an arbitrary choice of the bound of the prime

    prime_exp = 2
    I = prime ** 2
    while I.idealstar().order() == 1 and prime_exp < bound_prime:
        prime_exp += 1
        I *= prime
    while I.idealstar().exponent() < max(bound_Gl)/4 and prime_exp < bound_prime:
        prime_exp += 1
        I *= prime

    if (I/prime).idealstar().exponent() != 1:
        prime_exp -=1
        I /= prime

    if prime_exp > bound_prime:
        return [], bound_prime

    #we divide the generators in two groups, the ones that are divisible by prime and the rest

    #we do not include the generator of the torsion part in G_zero_val
    G_zero_val = [g for g in Gl if g.valuation(prime) == 0][1:]
    bound_G_zero_val = [b for g,b in zip(Gl,bound_Gl) if g in G_zero_val]

    G_non_zero_val = [g for g in Gl if g.valuation(prime) != 0 or g.multiplicative_order() != Infinity]
    bound_G_non_zero_val = [b for g,b in zip(Gl,bound_Gl) if g in G_non_zero_val]

    #we find the elements in Gl that have negative valuation less that -prime_exp

    v0 = vector([g.valuation(prime) for g in G_non_zero_val])
    L0 = []
    for v in cartesian_product_iterator([xrange(bound_G_non_zero_val[0])]+[xrange(-b,b+1) for b in bound_G_non_zero_val[1:]]):
        if vector(v)*v0 <= -prime_exp:
            L0.append(prod([g**e for g,e in zip(G_non_zero_val,v)]))

    #we find the congruence solutions
    OI = I.idealstar()
    Lcongruence = []
    for l0 in L0:
        for v in cartesian_product_iterator([xrange(OI.exponent())]*len(G_zero_val)):
            l1 = prod([g**e for g,e in zip(G_zero_val,v)])
            t = (l0*l1)/(l0*l1-1)
            if vector(I.ideallog(t)).is_zero():
                Lcongruence.append(l0*l1)

    #we are going to lift the solutions
    G_zero_val_powers = [g**OI.exponent() for g in G_zero_val]
    B = [(b/OI.exponent()).floor()+1 for b in bound_G_zero_val]
    Lpower = []
    for v in cartesian_product_iterator([xrange(-b,b+1) for b in B]):
            Lpower.append(prod([g**ei for g,ei in zip(G_zero_val_powers,v)]))

    SunitL = prime.ring().S_unit_group(S = Sm)
    solutions = []
    for l0 in Lcongruence:
        for l1 in Lpower:
            if is_S_unit_element(SunitL, 1 - l1*l0):
                solutions.append(l0*l1)

    return solutions,prime_exp


def sieve_for_p_not_in_support_of_Gl_C2(p, Gl, SL, bounds):
    r"""

    INPUT:
        - ``p`` : an ideal of a number field `K`
        - ``Gl`` : a list of generators of a subgroup of `K^*`
        - ``SL`` : a list of finite
        - ``bounds`` : a list of upper bounds for the exponents of the solutions

    OUTPUT:
        All `\lambda` of solutions of the S-unit equation `\lambda+\mu=1` such that `p` divides
        `\mu` and `p` is not in the support of ``Gl``.

    EXAMPLE::

        sage: L = QuadraticField(17,'b')
        sage: b = L.gen()
        sage: Gl = [L(-1), -8*b + 33, -3/4*b + 13/4]
        sage: p = [L.ideal(-1/2*b + 3/2),L.ideal(-1/2*b - 3/2),L.ideal(-b)]
        sage: sieve_for_p_not_in_support_of_Gl(SL[2]^2,Gl,SL,398)
            [7/16*b + 33/16, -1/8*b + 9/8, 1/8*b - 9/8, -5/4*b + 21/4, -8*b + 33, 8*b - 33, -9/32*b + 49/32,
             528*b + 2177, -23/256*b + 273/256, -528*b + 2177, 9/32*b + 49/32, 8*b + 33, -8*b - 33, 5/4*b + 21/4,
             1/8*b + 9/8, -1/8*b - 9/8, -7/16*b + 33/16, -1207/64*b + 4977/64, 23/256*b + 273/256, -3/4*b - 13/4,
             -1, 3/4*b - 13/4, 1207/64*b + 4977/64]
    """
    if Gl == []:
        raise ValueError('Gl is empty')
    L = Gl[0].parent()
    Glfree = [g for g in Gl if g.multiplicative_order() == Infinity]
    g0 = [g for g in Gl if g.multiplicative_order() != Infinity][0]
    SunitL = L.S_unit_group(S=SL)

    # we create the congruence relations for the exponents with respect to the ideal p**n
    orders = p.idealstar().gens_orders()
    M = matrix(ZZ, len(Gl), len(orders), [p.ideallog(g) for g in Gl])

    # we divide the congruence relations with the gcd of the coefficients
    GCD = [gcd(list(col) + [m]) for col, m in zip(M.columns(), orders)]
    # print 'GCD=',GCD
    C = matrix(ZZ, [col / g for col, g in zip(M.columns(), GCD)]).transpose()
    # print 'C',C
    prime_orders = [c / g for c, g in zip(orders, GCD)]
    maxorder = max(prime_orders)
    # print 'prime_orders',prime_orders

    # we need a bound for the exponents of the solutions mod p**n
    congruence_bounds = [xrange(bounds[0])] + [xrange(maxorder) if 2 * b >= maxorder else xrange(-b, b) for b in
                                               bounds[1:]]
    Bpr = [0 if 2 * b >= maxorder else 1 for b in bounds[1:]]
    # print 'congruence_bounds',congruence_bounds

    # we determine the solutions module p
    count = 0
    elements = []
    for v in cartesian_product_iterator(congruence_bounds):
        v = vector(v)
        if vector([(v * col) % m for m, col in zip(prime_orders, M.columns())]).is_zero():
            elements.append(prod([g ** e for g, e in zip(Gl, v)]))
            count += 1
    # print 'count',count
    # print 'percent',(count/prod(congruence_bound)).n(21)

    # we determine the global solutions

    Sunits = []
    B = [QQ(b / len(c)).floor() + 1 if len(c) != 0 else 1 for b, c in zip(bounds[1:], congruence_bounds[1:])]
    # print 'B',B
    Gl_exp = [g ** len(c) if b == 0 else 1 for g, c, b in zip(Gl[1:], congruence_bounds[1:], Bpr)]
    count = 0
    for v in cartesian_product_iterator([xrange(-b, b) if i == 0 else xrange(1) for b, i in zip(B, Bpr)]):
        # print 'v',v
        l = prod([g ** e for g, e in zip(Gl_exp, v)])
        # print 'case',count
        count += 1
        for i, g in enumerate(elements):
            # print 'i',i
            mu = 1 - l * g
            if is_S_unit_element(SunitL, mu):
                if (1 - mu) not in Sunits:
                    Sunits.append(1 - mu)
    # print 'percent',(count/(g0.multiplicative_order()*congruence_bound**len(Glfree))).n(21)
    return Sunits


def reduce_the_bound_for_p_in_support_of_Gl(prime, Gm, B):
    r"""

    INPUT:
        - ``prime`` : a prime ideal which lies in the support of `G_\lambda`
        - ``Gm`` : a list of generators of the group ``G_\mu``
        - ``B`` : an upper bound for the exponents of the solutions `\lambda ,\mu`

    OUTPUT:
        A reduced upper bound for the valuation of `\lambda` at the prime ideal ``prime``.

    COMMENT:
        We use Smart's ideas to prove that the inequality `\mid\mu -1\mid_{\mathfrak p}\leq\delta` has not nontrivial
        solutions.

    EXAMPLE::

        sage:

    """

    print 'reduce_the_bound_for_p_in_supp'
    Blow = 1
    Bupp = B
    Bmid = RR((Blow + Bupp) / 2).floor()

    L = prime.ring()
    Labs = L.absolute_field('a')
    eLLabs = L.embeddings(Labs)[0]
    prime_abs = eLLabs(prime)
    Gm_abs = [eLLabs(g) for g in Gm]
    p = prime_abs.absolute_norm().factor()[0][0]
    f = prime_abs.residue_class_degree()
    precision = 200

    # we evaluate the new basis of Gm of elements with zero valuation at prime and their p-adic logarithms
    new_Gm0_abs, new_Gm_abs, k = a_basis_with_0_order_at_p(prime_abs, Gm_abs)
    new_Gm_abs_logp = [log_p(m, prime_abs, precision) for m in new_Gm_abs]
    new_Gm0_abs_logp = [log_p(m0, prime_abs, precision) for m0 in new_Gm0_abs]

    while Bupp - Blow > 1:
        trivial, new_Gm0_abs_logp, new_Gm_abs_logp, precision = trivial_Tp_finite_place(B, prime_abs, new_Gm0_abs,
                                                                                        new_Gm_abs, new_Gm0_abs_logp,
                                                                                        new_Gm_abs_logp,
                                                                                        p ** (-Bmid * f), precision)
        if trivial:
            Bupp = Bmid
        else:
            Blow = Bmid
        Bmid = (QQ((Blow + Bupp) / 2)).floor()
    return Bupp


def elliptic_curves_with_good_reduction_with_a_rational_Weierstrass_point(K, S, proof = True):
    r"""

    INPUT:
        - ``K`` : a number field
        - ``SK`` : a list of prime ideal of ``K``

    OUTPUT:
        All curves with good reduction outside ``SK`` and at least one rational order 2 point

    EXAMPLE::

        sage:
    """
    import time

    if K == QQ:
        K = NumberField(x - 1, 'a')
        SK = [K.prime_above(p) for p in S]
    else:
        SK = S

    # we through away the canditate 2-division fields whose relative discriminant does not have even valuation at
    # the primes above 2 which are not in SK


    primes_above_2_not_in_SK = [p2 for p2 in K.primes_above(2) if p2 not in SK]
    if len(primes_above_2_not_in_SK) > 0:
        quadratic_fields = []
        for M in quadratic_extensions(K, SK + primes_above_2_not_in_SK):
            if len([1 for p in primes_above_2_not_in_SK if M.relative_discriminant().valuation(p) % 2 != 0]) == 0:
                quadratic_fields.append(M)
    else:
        quadratic_fields = quadratic_extensions(K, SK)

    for p in K.primes_above(2):
        if p not in SK:
            SK.append(p)

    # using Hilbert symbol we choose with which fields we are going to work with

    A = copy(zero_matrix(ZZ, len(quadratic_fields)))
    B = [0] * len(quadratic_fields)
    D = [K(1)]
    for i in range(len(quadratic_fields)):
        d1 = relative_discriminant_element(quadratic_fields[i])
        D.append(d1)
        for j in range(i, len(quadratic_fields)):
            d2 = relative_discriminant_element(quadratic_fields[j])
            A[i, j] = (K.hilbert_symbol(d1, d2) + 1) / 2
            if A[i, j] == 1:
                if i != j:
                    B[i] += 1
                    B[j] += 1
                else:
                    B[i] += 1

    # The case of two isogenous curves without full 2-torsion

    final_fields = []

    for i in range(len(quadratic_fields)):
        if A[i, i] != 0:
            final_fields.append(quadratic_fields[i])
            D.remove(relative_discriminant_element(quadratic_fields[i]))
            for j in range(i, len(quadratic_fields)):
                if A[i, j] == 1:
                    if i != j:
                        B[i] -= 1
                        B[j] -= 1
                        A[i, j] = 0
                    else:
                        B[i] -= 1
                        A[i, i] = 0
            for j in range(i):
                if A[j, i] == 1:
                    if i != j:
                        B[i] -= 1
                        B[j] -= 1
                        A[j, i] = 0
                    else:
                        B[i] -= 1
                        A[i, i] = 0

    # The rest cases

    while not A.is_zero():
        m = max([b for b in B])
        if m != 0:
            maxedges = B.index(m)
            final_fields.append(quadratic_fields[maxedges])
            D.remove(relative_discriminant_element(quadratic_fields[maxedges]))
            for j in range(maxedges, len(quadratic_fields)):
                if A[maxedges, j] == 1:
                    if maxedges != j:
                        B[maxedges] -= 1
                        B[j] -= 1
                        A[maxedges, j] = 0
                    else:
                        B[maxedges] -= 1
                        A[maxedges, maxedges] = 0
            for j in range(maxedges):
                if A[j, maxedges] == 1:
                    if maxedges != j:
                        B[maxedges] -= 1
                        B[j] -= 1
                        A[j, maxedges] = 0
                    else:
                        B[maxedges] -= 1
                        A[maxedges, maxedges] = 0

    #we check if we have to solve more S-unit equation

    for d1 in D:
        for d2 in D:
            for d3 in D:
                if (-d1*d2*d3).is_square() and K.hilbert_symbol(d1,d2)==1 and K.hilbert_symbol(d1,d3)==1 and K.hilbert_symbol(d1,d3)==1:
                    if d1 != 1:
                        M = [L for L in quadratic_fields if relative_discriminant_element(L) == d1][0]
                        if M not in final_fields:
                            final_fields.append(M)
                    if d2 != 1:
                        M = [L for L in quadratic_fields if relative_discriminant_element(L) == d2][0]
                        if M not in final_fields:
                            final_fields.append(M)
                    if d3 != 1:
                        M = [L for L in quadratic_fields if relative_discriminant_element(L) == d3][0]
                        if M not in final_fields:
                            final_fields.append(M)

    J = []
    for L in final_fields:
        print 'L',L
        SL = sum([L.primes_above(p) for p in SK],[])
        Gl,Gm = Norm_subgroup_division_field(SK, SL,proof = proof)
        print 'Gl',len(Gl)-1
        bound = reduce_the_bound(L, Gl, Gm, 200)
        print 'bound',bound
        for l in sieve_in_C2(Gl, Gm, bound):
            j = j_invariant(l)
            if j.absolute_minpoly().degree() <= K.absolute_degree():
                j = j[0]
                if j not in J:
                    J.append(j)

    print 'J',J
    return J
    J = [K(j) for j in J if j in K]
    Jfinal = []
    for j in J:
        if j not in Jfinal:
            Jfinal.append(j)

    if K.absolute_degree() == 1:
        Jfinal = [QQ(j) for j in Jfinal]
        curves = egros_from_jlist_over_K(Jfinal,QQ,[p for p in S])
    else:
        curves = egros_from_jlist_over_K(Jfinal,K,S)
    curves_final = curves

    for E1 in curves:
        for E in [iso.codomain() for iso in E1.isogenies_prime_degree(2)]:
            if E.torsion_order()%2 == 0:
                if len([1 for E2 in curves_final if E.is_isomorphic(E2)]) == 0:
                    curves_final.append(E)

    return curves_final


##Cubic case


def find_reduce_S_C3(G):
    r"""

    INPUT:
        - ``G`` : a list of generators for a multiplicative group when we work with the `C_3` case.

    OUTPUT:
        A list of prime ideals in the support of ``G`` such that contains two out of the three primes above a prime in
        the base field such that the sum of the valuation of the generators in the third prime is equal to the opposite
        of the sum of the valuations of the generators with respect to the other two primes.

    EXAMPLE::

        sage:
    """
    L = G[0].parent()
    sigma = find_sigma(L)
    S = support_of_G(G, 20)[0]
    reduce_S = []
    while S != []:
        p1 = S[0]
        p2 = sigma(p1)
        p3 = sigma(p2)
        sum1, sum2, sum3 = [sum([g.valuation(p) for g in G]) for p in [p1, p2, p3]]
        if sum1 == sum2:
            reduce_S.append(p1)
        elif sum1 == sum3:
            reduce_S.append(p3)
        else:
            reduce_S.append(p2)
        S.remove(p1)
        S.remove(p2)
        S.remove(p3)
    return reduce_S


def reduce_bound_for_unit_generators_C3(Gl, bounds, R):
    r"""

    INPUT:
        - ``Gl`` : a list of generators of the group
        - ``bounds`` : a list of upper bounds for each generator
        - ``R`` : a real number such that `\mid\log\mid\mu\mid_{\mathfrak p}\mid\leq\log(R)` for all infinite primes `\mathfrak p`

    OUTPUT:
        A list of upper bounds for each generator such that the bounds are smaller for the generators which are units

    COMMENT:
        We use Smart's ideas to prove that the inequality `\mid\mu -1\mid_{\mathfrak p}\leq\delta` has not nontrivial
        solutions for `\mathfrak p` be an infinite prime

    EXAMPLE::

        sage:

    """
    L = Gl[0].parent()
    infinite_primes = sum(support_of_G(Gl, 200)[1:], [])
    # print 'bounds',bounds
    print 'reduce_bound_for_unit_generators_C3'

    # we find which generators are units
    units_index = [i for i, g in enumerate(Gl) if
                   g.is_integral() and g.absolute_norm().abs() == 1 and g.multiplicative_order() == Infinity]
    Glunit = [g for i, g in enumerate(Gl) if i in units_index]
    c1_units = c_constants(Glunit, 200)[0]

    # we are going to reduce the bound for units using Smart's ideas
    Bold = max([b for i, b in enumerate(bounds) if i in units_index])

    # we find logRlprime
    logRlprime = max([sum([b * log(p(g).abs()).abs() for b, g in zip(bounds, Gl) if g not in Glunit]) if is_real_place(
        p) else sum([2 * b * log(p(g).abs()).abs() for b, g in zip(bounds, Gl) if g not in Glunit]) for p in
                      infinite_primes])

    # we make an arbitrary choice of an initial delta
    delta_old = 1 / R
    delta_new = sqrt(delta_old)

    # we reduce the bounds for the units
    reduce_bounds = bounds
    # print 'len(infinite_primes)',len(infinite_primes),delta_old,delta_new
    while True:
        # print 'makrinari',len([1 for place in infinite_primes if trivial_Tp_infinite_place(reduce_bounds[1:], place, Gl[1:], delta_new)])
        if len([1 for place in infinite_primes if
                trivial_Tp_infinite_place(reduce_bounds[1:], place, Gl[1:], delta_new)]) == len(infinite_primes):
            Bold = min((c1_units * log(delta_new).abs() + c1_units * logRlprime).floor(), Bold)
            # print 'Bold',Bold
            delta_old = delta_new
            delta_new = sqrt(delta_new)
            reduce_bounds = [min(b, Bold) if i in units_index else b for i, b in enumerate(reduce_bounds)]
            print 'reduce_bounds',reduce_bounds
        else:
            return reduce_bounds, 1 / delta_old ** 2


def reduce_cases_with_p_outside_S_and_Hilbert_symbol_C3(I, Gl, Gm, bounds):
    r"""

    INPUT:
        - ``I`` : an ideal of a number field
        - ``Gl`` : a list of generators of the group where `\lambda` lies
        - ``bounds`` : a list of upper bounds for each exponent. It is the same for both groups since by construction
        it holds `m_i=\sigma(l_i^{-1})`, where `l_i` and `m_i` are the generators of `Gl` and `Gm` respectively.

    """
    L = Gl[0].parent()
    Sm = support_of_G(Gm, 20)[0]
    # sigma = find_sigma(L)

    # print 'bounds',bounds

    # the part of the sieve based on Hilbert symbol

    Q = []
    for p in Sm:
        n = p.residue_field().order()
        if n == 2:
            M = matrix(Integers(n), [[tame_hilbert_symbol(gl, gm, p, n) for gm in Gm] for gl in Gl])
        else:
            M = matrix(Integers(n - 1), [[tame_hilbert_symbol(gl, gm, p, n - 1) for gm in Gm] for gl in Gl])
        Q.append(M)

    lcm_hsymbol = lcm([M.base_ring().order() for M in Q])
    # print 'lcm_hsymbol',lcm_hsymbol

    # the part of the sieve based on unramified prime and Hilbert symbol
    factors = I.factor()
    n = len(factors)
    maxorder = lcm([max((f[0] ** f[1]).idealstar().gens_orders()) for f in factors] + [lcm_hsymbol])

    congruence_bounds = [xrange(bounds[0])] + [xrange(maxorder) if 2 * b >= maxorder else xrange(-b, b + 1) for b in
                                               bounds[1:]]
    Bpr = [0 if 2 * b >= maxorder else 1 for b in bounds[1:]]
    # print 'congruence_bound=%s'%(congruence_bounds)
    count = 0
    elements_l = []
    elements_m = []
    for v in cartesian_product_iterator(congruence_bounds):
        v = vector(v)
        if len([1 for M in Q if (v * M * v).is_zero()]) == len(Q):
            # print 'v-1',v
            l = prod([g ** e for g, e in zip(Gl, v)])
            m = prod([g ** e for g, e in zip(Gm, v)])
            if len([1 for f in factors if (l + m - 1).valuation(f[0]) >= f[1]]) == n:
                # print 'v-2',v
                count += 1
                elements_l.append(l)
                elements_m.append(m)

    Sunits = []
    SmunitL = L.S_unit_group(S=Sm)
    B = [QQ(b / len(c)).floor() + 1 if len(c) != 0 else 1 for b, c in zip(bounds[1:], congruence_bounds[1:])]
    # print 'B',B
    Gl_final = [g ** len(c) if b == 0 else 1 for g, c, b in zip(Gl[1:], congruence_bounds[1:], Bpr)]
    Gm_final = [g ** len(c) if b == 0 else 1 for g, c, b in zip(Gm[1:], congruence_bounds[1:], Bpr)]
    # print 'number of final checks %s'%(count * prod([2*b+1 if br == 0 else 1 for b,br in zip(B,congruence_bounds[1:])]))
    import time
    for v in cartesian_product_iterator([xrange(-b, b) if i == 0 else xrange(1) for b, i in zip(B, Bpr)]):
        # start = time.time()
        print 'v',v
        l0 = prod([g ** e for g, e in zip(Gl_final, v)])
        m0 = prod([g ** e for g, e in zip(Gm_final, v)])
        for l1, m1 in zip(elements_l, elements_m):
            if l0 * l1 + m0 * m1 == 1:
                Sunits.append(l0 * l1)
        # end = time.time()
        # print 'time for each loop %s'%(end - start)
        # return 1
    return Sunits


def sieve_for_p_in_support_of_Gl_C3(prime, Gm, Sl, bounds, bound_prime):
    r"""

    INPUT:
        - ``I`` : an ideal of a number field K which a power of a single prime `\mathfrak p`
        - ``Gm`` : a list of generators of a subgroup of `K^*`
        - ``Sl`` : a list of finite primes
        - ``bounds`` : a list of upper bounds for the exponents of the generators(including torsion)

    OUTPUT:
        All `\lambda` of the solutions of the S-unit equation `\lambda+\mu=1` such that `\mu\in G_m`, `I` divides
        `\lambda` and `\lambda` is a ``Sl`` unit.

    EXAMPLE::

        sage: L = QuadraticField(17,'b')
        sage: b = L.gen()
        sage: Gl = [L(-1), -8*b + 33, -3/4*b + 13/4]
        sage: SL = [L.ideal(-1/2*b + 3/2),L.ideal(-1/2*b - 3/2),L.ideal(-b)]
        sage: sieve_for_p_in_support_of_Gl(SL[0]^5,Gl,SL,398)
            [0]
    """
    if Gm == []:
        raise ValueError('Gl is empty')
    L = Gm[0].parent()
    sigma = find_sigma(L)

    # here we need to make a change of generators such that all the generators have 0 valuation at p
    new_Gm0, new_Gm, k = a_basis_with_0_order_at_p(prime, Gm)
    reduce_bounds = [e for i, e in enumerate(bounds) if i != k]
    # new_Gl = [1 / sigma(sigma(mi)) for mi in new_Gm]

    exp = 2
    I = prime ** 2
    while I.idealstar().order() == 1:
        exp += 1
        I *= prime

    if exp > bound_prime:
        return [], exp

    Sunits = []
    for m0 in new_Gm0:
        percent = 1
        while 20 * percent >= 1:
            orders = I.idealstar().gens_orders()

            # we create the congruence relations for the exponents with respect to the ideal p**n
            M = matrix(ZZ, len(new_Gm), len(orders), [I.ideallog(g) for g in new_Gm])
            m0log = vector(ZZ, I.ideallog(m0))
            GCD = [gcd(list(col) + [m] + [t]) for col, m, t in zip(M.columns(), orders, m0log)]
            orders = [c / g for c, g in zip(orders, GCD)]
            M = matrix(ZZ, [col / g for col, g in zip(M.columns(), GCD)]).transpose()
            m0log = vector(ZZ, [c / g for c, g in zip(m0log, GCD)])

            maxorder = max(orders)
            # Now we find which elements satisfy the congruence relation
            if k != 0:
                congruence_bounds = [xrange(maxorder)] * len(reduce_bounds[1:])
                D = [xrange(-RR(B / maxorder).floor() - 1, RR(B / maxorder) + 1) for B in reduce_bounds[1:]]
            else:
                congruence_bounds = [xrange(maxorder)] * len(reduce_bounds)
                D = [xrange(-RR(B / maxorder).floor() - 1, RR(B / maxorder) + 1) for B in reduce_bounds]

            # We find congruence solutions and we store them
            V = []
            m0_elements = []
            for v in cartesian_product_iterator(congruence_bounds):
                v = vector(v)
                if vector([((v * col) + f) % m for m, f, col in zip(orders, m0log, M.columns())]).is_zero():
                    m0_elements.append(m0 ** f * prod([g ** e for g, e in zip(new_Gm, v)]))
                    V.append(v)
            percent = QQ(len(V)) / QQ(maxorder ** len(congruence_bounds))
            if 20 * percent >= 1:
                exp += 1
                I *= prime

        # we determine the solutions

        # new_Gl = [sigma(sigma(1 / g)) for g in new_Gm]
        l0_elements = [sigma(sigma(1 / t)) for t in m0_elements]
        if len(V) != 0:
            new_Gm_powers = [g ** maxorder for g, c, b in new_Gm]
            new_Gl_powers = [sigma(sigma(1 / g)) for g in new_Gm_powers]
            for v in cartesian_product_iterator(D):
                m1 = prod([g ** e for g, e in zip(new_Gm_powers, v)])
                l1 = prod([g ** e for g, e in zip(new_Gl_powers, v)])
                for m0, l0 in zip(m0_elements, l0_elements):
                    if m0 == 1:
                        m = m0 * m1
                        if m0 * m1 not in Sunits:
                            Sunits.append(m)
    return Sunits, exp


def reduce_bound_with_simple_inequalities_C3(Gl, p, bounds, R):
    r"""

    INPUT:
        ``Gl`` : a list of generators
        ``p`` : an infinite prime
        ``bounds`` : a list of upper bounds for the exponents of the generators
        ``R`` : a real number such that `\frac{1}{R}\leq \mid\mu\mid_{p}\leq R` for all infinite primes

    OUTPUT:
        A list of new upper bounds for the generators using simple inequalities

    EXAMPLE::

        sage:
    """
    if is_real_place(p):
        v = [log(p(g).abs()).abs() for g in Gl]
    else:
        v = [2 * log(p(g).abs()).abs() for g in Gl]
    # print 'v',v
    if vector(v).is_zero():
        return bounds
    max_index = v.index(max(v))
    vbar = [c for i, c in enumerate(v) if i != max_index]
    bounds_bar = [b for i, b in enumerate(bounds) if i != max_index]
    # print 'bounds_bar',bounds_bar
    # print 'S',[c*b for c,b in zip(vbar,bounds_bar)]
    S = sum([c * b for c, b in zip(vbar, bounds_bar)])

    # print 'bounds',bounds
    # print 'max_index',max_index
    low_b = QQ(S / v[max_index]).floor()
    # print 'low_b',low_b
    if low_b <= bounds[max_index]:
        for b in range(low_b, bounds[max_index] + 1):
            # print 'b',b
            # print 'v[max_index]*b - S',v[max_index]*b - S
            if v[max_index] * b - S > log(R):
                # print 'b',b
                bounds[max_index] = b
                return bounds
        return bounds
    else:
        return bounds


def nonhomogeneous_solutions(A,M,B,N):
    r"""

    INPUT:
        ``A`` : a matrix
        ``M`` : a vector
        ``B`` : a list of lists
        ``N`` : a matrix

    OUTPUT:
        A solutions `\vector x`for each congruence system `\sum_{j=1}^{n}a_{i,j}x_j\equiv\b_i\mod m_i`,
        where `b_i` lies in ``B[i]``. Returns both `\vector x,\vector b`. The columns of ``N`` are generators
        of the lattice of the solutions `\sum_{j=1}^{n}a_{i,j}x_j\equiv 0\mod m_i`.
    """

    rA,cA = A.dimensions()
    LCM = lcm(M)
    Abar = block_matrix(ZZ,[[A,diagonal_matrix(ZZ,[-m for m in M])]])
    D,U,V = Abar.smith_form()
    D_diagonal = D.diagonal()

    solutions = []
    print 'B',B
    for v in cartesian_product_iterator(B):
        b = vector(v)
        bbar = U*b
        if len([bi/di for bi,di in zip(bbar,D_diagonal) if bi%di == 0]) == rA:
            xbar = D.solve_right(bbar)
            x = V*xbar
            x2 = x[:cA]%LCM
            # print 'x2-1',x2
            t = vector([g.floor() for g in N.inverse()*x2])
            x2 = x2-N*t
            # print 'x2-2',x2
            solutions.append(x2)
    return solutions


def exponents_of_Fermat_equation_C3_S3(Gl,Gm,primes_bound = 7,residue_bound = 3000000):
    """

    INPUT:
        ``Gl``: a list of generators of `G_\lambda`
        ``Gm``: a list of generators of `G_\mu`
        ``primes_bound``: a bound of the range of the rational primes
        ``residue_bound``: a bound for the order of the residue field

    OUTPUT:
        ``Exp``: a list of lists where each list contains the exponents `k` of the Fermat
            equation `s^k+\sigma(1/s)^k=1` in the residue field of the associate prime.
        ``A``: a matrix with integer coefficients. Let `\vec x=(x_1,\cdots,x_n)` be the
            vector of exponents of the free part of ``Gl`` for a solution of the `S`-unit
            equation and `\vec b` the vector of the positive value of the diagonal matrix
            ``B``. Then we have that `A\cdot\vec x\equiv\vec m_0\mod\vec b` where for the
            vector `\vec m_0` we have that the i-th coordinate lies in the i-th list of
            ``Exp``.
        ``B``: a diagonal matrix of negative integers. Each element of the diagonal is
            the opposite value of the multiplicative order of the residue field of the
            associate prime.
        ``N``: a matrix whose columns generate the solutions `\vec x` of `A\cdot\vec x
            \equiv 0\mod\vec b`.

    NOTATION:
        Let `A` be a matrix and `\vec m_0,\vec b` two vectors of suitable dimensions. We denote by
        `A\cdot x\equiv\vec m_0\mod\vec b` the system of congruence equations of `A_i\cdot x\equiv m_{0,i}
        \mod b_i` where `A_i` is the i-th row of `A`, m_{0,i} is the i-th element of `\vec m_0` and
        `b_i` is the i-th element of `\vec b`.
    """
    L = Gl[0].parent()
    torsion_order = len(L.roots_of_unity())
    sigma = find_sigma(L)
    Sl = support_of_G(Gl,50)[0]
    Sm = support_of_G(Gm,50)[0]
    initial_primes = []
    p = ZZ(2)
    while p < primes_bound:
        for P in L.primes_above(p):
            if sigma(P) == P and P not in Sl+Sm:
                if P.residue_field().order() < residue_bound:
                    initial_primes.append(P)
        p = Primes().next(p)
    primes = initial_primes
    # print 'primes',primes
    Fp = [P.residue_field() for P in primes]
    Exp = []
    A = []
    for P,fp in zip(primes,Fp):
        genP = fp.lift(fp.multiplicative_generator())
        sgenP = sigma(1/genP)
        gen = fp(genP)
        sgen = fp(sgenP)
        k = P.ideallog(genP)[0]
        GFp = Integers(fp.order()-1)
        k0 = ZZ(GFp(P.ideallog(Gl[0])[0]/k))
        exp0 = sum([[GFp(i-j*k0) for j in range(torsion_order)] for i in range(fp.order()-1) if gen**i+sgen**i == 1],[])
        exponents = []
        for ex in exp0:
            if ex not in exponents:
                exponents.append(ZZ(ex))
        Exp.append(exponents)
        A += [(vector(Integers(fp.order()-1),[P.ideallog(g)[0]/k for g in Gl[1:]]).change_ring(ZZ)).list()]

    B = diagonal_matrix(ZZ,[-fp.order()+1 for fp in Fp])
    A = matrix(ZZ,A)
    N = block_matrix(ZZ,[[A,B]]).right_kernel_matrix().matrix_from_columns(range(len(Gl)-1)).LLL().transpose()

    return Exp,A,B,N


def final_loop_with_use_of_primes_outside_Sl_C3_S3(Gl,Gm,bound_Gl):
    r"""

    INTPUT
        ``Gl`` : a list of generators of `G_\lambda`
        ``Gm`` : a list of generators of `G_\mu`
        ``bound_Gl`` : a list of bounds for the exponents

    OUTPUT:
        A list of solutions of the S-unit equation `\lambda+\mu=1`.
    """
    
    Exp,A,B,N = exponents_of_Fermat_equation_C3_S3(Gl,Gm)
    nonhom_solutions = nonhomogeneous_solutions(A,[b.abs() for b in B.diagonal()],Exp,N)
    bound = 0
    Vnon_hom = [vector([0] + x1.list()) for x1 in nonhom_solutions]
    for x0 in nonhom_solutions:
        newbound = sum([(bi+x0i.abs())**2 for bi,x0i in zip(bound_Gl[1:],x0)])
        # return N,newbound
        if newbound > bound:
            T0 = matrix(pari(N.transpose()*N).qfminim(newbound).python()[2]).columns()
            bound = newbound
    T0.append(zero_vector(ZZ,N.dimensions()[0]))
    print 'len(Vnon_hom)',len(Vnon_hom)
    print 'len(T0)',len(T0)
    V0 = []
    for e0 in range(bound_Gl[0]):
        for t in T0:
            V0.append(vector([e0]+(N*t).list()))
            V0.append(vector([e0]+(N*(-t)).list()))
    print 'len(V0)',len(V0)
    boundmax = max(bound_Gl)
    Vfinal = []
    for vnon in Vnon_hom:
        for v0 in V0:
            if (vnon+v0).norm(oo) <= boundmax:
                if len([1 for a,b in zip(vnon+v0,bound_Gl) if a.abs() > b]) == 0:
                    Vfinal.append(vnon+v0)
    print 'len(Vfinal)',len(Vfinal)
    # return Vfinal
    sunits = []
    Sm = support_of_G(Gm,30)[0]
    SunitL = Gl[0].parent().S_unit_group(S = Sm)
    for v in Vfinal:
        l = prod([g**e for g,e in zip(Gl,v)])
        if is_S_unit_element(SunitL,1-l):
            sunits.append(l)
    return sunits


def sieve_in_C3(Gl, Gm, B):
    r"""

    INPUT:
        - ``Gl`` : a list of generators of the group where `\lambda` lies.
        - ``Gm`` : a list of generators of the group where `\mu` lies.
        - ``B`` : an upper bound for the exponents

    OUTPUT:
        A listof `\lambda` of the solutions of the `S`-unit equation `\lambda +\mu = 1` up to the action of `S_3` whose
        absolute value of the exponents is less than ``B``.

    EXAMPLE::

        sage:


    """
    L = Gl[0].parent()
    Sl = support_of_G(Gl, 30)[0]
    infinite_primes = sum(support_of_G(Gl, 200)[1:], [])
    sigma = find_sigma(L)
    Slreduce = find_reduce_S_C3(Gl)
    # print 'Slreduce=%s'%(Slreduce)

    # we make lists of upper bounds for each generator
    bound_Gl = [Gl[0].multiplicative_order()] + [B] * (len(Gl) - 1)
    print 'bound_Gl-0', bound_Gl

    # for each prime in Slreduce we get a reduced upper bound for the valuation of lambda using Smart's idea

    bound_Slreduce = [0] * len(Slreduce)
    for i, prime in enumerate(Slreduce):
        bound_Slreduce[i] = bound_Slreduce[Slreduce.index(prime)] = reduce_the_bound_for_p_in_support_of_Gl(prime,Gm, B)

    bound_Sl = [0] * len(Sl)
    for i, p1 in enumerate(Slreduce):
        p2 = sigma(p1)
        p3 = sigma(p2)
        bound_Sl[Sl.index(p1)] = bound_Sl[Sl.index(p2)] = bound_Sl[Sl.index(p3)] = bound_Slreduce[i]
    bound_Gm = bound_Gl = bounds_for_exponents_from_bounds_for_primes(Gl, Sl, bound_Sl, bound_Gl)
    print 'bound_Gl-1', bound_Gl

    # we reduce the bound for the unit generators
    R = max([exp(sum([(log(s(g).abs())).abs() * b for g, b in zip(Gl, bound_Gl) if s(g).abs() != 1])) for s in
             infinite_primes])
    bound_Gl, R = reduce_bound_for_unit_generators_C3(Gl, bound_Gl, R)
    print 'bound_Gl-2', bound_Gl


    old_bound = copy(bound_Gl)
    for p in infinite_primes:
        bound_Gl = reduce_bound_with_simple_inequalities_C3(Gm, p, bound_Gl, R)

    while old_bound != bound_Gl:
        old_bound = copy(bound_Gl)
        for p in infinite_primes:
            bound_Gl = reduce_bound_with_simple_inequalities_C3(Gm, p, bound_Gl, R)

    print 'bound_Gl-3', bound_Gl

    Sunits = []

    # we determine the solutions which are divisible by high powers of primes in Slreduce

    print 'Slreduce',Slreduce
    for k, p in enumerate(Slreduce):
        solutions, exp1 = sieve_for_p_in_support_of_Gl_C3(p,Gm,Sl,bound_Gl,bound_Slreduce[k])
        Sunits += solutions
        solutions, exp2 = sieve_for_p_in_support_of_Gl_C3(p,[sigma(g) for g in Gm],Sl,bound_Gl,bound_Slreduce[k])
        Sunits += solutions
        bound_Slreduce[k] = max(exp1, exp2)
    for i, p1 in enumerate(Slreduce):
        p2 = sigma(p1)
        p3 = sigma(p2)
        bound_Sl[Sl.index(p1)] = bound_Sl[Sl.index(p2)] = bound_Sl[Sl.index(p3)] = bound_Slreduce[i]
    bound_Gl = bounds_for_exponents_from_bounds_for_primes(Gl, Sl, bound_Sl, bound_Gl)
    print 'bound_Gl-4', bound_Gl

    # we reduce the bound for the unit generators again
    bound_Gl, R = reduce_bound_for_unit_generators_C3(Gl, bound_Gl, R)
    print 'bound_Gl-5', bound_Gl

    old_bound = copy(bound_Gl)
    for p in infinite_primes:
        bound_Gl = reduce_bound_with_simple_inequalities_C3(Gm, p, bound_Gl, R)
    #
    while old_bound != bound_Gl:
        old_bound = copy(bound_Gl)
        for p in infinite_primes:
            bound_Gl = reduce_bound_with_simple_inequalities_C3(Gm, p, bound_Gl, R)

    print 'bound_Gl-6', bound_Gl

    #in case

    Sunits += final_loop_with_use_of_primes_outside_Sl_C3_S3(Gl,Gm,bound_Gl)

    # we throw away 0 and 1

    while 0 in Sunits:
        Sunits.remove(0)
    while 1 in Sunits:
        Sunits.remove(1)

    return Sunits


def elliptic_curves_with_good_reduction_with_cubic_two_division_field(K, S, proof = True):
    r"""

    INPUT:
        - ``K`` : a number field
        - ``SK`` : a list of prime ideal of ``K``

    OUTPUT:
        All curves with good reduction outside ``SK`` and at least one rational order 2 point

    EXAMPLE::

        sage:
    """

    if K == QQ:
        K = NumberField(x - 1, 'a')
        SK = [K.prime_above(p) for p in S]
    else:
        SK = S

    # we through away the canditate two division fields whose relative discrimiant does not have even valuation at
    # the primes above which are not in SK

    primes_above_2_not_in_SK = [p2 for p2 in K.primes_above(2) if p2 not in SK]
    if len(primes_above_2_not_in_SK) > 0:
        cubic_fields = []
        for L in cubic_extensions(K, SK + primes_above_2_not_in_SK):
            if len([1 for p in primes_above_2_not_in_SK if L.relative_discriminant().valuation(p) % 2 != 0]) == 0:
                cubic_fields.append(L)
    else:
        cubic_fields = cubic_extensions(K, SK)

    # now we have to add the primes above 2 in SK
    for p in K.primes_above(2):
        if p not in SK:
            SK.append(p)

    J = []
    for L in cubic_fields:
        SL = sum([L.primes_above(p) for p in SK], [])
        Gl, Gm = Norm_subgroup_division_field(SK, SL, proof = proof)
        bound = reduce_the_bound(L, Gl, Gm, 200)
        for l in sieve_in_C3(Gl, Gm, bound):
            j = j_invariant(l)
            if j.absolute_minpoly().degree() <= K.absolute_degree():
                j = j[0]
                if j not in J:
                    J.append(j)

    J = [K(j) for j in J if j in K]+[K(0),K(1728)]
    Jfinal = []
    for j in J:
        if j not in Jfinal:
            Jfinal.append(j)

    if K.absolute_degree() == 1:
        Jfinal = [QQ(j) for j in Jfinal]
        curves = egros_from_jlist_over_K(Jfinal,QQ,[p.smallest_integer() for p in S])
    else:
        curves = egros_from_jlist_over_K(Jfinal,K,S)

    curves = [E for E in curves if E.two_division_polynomial().discriminant().is_square()]
    return curves


##S3 case

def sieve_for_p_in_support_of_Gl_S3(prime, Gm, Sl, bounds, bound_prime, R, Sm, bound_Sm,precision):
    r"""

    INPUT:
        - ``I`` : an ideal of a number field K which a power of a single prime `\mathfrak p`
        - ``Gm`` : a list of generators of a subgroup of `K^*`
        - ``Sl`` : a list of finite primes
        - ``bounds`` : a list of upper bounds for the exponents of the generators(including torsion)

    OUTPUT:
        All `\lambda` of the solutions of the S-unit equation `\lambda+\mu=1` such that `\mu\in G_m`, `I` divides
        `\lambda` and `\lambda` is a ``Sl`` unit.

    EXAMPLE::

        sage: L = QuadraticField(17,'b')
        sage: b = L.gen()
        sage: Gl = [L(-1), -8*b + 33, -3/4*b + 13/4]
        sage: SL = [L.ideal(-1/2*b + 3/2),L.ideal(-1/2*b - 3/2),L.ideal(-b)]
        sage: sieve_for_p_in_support_of_Gl(SL[0]^5,Gl,SL,398)
            [0]
    """
    if Gm == []:
        raise ValueError('Gl is empty')
    L = Gm[0].parent()
    sigma = find_sigma(L)
    SunitL = L.S_unit_group(S=Sl)
    sigma_prime = sigma(prime)

    # here we need to make a change of generators such that all the generators have 0 valuation at p
    new_Gm0, new_Gm, k = a_basis_with_0_order_at_p(prime, Gm)
    reduce_bounds = [e for i, e in enumerate(bounds) if i != k]
    new_Gl = [1 / sigma(sigma(mi)) for mi in new_Gm]
    # units_number = len([g for g in new_Gm if g.is_integral() and g.absolute_norm().abs() == 1])

    exp = 1
    I0 = prime
    while I0.idealstar().order() == 1:
        exp += 1
        I0 *= prime

    if exp > bound_prime:
        return [], exp

    exp_m0 = [exp] * len(new_Gm0)
    Sunits = []
    for m0 in new_Gm0:
        percent = 1
        I = I0
        while 20 * percent >= 1:
            orders = I.idealstar().gens_orders()

            # we create the congruence relations for the exponents with respect to the ideal p**n
            M = matrix(ZZ, len(new_Gm), len(orders), [I.ideallog(g) for g in new_Gm])
            m0log = vector(ZZ, I.ideallog(m0))
            GCD = [gcd(list(col) + [m] + [t]) for col, m, t in zip(M.columns(), orders, m0log)]
            orders = [c / g for c, g in zip(orders, GCD)]
            M = matrix(ZZ, [col / g for col, g in zip(M.columns(), GCD)]).transpose()
            m0log = vector(ZZ, [c / g for c, g in zip(m0log, GCD)])
            maxorder = max(orders)

            # Now we find which elements satisfy the congruence relation
            if k != 0:
                congruence_bounds = [xrange(maxorder) if maxorder <= B else xrange(-B,B+1) for B in reduce_bounds[1:]]
                D = [xrange(-RR(B / maxorder).floor() - 1, RR(B / maxorder) + 1) if maxorder <= B else xrange(0,1) for B in reduce_bounds[1:]]
            else:
                congruence_bounds = [xrange(maxorder) if maxorder <= B else xrange(-B,B+1) for B in reduce_bounds]
                D = [xrange(-RR(B / maxorder).floor() - 1, RR(B / maxorder) + 1) if maxorder <= B else xrange(0,1) for B in reduce_bounds]

            D_bounds = [len(d)/2 for d in D if len(d) != 1]

            # We find congruence solutions and we store them
            m0_elements = []
            Vcon = []
            for v in cartesian_product_iterator(congruence_bounds):
                v = vector(v)
                if vector([((v * col) + f) % m for m, f, col in zip(orders, m0log, M.columns())]).is_zero():
                    Vcon.append(v)
                    m0_elements.append(m0 * prod([g ** e for g, e in zip(new_Gm, v)]))
            percent = QQ(len(m0_elements)) / QQ(prod([len(b) for b in congruence_bounds]))

            if 20 * percent >= 1:
                exp_m0[new_Gm0.index(m0)] += 1
                I *= prime

        # I am going to use Fincke-Pohst algorithm only for the unit generators and for both Gm and Gl
        if len([1 for d in D if len(d) > 1]) > 0 :
            suppGm = support_of_G(Gm, precision)
            new_Gmk = [g**maxorder for g,d in zip(new_Gm,D) if len(d) != 1]
            Am = zero_matrix(RealField(prec=precision), len(suppGm[1] + suppGm[2]+suppGm[0]), len(new_Gmk))

            i = 0
            for pr in suppGm[1]:
                logm0max = max([log(pr(t).abs()).abs() for t in m0_elements])
                # logm0max = log(pr(m0con).abs()).abs()
                logRm = log(R) + logm0max
                Am[i] = vector([log(pr(mi).abs()) for mi in new_Gmk]) / logRm
                i += 1

            for pr in suppGm[2]:
                logm0max = max([2 * log(pr(t).abs()).abs() for t in m0_elements])
                # logm0max = 2 * log(pr(m0con).abs()).abs()
                logRm = log(R) + logm0max
                Am[i] = vector([2 * log(pr(mi).abs()) for mi in new_Gmk]) / logRm
                i += 1

            for pr in suppGm[0]:
                logm0max = max([log(t.abs_non_arch(pr,prec = precision)).abs() for t in m0_elements])
                p = pr.absolute_norm().factor()[0][0]
                fpr = pr.residue_class_degree()
                logRm = bound_Sm[Sm.index(pr)] * fpr * log(p) + logm0max
                Am[i] = vector([log(mi.abs_non_arch(pr,prec = precision)) for mi in new_Gmk]) / logRm
                i += 1

            if log(det(Am.transpose() * Am).abs()) < -30:
                Q = Am.transpose() * Am
                f = len(suppGm[1] + suppGm[2]+suppGm[0])
                V1 = []
                for v in cartesian_product_iterator([xrange(-d,d+1) for d in D_bounds]):
                    v = vector(v)
                    if v*Q*v <= f:
                        V1.append(v)
            else:
                V1 = pari(Am.transpose() * Am).qfminim(len(suppGm[1] + suppGm[2]+suppGm[0]), flag=2).python()[2].columns()
            Vfinal = []

            for v in V1:
                if  len([1 for a,b in zip(D_bounds,v) if b.abs() > a]) == 0:
                    Vfinal.append(v)
                    Vfinal.append(-v)
        else:
            V1 = []
            Vfinal = []

        SmQ = []
        for q in Sm:
            p = q.absolute_norm().factor()[0][0]
            if p not in SmQ:
                SmQ.append(p)
        print 'm0_elements,Vfinal,e',len(m0_elements),len(Vfinal),e
        if len(m0_elements) != 0:
            M1 = [prod([ g ** e for g, e in zip(new_Gmk, v)]) for v in Vfinal]+[L(1)]
            for  m0 in m0_elements:
                for m1 in M1:
                    a0 = QQ(sum((m0*m1).absolute_minpoly().list()))
                    if QQ(a0.prime_to_S_part(SmQ).abs()) == 1:
                        if is_S_unit_element(SunitL,1-m0 * m1):
                            Sunits.append(m0 * m1)

    return Sunits, min(exp_m0)


def reduce_bound_for_unit_generators_S3(Gl, Gm, bounds, R):
    r"""

    INPUT:
        - ``Gl`` : a list of generators of the group where `\lambda` lies
        - ``Gm`` : a list of generators of the group where `\mu` lies
        - ``bounds`` : a list of upper bounds for each generator
        - ``R`` : a real number such that `\mid\log\mid\mu\mid_{\mathfrak p}\mid\leq\log(R)` for all infinite primes `\mathfrak p`

    OUTPUT:
        A list of upper bounds for each generator such that the bounds are smaller for the generators which are units

    COMMENT:
        We use Smart's ideas to prove that the inequality `\mid\mu -1\mid_{\mathfrak p}\leq\delta` has not nontrivial
        solutions for `\mathfrak p` be an infinite prime

    EXAMPLE::

        sage:

    """
    # L = Gl[0].parent()
    infinite_primes_Gl = sum(support_of_G(Gl, 200)[1:], [])
    infinite_primes_Gm = sum(support_of_G(Gm, 200)[1:], [])
    infinite_primes = infinite_primes_Gl + [p for p in infinite_primes_Gm if p not in infinite_primes_Gl]
    length_infinite_primes = len(infinite_primes)

    # we find which generators are units
    units_index = [i for i, g in enumerate(Gl) if
                   g.is_integral() and g.absolute_norm().abs() == 1 and g.multiplicative_order() == Infinity]
    Glunit = [g for i, g in enumerate(Gl) if i in units_index]

    if len(Glunit) == 0:
        return bounds, R
    c1_units = c_constants(Glunit, 200)[0]
    print 'c1',c1_units

    # we are going to reduce the bound for units using Smart's ideas
    Bold = max([bounds[b] for b in units_index])
    print 'Bold',Bold

    # we find logRlprime
    c2inf = max([sum([b * log(p(g).abs()).abs() for b, g in zip(bounds, Gl) if g not in Glunit]) if is_real_place(
        p) else sum([2 * b * log(p(g).abs()).abs() for b, g in zip(bounds, Gl) if g not in Glunit]) for p in
                      infinite_primes])

    print 'c2inf',c2inf

    # we make an arbitrary choice of an initial delta
    delta_old = 1 / R
    delta_new = 1/RR(10**60)#sqrt(delta_old)
    print 'delta_new',delta_new
    print 'log(delta_new).abs()',log(delta_new).abs()
    # return 1
    # we reduce the bounds for the units
    reduce_bounds = bounds
    while True:

        sm = len([1 for place in infinite_primes if
                  trivial_Tp_infinite_place(reduce_bounds[1:], place, Gm[1:], delta_new)])
        sl = len([1 for place in infinite_primes if
                  trivial_Tp_infinite_place(reduce_bounds[1:], place, Gl[1:], delta_new)])
        if sm == length_infinite_primes and sl == length_infinite_primes:
            Bold = min((c1_units * log(delta_new).abs() + c1_units * c2inf).floor(), Bold)
            delta_old = delta_new
            delta_new = sqrt(delta_new)
            reduce_bounds = [min(b, Bold) if i in units_index else b for i, b in enumerate(reduce_bounds)]
        else:
            return reduce_bounds, 1 / delta_old ** 2


def reduce_the_bound_for_place_in_support_of_Gl(place,Gens,bounds):
    r"""

    INPUT:
        - ``place`` : an infinite place
        - ``Gens`` : a list of generators of multiplicative group (including torsion)
        - ``bounds`` : a list of upper bounds for each generator

    OUTPUT:
        A number ``log(R)`` such that `\frac{1}{R}\leq |g|_p\leq R` where `p` is the place for `g` in ``Gens``
    """
    # print 'place'
    if is_real_place(place):
        R = exp(sum([(log(place(g).abs())).abs() * b for g, b in zip(Gens, bounds)]))
    else:
        R = exp(sum([(2 * log(place(g).abs())).abs() * b for g, b in zip(Gens, bounds)]))
    delta_old = 1/R
    delta_new = sqrt(delta_old)
    square_reduction = True
    while square_reduction:
        if trivial_Tp_infinite_place(bounds[1:], place, Gens[1:], delta_new):
            delta_old = delta_new
            delta_new = sqrt(delta_old)
        else:
            square_reduction = False

    while trivial_Tp_infinite_place(bounds[1:], place, Gens[1:], delta_old*10):
        delta_old *= 10

    return log(delta_old).abs()


def sieve_in_S3(Gl, Gm, B):
    r"""

    INPUT:
        - ``Gl`` : a list of generators of the group where `\lambda` lies.
        - ``Gm`` : a list of generators of the group where `\mu` lies.
        - ``B`` : an upper bound for the exponents

    OUTPUT:
        A listof `\lambda` of the solutions of the `S`-unit equation `\lambda +\mu = 1` up to the action of `S_3` whose
        absolute value of the exponents is less than ``B``.

    EXAMPLE::

        sage:


    """
    L = Gl[0].parent()
    Sl, real_infinite_primes_Sl, complex_infinite_primes_Sl = support_of_G(Gl, 200)
    Sm, real_infinite_primes_Sm, complex_infinite_primes_Sm = support_of_G(Gm, 200)
    infinite_primes_Gl = real_infinite_primes_Sl + complex_infinite_primes_Sl #[p for p in real_infinite_primes_Sl + complex_infinite_primes_Sl if p in real_infinite_primes_Sm + complex_infinite_primes_Sm]
    sigma = find_sigma(L)
    Glm = [Gl[0]]+[m/l for m,l in zip(Gm[1:],Gl[1:])]


    # when we have only one generator of the free part
    if len(Gl) == 2:
        Sunits = []
        find_prime = False
        p = 2
        while not find_prime:
            for pL in L.primes_above(p):
                if pL not in Sl and pL not in Sm and not pL.idealstar().is_trivial():
                    pK = pL.ideal_below()
                    if pK.residue_class_degree() == pL.residue_class_degree():
                        I = L.ideal(pL.ideal_below())
                        find_prime = True
            p = Primes().next(ZZ(p))

        # we do the final sieve using the unramified and split prime we found above and the Hilbert symbol
        for l in reduce_cases_with_p_outside_S_and_Hilbert_symbol_C3(I, Gl, Gm, [
            L.primitive_root_of_unity().multiplicative_order()] + [B]):
            if l not in Sunits:
                Sunits.append(l)

        return Sunits

    # we have gp6 primes
    for p in Sl:
        if len(L.primes_above(p.ideal_below().ideal_below())) == 6:
            raise ValueError('There exists a prime with 6 primes!')

    # gp3 and gp6 mean the primes which have 3 and 6 congugate primes respectively

    SlnotSm_gp3 = []
    for p in Sl:
        p_below = p.ideal_below().ideal_below()
        if len(L.primes_above(p_below)) == 3:
            if p not in Sm:
                SlnotSm_gp3.append(p)

    # we make lists of upper bounds for each generator
    bound_Gl = [Gl[0].multiplicative_order()] + [B] * (len(Gl) - 1)
    bound_Sl = [0] * len(Sl)
    bound_Sm = [0] * len(Sm)
    print 'bound Gl-0', bound_Gl

    # for each prime in SlnotSm_gp3 we get a reduced upper bound for the valuation of lambda using Smart's idea

    for prime in SlnotSm_gp3:
        e = reduce_the_bound_for_p_in_support_of_Gl(prime, Gm, B)
        bound_Sl[Sl.index(prime)] = e
        if sigma(prime) in Sl:
            bound_Sl[Sl.index(sigma(prime))] = e
        else:
            bound_Sl[Sl.index(sigma(sigma(prime)))] = e

    for prime in SlnotSm_gp3:
        bound_Sm[Sm.index(sigma(prime))] = bound_Sm[Sm.index(sigma(sigma(prime)))] = bound_Sl[Sl.index(prime)]

    bound_Gl = bounds_for_exponents_from_bounds_for_primes(Gl, Sl, bound_Sl, bound_Gl)
    print 'bound_Gl-1', bound_Gl

    # for each infinite place we get an upper bound for `|\log|\lambda|_p|`

    bound_places = [max(reduce_the_bound_for_place_in_support_of_Gl(place,Gm,bound_Gl),reduce_the_bound_for_place_in_support_of_Gl(place,Glm,bound_Gl)) for place in infinite_primes_Gl]

    primes_bounds = []
    for P,v in zip(Sl,bound_Sl):
        fp = P.residue_class_degree()
        p = P.smallest_integer()
        primes_bounds += [log(p) * fp * v]
    bound_Gl = [bound_Gl[0]]+bounds_for_exponents_from_bounds_of_absolute_values(Gl[1:], Sl, primes_bounds, infinite_primes_Gl, bound_places)

    # we reduce the bound for the unit generators
    # R = max([exp(sum([(2 * log(s(g).abs())).abs() * b for g, b in zip(Gl, bound_Gl) if s(g).abs() != 1])) for s in infinite_primes])


    # bound_Gl, R = reduce_bound_for_unit_generators_S3(Gl, Gm, bound_Gl, R)
    # print 'bound_Gl-2', bound_Gl,R
    # return bound_Gl
    #
    # # we reduce the bound using simple inequalities
    #
    # old_bound = copy(bound_Gl)
    # for p in infinite_primes:
    #     bound_Gl = reduce_bound_with_simple_inequalities_C3(Gm, p, bound_Gl, R)
    #
    # while old_bound != bound_Gl:
    #     old_bound = copy(bound_Gl)
    #     for p in infinite_primes:
    #         bound_Gl = reduce_bound_with_simple_inequalities_C3(Gm, p, bound_Gl, R)
    #
    # print 'bound_Gl-3', bound_Gl
    # print 'bound_Sl', bound_Sl
    #
    # # return bound_Gl

    Sunits = []

    # we determine the solutions which are divisible by high powers of primes in SlnotSm_gp3


    #return final_loop_with_use_of_primes_outside_Sl_C3_S3(Gl,Gm,bound_Gl)

    # for k, p in enumerate(SlnotSm_gp3):
    #     print 'mpika'
    #     # return p,Sl,bound_Sl[Sl.index(p)],R,Sm,bound_Sm
    #     solutions, e = sieve_for_p_in_support_of_Gl_S3(p, Gm, Sl, bound_Gl, bound_Sl[Sl.index(p)],R,Sm,bound_Sm, 400)
    #
    #     Sunits += solutions
    #     bound_Sl[Sl.index(p)] = e
    #     if sigma(p) in Sl:
    #         bound_Sl[Sl.index(sigma(p))] = e
    #     else:
    #         bound_Sl[Sl.index(sigma(sigma(p)))] = e
    #
    #     # again we get new bounds for the exponents by the new bounds we have to the primes
    #     bound_Gl = bounds_for_exponents_from_bounds_for_primes(Gl, Sl, bound_Sl, bound_Gl)
    #     print 'bound_Gl-4', bound_Gl
    #
    # # we reduce the bound for the unit generators again
    # # return bound_Gl,R
    # bound_Gl, R = reduce_bound_for_unit_generators_S3(Gl, Gm, bound_Gl, R)
    # print 'bound_Gl-5', bound_Gl
    #
    # # we reduce the bound using simple inequalities again
    #
    # old_bound = copy(bound_Gl)
    # for p in infinite_primes:
    #     bound_Gl = reduce_bound_with_simple_inequalities_C3(Gm, p, bound_Gl, R)
    #
    # while old_bound != bound_Gl:
    #     old_bound = copy(bound_Gl)
    #     for p in infinite_primes:
    #         bound_Gl = reduce_bound_with_simple_inequalities_C3(Gm, p, bound_Gl, R)
    #
    print 'bound_Gl-6', bound_Gl
    return 1
    # return final_loop_with_use_of_primes_outside_Sl_C3_S3(Gl,Gm,bound_Gl)
    Sunits += final_loop_with_use_of_primes_outside_Sl_C3_S3(Gl,Gm,bound_Gl)

    # we throw away 0 and 1

    while L(0) in Sunits:
        Sunits.remove(L(0))
    while L(1) in Sunits:
        Sunits.remove(L(1))

    return Sunits


def elliptic_curves_with_good_reduction_with_S3_two_division_field(K, S):
    r"""

    INPUT:
        - ``K`` : a number field
        - ``SK`` : a list of prime ideal of ``K``

    OUTPUT:
        All curves with good reduction outside ``SK`` and at least one rational order 2 point

    EXAMPLE::

        sage:
    """
    import time

    if K == QQ:
        K = NumberField(x - 1, 'a')
        SK = [K.prime_above(p) for p in S]
    else:
        SK = S

    # we through away the canditate two division fields whose relative discrimiant does not have even valuation at
    # the primes above which are not in SK


    primes_above_2_not_in_SK = [p2 for p2 in K.primes_above(2) if p2 not in SK]
    if len(primes_above_2_not_in_SK) > 0:
        S3_fields = []
        quadratic_subfields = []
        cubic_polynomials = []
        T = s3_extensions(K, SK + primes_above_2_not_in_SK)
        for f, L, M in zip(T[0], T[1], T[2]):
            K_abs_degree = K.absolute_degree()
            dM = M.relative_discriminant()
            L1 = K.extension(f, 'l1')
            dL1 = L1.relative_discriminant()
            t = dM ** 3 * dL1 ** 2

            if len([1 for p in primes_above_2_not_in_SK if (t.valuation(p) - 3 * dM.valuation(p)) % 4 != 0]) == 0:
                S3_fields.append(L)
                quadratic_subfields.append(M)
                cubic_polynomials.append(f)
    else:
        cubic_polynomials, S3_fields, quadratic_subfields = s3_extensions(K, SK)

    # now we have to add the primes above 2 in SK
    for p in primes_above_2_not_in_SK:
        SK = [p] + SK

    J = []
    for f, L in zip(cubic_polynomials, S3_fields):
        SL = sum([L.primes_above(p) for p in SK], [])
        Gl, Gm = Norm_subgroup_division_field(SK, SL,f)
        print 'Gl',len(Gl)-1
        bound = reduce_the_bound(L, Gl, Gm, 200)
        print 'bound',bound
        for l in sieve_in_S3(Gl, Gm, bound):
            j = j_invariant(l)
            if j.absolute_minpoly().degree() <= K.absolute_degree():
                j = j[0]
                if j not in J:
                    J.append(j)

    J = [K(j) for j in J]+[K(0),K(1728)]
    Jfinal = []
    for j in J:
        if j not in Jfinal:
            Jfinal.append(j)

    if K.absolute_degree() == 1:
        Jfinal = [QQ(j) for j in Jfinal]
        curves = egros_from_jlist_over_K(Jfinal,QQ,[ZZ(p) for p in S])
    else:
        curves = egros_from_jlist_over_K(Jfinal,K,S)

    curves = [E for E in curves if not E.two_division_polynomial().discriminant().is_square()]

    return curves



#the function that computes elliptic curves with good reduction outside S
#based on Angelos Koutsianas' thesis with title `Applications of S-unit Equations to the
#Arithmetic of Elliptic Curves'

def elliptic_curves_with_good_reduction_outside_S(K,S,proof = True):
    """

    INPUT:
        - ``K`` : a number field
        - ``S`` : a list of prime ideals of ``K``

    OUTPUT:
        All elliptic curves over ``K`` with good reduction outside ``S``

    COMMENT:
        This implementation is based on Angelos Koutsianas' thesis which computed curves
        by solving `S`-unit equations.

    EXAMPLE::

        sage: S = [2]
        sage: curves = elliptic_curves_with_good_reduction_outside_S(QQ,S)
        sage: len(curves)
            24

        sage: S = [2,3]
        sage: curves = elliptic_curves_with_good_reduction_outside_S(QQ,S)
    """

    #we compute curves with trivial or quadratic 2-division field

    curves_C2_1 = elliptic_curves_with_good_reduction_with_a_rational_Weierstrass_point(K, S, proof)

    #we compute curves with cubic 2-division field

    curves_C3 = elliptic_curves_with_good_reduction_with_cubic_two_division_field(K,S)

    #we compute curves with S3 2-diviosion field

    curves_S3 = elliptic_curves_with_good_reduction_with_S3_two_division_field(K,S)

    #we order the curves according to the absolute norm of the their conductor

    curves = curves_C2_1 + curves_C3 + curves_S3

    if K == QQ:
        for i in range(len(curves)):
            for j in range(i,len(curves)):
                if curves[i].conductor() > curves[j].conductor():
                    temp = curves[i]
                    curves[i] = curves[j]
                    curves[j] = temp

    else:
        for i in range(len(curves)):
            for j in range(i,len(curves)):
                if curves[i].conductor().absolute_norm() > curves[j].conductor().absolute_norm():
                    temp = curves[i]
                    curves[i] = curves[j]
                    curves[j] = temp

    return curves



##Non trivial Tp set using Smart's ideas

#Non complete list of curve
def non_complete_egros(K,SK,B = 20,proof = True):
    r"""

    INTPUT:
        ``K`` : a number field
        ``SK`` : a finite set of primes
        ``proof`` : for the computations of S-unit groups

    OUTPUT
        A list of potential complete list of all elliptic curves over ``K``
        with good reduction outside ``SK``
    """
    L = two_division_fields(K,SK)

    J2 = []
    for M in L[0]:
        Gl,Gm = Norm_subgroup_division_field(SK,sum([M.primes_above(p) for p in SK],[]),proof = proof)
        J2 += non_complete_solutions(Gl,Gm,K,B = B)

    J3 = []
    for M in L[1]:
        Gl,Gm = Norm_subgroup_division_field(SK,sum([M.primes_above(p) for p in SK],[]),proof = proof)
        J3 += non_complete_solutions(Gl,Gm,K,B = B)

    JS3 = []
    for M,h in zip(L[3],L[2]):
        Gl,Gm = Norm_subgroup_division_field(SK,sum([M.primes_above(p) for p in SK],[]),h,proof = proof)
        JS3 += non_complete_solutions(Gl,Gm,K,B = B)

    J = [K(0),K(1728)]
    for j in J2+J3+JS3:
        if j not in J:
            J.append(j)

    return J

def non_complete_solutions(Gl,Gm,K,b = 10,B = 20):
    r"""

    INPUT:
        ``Gl`` : a list of generators
        ``Gm`` : a list of generators
        ``K`` : the base field

    RETURN:
        A list of solutions up to the action of `S_3` for the S-unit equation
        `\lambda+\mu=1` for `\lambda\in Gl` and `\mu\in Gm`
    """

    L = Gl[0].parent()
    Sm = support_of_G(Gm,10)[0]
    Sl = support_of_G(Gl,10)[0]
    Slm = Sm + [p for p in Sl if p not in Sm]
    SunitL = L.S_unit_group(S = Slm)
    stop = False
    sol = []
    while not stop and b <= B:
        soltemp = []
        for v in cartesian_product_iterator([xrange(Gl[0].multiplicative_order())]+[xrange(b+1)]+[xrange(-b,b+1)]*(len(Gl)-2)):
            l = prod([g**e for g,e in zip(Gl,v)])
            if is_S_unit_element(SunitL,1-l):
                soltemp.append(l)

        if len(sol) == len(soltemp):
            stop = True
        else:
            b +=2
            sol = soltemp
    J = []
    if L.absolute_degree()/K.absolute_degree() == 6:
        for l in sol:
            j = j_invariant(l)
            if j.minpoly().degree() == 1:
                if j[0][0] not in J:
                    J.append(j[0][0])
    else:
        for l in sol:
            j = j_invariant(l)
            if j.minpoly().degree() == 1:
                if j[0] not in J:
                    J.append(j[0])
    return J
