def eroots(E):
    r'''
    
    INPUT:
        
    - ``E`` : an elliptic curve
    
    OUTPUT:
        
     The three roots of the 2 - division polynomial of ``E``
     
    EXAMPLES::
        
      sage : E = EllipticCurve([0,0,0,-1,0])
      sage : eroots(E)
        (1, 0, -1)  
    '''      
   
    f = E.division_polynomial(2)
    L = f.splitting_field('a')
    e1, e2, e3 = f.roots(L)
    
    return e1[0], e2[0], e3[0]


def lambda_invariants(E):
    r'''
    
    INPUT:
        
    - ``E`` : an elliptic curve
    
    OUTPUT:
    
     A list with all lambda invariants of E.
    
    EXAMPLES::
        
      sage : E = EllipticCurve([0,0,0,-1,0])
      sage : lambda_invariants(E)
          [1/2, 2, 1/2, -1, 2, -1]
    '''
    
    e1, e2, e3 = eroots(E) 
    l = (e1 - e2) / (e1 - e3)
    
    return [l,1/l,1-l,1-1/l,1/(1-l),l/(l-1)]


def j_invariant(l):
    r"""
    
    INPUT:
        - ``l`` : the lambda invariant of an elliptic curve `E`
        
    OUTPUT:
         The associate to ``l`` `j`-invariant of `E`
    """
    
    return (2**8 *(l**2 - l + 1)**3)/(l**2 * (1-l)**2)


def has_good_reduction_outside_S_over_K(E,S):
    r"""

    INPUT:
        - ``E`` : an elliptic curve
        - ``S`` : a set of primes of the field of definition of ``E``

    OUTPUT:
        True, if ``E`` has good reduction outside ``S``, otherwise False. We use Lemma 3.1 of the reference

    REFERENCE:
        J. E. Cremona and M. P. Lingham. Finding All Elliptic Curves with Good Reduction Outside a Given Set of Primes.
        Experimental Mathematics, 16(3):303-312, 2007.

    """
    K = E.base_ring()
    D = E.discriminant()
    d = D.absolute_norm()

    SQ = []
    for P in S:
        p = P.absolute_norm().factor()[0][0]
        if p not in SQ:
            SQ.append(p)

    d = d.prime_to_S_part(SQ)

    for p in K.primes_above(d):
        if not E.has_good_reduction(p) and p not in S:
            return False

    return True


def egros_from_0_over_K(K,S):
    r"""

    INPUT:
        - ``K`` : a number field
        - ``S`` : a list of primes of ``K``

    OUTPUT:

        A list with all elliptic curves over ``K`` with good reduction outside ``S`` and `j`-invariant equal to 0.

    REFERENCE:
        J. E. Cremona and M. P. Lingham. Finding All Elliptic Curves with Good Reduction Outside a Given Set of Primes.
        Experimental Mathematics, 16(3):303-312, 2007.

    EXAMPLE::

        sage:

    """

    if K == QQ:
        from sage.schemes.elliptic_curves.ell_egros import egros_from_j_0
        return egros_from_j_0(S)

    #S contains a prime above 3 such that its order at 3 is odd
    for p in K.primes_above(3):
        if (K(3)).valuation(p) %2 == 1 and p not in S:
            return []

    Sprime = copy(S)

    #we add suitable primes above 2
    for p in K.primes_above(2):
        if (K(2)).valuation(p)%3 == 1 or (K(2)).valuation(p)%3 == -1 and p not in Sprime:
            Sprime.append(p)

    #we add suitable primes above 3
    for p in K.primes_above(3):
        if (K(2)).valuation(p)%4 == 2 and p not in Sprime:
            Sprime.append(p)

    SprimenotS_2 = [p for p in Sprime if p not in S and (K(2)).valuation(p) != 0]
    SprimenotS_3 = [p for p in Sprime if p not in S and (K(3)).valuation(p) != 0]

    import time

    selmergens,orders = K.selmer_group(Sprime,6,orders=True)

    curves = []
    if len(SprimenotS_2) + len(SprimenotS_3) == 0:
        for v in cartesian_product_iterator([xrange(b) for b in orders]):
            w = prod([g**i for g,i in zip(selmergens,v)])
            E = EllipticCurve([0,w])
            if has_good_reduction_outside_S_over_K(E,S):
                curves.append(E)
        return curves

    for v in cartesian_product_iterator([xrange(b) for b in orders]):
        w = prod([g**i for g,i in zip(selmergens,v)])
        if len([1 for p in SprimenotS_3 if w.valuation(p)%6 == 3 and (K(3)).valuation(p)%4 == 2]) == len(SprimenotS_3):
            n1 = len([1 for p in SprimenotS_2 if w.valuation(p)%6 == 4 and (K(2)).valuation(p)%3 == 1])
            n2 = len([1 for p in SprimenotS_2 if w.valuation(p)%6 == 2 and (K(2)).valuation(p)%3 == 2])
            if n1+n2 == len(SprimenotS_2):
                E = EllipticCurve([0,w])
                start = time.time()
                if has_good_reduction_outside_S_over_K(E,S):
                    curves.append(E)

    return curves


def egros_from_1728_over_K(K,S):
    r"""

    INPUT:
        - ``K`` : a number field
        - ``S`` : a list of primes of ``K``

    OUTPUT:

        A list with all elliptic curves over ``K`` with good reduction outside ``S`` and `j`-invariant equal to 1728.

    REFERENCE:
        J. E. Cremona and M. P. Lingham. Finding All Elliptic Curves with Good Reduction Outside a Given Set of Primes.
        Experimental Mathematics, 16(3):303-312, 2007.

    EXAMPLE::

        sage:

    """
    if K == QQ:
        from sage.schemes.elliptic_curves.ell_egros import egros_from_j_1728
        return egros_from_j_1728(S)

    Sprime = copy(S)

    #we add suitable primes above 2
    for p in K.primes_above(2):
        if (K(2)).valuation(p)%2 == 1 and p not in Sprime:
            Sprime.append(p)

    SprimenotS = [p for p in Sprime if p not in S]

    selmergens,orders = K.selmer_group(Sprime,4,orders=True)

    curves = []

    if len(SprimenotS) == 0:
        for v in cartesian_product_iterator([xrange(b) for b in orders]):
            w = prod([g**i for g,i in zip(selmergens,v)])
            E = EllipticCurve([w,0])
            if has_good_reduction_outside_S_over_K(E,S):
                curves.append(E)
        return curves


    for v in cartesian_product_iterator([xrange(b) for b in orders]):
        w = prod([g**i for g,i in zip(selmergens,v)])
        if len([1 for p in SprimenotS if w.valuation(p)%4 == 2]) == len(SprimenotS):
            E = EllipticCurve([w,0])
            if has_good_reduction_outside_S_over_K(E,S):
                curves.append(E)
    return curves


def egros_from_j_over_K(j,K,S):
    r"""

    INPUT:
        - ``K`` : a number field
        - ``S`` : a list of primes of ``K``

    OUTPUT:

        A list with all elliptic curves over ``K`` with good reduction outside ``S`` and `j`-invariant equal to
        ``j``.

    REFERENCE:
        J. E. Cremona and M. P. Lingham. Finding All Elliptic Curves with Good Reduction Outside a Given Set of Primes.
        Experimental Mathematics, 16(3):303-312, 2007.

    EXAMPLE::

        sage:

    """
    if K == QQ:
        from sage.schemes.elliptic_curves.ell_egros import egros_from_j
        return egros_from_j(j,S)

    if j == K(0):
        return egros_from_0_over_K(K,S)
    if j == K(1728):
        return egros_from_1728_over_K(K,S)

    w = j**2 * (j - 1728)**3
    #the case w not in K(S,6)

    if not in_KSn(w,S,6):
        return []

    #the case w in K(S,4)_2

    J = brace_map(w,S,2)[1]
    power_n, W0 = in_nCKSmn(J,S,2,2)
    principal, u = is_S_principal(J/W0**2,S)
    #we choose t as in the reference

    curves = []
    u /= 3
    if power_n:
        if principal:
            if K.class_number() == 1:
                E = EllipticCurve([-3*u**2*j*(j-1728),-2*u**3*j*(j-1728)**2]).global_minimal_model()
            else:
                E = EllipticCurve([-3*u**2*j*(j-1728),-2*u**3*j*(j-1728)**2]).global_minimal_model(semi_global=True)
            Sel2 = K.selmer_group(S,2)
            for v in cartesian_product_iterator([xrange(2)]*len(Sel2)):
                t = prod([g**e for g,e in zip(Sel2,v)])
                Et = E.quadratic_twist(t).integral_model()
                if has_good_reduction_outside_S_over_K(Et,S):
                    curves.append(Et)

    return curves


def egros_from_jlist_over_K(J,K,S):
    r"""

    INPUT:
        - ``J`` : a list of `j`-invariants
        - ``K`` : a number field `K`
        - ``S``: a finite set of primes of ``K``

    OUTPUT:
        A list of all elliptic curves over ``K`` with good reduction outside ``S`` with `j`-invariant in ``J``

    EXAMPLE::
        sage:
    """

    return sum([egros_from_j_over_K(j,K,S) for j in J],[])


def j_invariant_of_2_isogenous(j):
    r"""

    INPUT:
        - ``j`` : the `j`-invariant of an elliptic curve with exactly one rational point of order 2.

    OUTPUT:
        The `j`-invariant of its 2-isogenous curve.
    """
    if j == 0:
        return []

    if j == 1728:
        return [EllipticCurve([-4,0]).j_invariant()]

    E = EllipticCurve([1,0,0,-36/(j-1728),-1/(j-1728)]).short_weierstrass_model()
    roots = E.two_division_polynomial().roots()
    if len(roots) == 1:
        r = roots[0][0]
        a1,a2,a3,a4,a6 = E.change_weierstrass_model(1,r,0,0).a_invariants()
        return [EllipticCurve([0,-2*a2,0,a2**2-4*a4,0]).j_invariant()]
    elif len(roots) == 3:
        J = []
        for r in roots:
            a1,a2,a3,a4,a6 = E.change_weierstrass_model(1,r[0],0,0).a_invariants()
            j = EllipticCurve([0,-2*a2,0,a2**2-4*a4,0]).j_invariant()
            if j not in J:
                J.append(j)
        return J

