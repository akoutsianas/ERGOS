def suitable_element_of_Kz(K,S):
    r"""
    
    INPUT:
        - ``K`` : a number field with `\zeta_3\not\in K`
        - ``S`` : a list of prime ideals of ``K``
        
    OUTPUT:
        A list of all 2-tuples `[b,Tr_{Kz/K}(a)]` we need, in order to determine a defining polynomial of a suitable cubic extension of ``K``. 
        
    REFERENCE:
        - Henri Cohen. Advanced Topics in Computational Number Theory. Number 193 in Graduate Texts in Mathematics. Springer-Verlag, New York, 1999. It is a special case of the theorem 5.3.5.
        - Angelos Koutsianas Thesis, 
    
    EXAMPLE::
        
        sage: K.<a> = NumberField(x-1)
        sage: S = sum([K.primes_above(p) for p in [2,3]],[])
        sage: suitable_element_of_Kz(K,S)
            [[1,1]]
            
        sage: K.<a> = NumberField(x^2+1)
        sage: S = sum([K.primes_above(p) for p in [2,3]],[])
        sage: suitable_element_of_Kz(K,S)
            [[-1, a], [-a, a - 1], [a, -2*a + 1], [-a, 2*a + 1]]
            
        sage: K.<a> = NumberField(x^2+3)
        sage: S = sum([K.primes_above(p) for p in [2,3]],[])
        sage: suitable_element_of_Kz(K,S)
            ValueError: K contains the 3rd root of unit
    """    
    
    RK = PolynomialRing(K,'y')

    if not RK([3,0,1]).is_irreducible():
        raise ValueError('K contains the 3rd root of unity')
    
    Kz = K.extension(RK([3,0,1]),'b')
    K_selmer_basis = K.selmer_group(S,3)
    Sz = sum([Kz.primes_above(p) for p in S],[])
    Kz_selmer_basis = Kz.selmer_group(Sz,3)
    M = matrix(Integers(3),len(Kz_selmer_basis),len(K_selmer_basis))
    for i,c in enumerate(Kz_selmer_basis):
        M[i] = list_selmer_group(K(c.relative_norm()),S,3)
    ker = M.kernel()
    T = []
    V = []

    for j,vec in enumerate(cartesian_product_iterator([xrange(3)]*len(ker.basis()))):
        v = sum([i * e for i,e in zip(vec,ker.basis())])
        if  not v.is_zero() and v not in V:
            V.append(2*v)
            a = prod([s**t for s,t in zip(Kz_selmer_basis,v)])
            f = RK([- a.relative_norm(),0,0,1])
            roots = f.roots()

            if len(roots) > 0:
                b = roots[0][0]
                T.append([b,a.trace(a.parent().base_field())])
    return T


def full_selmer_group(K,S,n):
    r"""
    
    INPUT:
        - ``K`` : a number field
        - ``S`` : a list of prime ideals of K
        - ``n`` : a natural number
        
    OUTPUT:
        A list of representatives of the Selmer group `K(S,n)`
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x-1)
        sage: S = sum([K.primes_above(p) for p in [2,3]],[])
        sage: [a.factor() for a in full_selmer_group(K,S,2)]
            [1, -1, 3, (-1) * 3, 2, (-1) * 2, 2 * 3, (-1) * 2 * 3]
        sage: S = sum([K.primes_above(p) for p in [2,5]],[])
        sage: [a.factor() for a in full_selmer_group(K,S,3)]
            [1, 5, 5^2, 2, 2 * 5, 2 * 5^2, 2^2, 2^2 * 5, 2^2 * 5^2]
            
        sage: K.<a> = NumberField(x^2-6)
        sage: S = sum([K.primes_above(p) for p in [2,3]],[])
        sage: full_selmer_group(K,S,2)
            [1, 2*a - 5, -1, -2*a + 5, a + 3, a - 3, -a - 3, -a + 3, a - 2, -9*a + 22, -a + 2, 9*a - 22, a, -5*a + 12, -a, 5*a - 12]
    """
                  
    Sel = K.selmer_group(S,n)
    list = [prod([s**t for t,s in zip(v,Sel)]) for v in cartesian_product_iterator([xrange(n)]*len(Sel))]
    
    #We want each element to appear only once
    
    sel = []
    for a in list:
        if a not in sel:
            sel.append(a)
    return sel


def modified_selmer_group_c3(K,S):
    r"""
    
    INPUT:
        - ``K`` : a number field such that `\zeta_3\in K`
        - ``S`` : a list of prime ideals of `K`
    
    OUTPUT:
        A list of elements in `K` such that for two elements `a,b` of the list it holds `K(\sqrt[3]{a})\neq K(\sqrt[3]{b})` 
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^2+3)
        sage: S = sum([K.primes_above(p) for p in [2,5]],[])
        sage: modified_selmer_group_c3(K,S)
            [-1/2*a + 1/2, 5, -5/2*a + 5/2, -5/2*a - 5/2, 2, -a + 1, -a - 1, 10, -5*a + 5, -5*a - 5, 50, -25*a + 25, -25*a - 25]
            
        sage: K.<a> = NumberField(x-1)
        sage: S = sum([K.primes_above(p) for p in [2,3]],[])
        sage: modified_selmer_group_c3(K,S)
            ValueError: The 3-rd root of unity does not lie in K
    """
    RK = PolynomialRing(K,'y')
    if RK([3,0,1]).is_irreducible():
        raise ValueError('The 3-rd root of unity does not lie in K')
    
    Sel = K.selmer_group(S,3)
    elements = []
    temp = []
    for v in cartesian_product_iterator([Integers(3)]*len(Sel)):
        v = vector(v)
        if v not in temp and 2 * v not in temp:
            elements.append(prod([b**e for b,e in zip(Sel,v)]))
            temp.append(v)
            temp.append(2*v)
    
    return [b for b in elements if b != 1]
       
    
def quadratic_extensions(K,S):
    r"""
    
    INPUT:
        - ``K`` : a number field
        - ``S`` : a list of prime ideals of `K`
        
    OUTPUT:
        A list of all quadratic extensions of `K` unramified outside `S`
    
    EXAMPLE::
        
        sage: K.<a> = NumberField(x-1)
        sage: S = sum([K.primes_above(p) for p in [2]],[])
        sage: quadratic_extensions(K,S)
            [Number Field in c2 with defining polynomial x^2 + 1 over its base field, 
            Number Field in c2 with defining polynomial x^2 - 2 over its base field, 
            Number Field in c2 with defining polynomial x^2 + 2 over its base field]    
        sage: S = sum([K.primes_above(p) for p in [3,5]],[])
        sage: quadratic_extensions(K,S)
            [Number Field in c2 with defining polynomial x^2 - 5 over its base field, 
            Number Field in c2 with defining polynomial x^2 + 3 over its base field, 
            Number Field in c2 with defining polynomial x^2 + 15 over its base field]
            
        sage: K.<a> = QuadraticField(-1)
        sage: S = sum([K.primes_above(p) for p in [2,3]],[])
        sage: S
            [Fractional ideal (a + 1), Fractional ideal (3)]
        sage: for L in quadratic_extensions(K,S):
        sage:     L.relative_discriminant().factor()
            (Fractional ideal (a + 1))^4
            Fractional ideal (3)
            (Fractional ideal (a + 1))^4 * (Fractional ideal (3))
            (Fractional ideal (a + 1))^5
            (Fractional ideal (a + 1))^5
            (Fractional ideal (a + 1))^5 * (Fractional ideal (3))
            (Fractional ideal (a + 1))^5 * (Fractional ideal (3))
    """
    
    #We enumerate the 2-Selmer group of K for the set of primes S
                          
    Sel = full_selmer_group(K,S,2)
    
    #we create all possible C2 extensions
    
    candidates = []
    t = PolynomialRing(K,'t').gen()
    for s in Sel:
        if s != 1:
            L = K.extension(t**2 - s,'c2')
            candidates.append(L)          
    
    #We check which fields in 'candidates' have discriminant that is divisible by primes not in 'S'.
                                  
    quadratic_extensions = []
    for L in candidates:       
        if len([I[0] for I in L.relative_discriminant().factor() if I[0] not in S]) == 0:
            quadratic_extensions.append(L)
            
    return quadratic_extensions


def c3_z3_in(K,S):
    r"""
    
    INPUT:
        - ``K`` : a number field such that `\zeta_3\in K`
        - ``S`` : a list of prime ideals of `K`
        
    OUTPUT:
        A list with all cubic extensions of `K` unramified outside of `S`.
        
    COMMENT:
        `K` should contain `\zeta_3`.
        
    EXAMPLE::
        
        sage: K.<a> = QuadraticField(-3)
        sage: S = sum([K.primes_above(p) for p in [3]],[])
        sage: S
            [Fractional ideal (-a)]
        sage: for L in c3_z3_in(K,S):
        sage:     L.relative_discriminant().factor()
            (Fractional ideal (-a))^6
            (Fractional ideal (-a))^8
            (Fractional ideal (-a))^8
            (Fractional ideal (-a))^8
            
        sage: K.<a> = NumberField(x-1)
        sage: S = sum([K.primes_above(p) for p in [2,3]],[])
        sage: c3_z3_in(K,S)
            ValueError: K does not contain the 3-rd root of unity
    """
    
    RK = PolynomialRing(K,'t')
    if RK([3,0,1]).is_irreducible():
        raise ValueError('K does not contain the 3-rd root of unity')
    
    #we enumerate all elements of the 3-Selmer group of K which give different cubic extensions
                          
    Sel = modified_selmer_group_c3(K,S)
    
    #We check which fields in 'candidates' have discriminant that is divisible by primes not in 'S'.
                                  
    cubic_extensions = []

    for s in Sel:
        L = K.extension(RK.gen()**3 - s,'c3')
        if K.ideal(L.relative_discriminant()).is_S_unit(S = S):
            cubic_extensions.append(L)
            
    return cubic_extensions


def c3_z3_not(K,S):
    r"""
    
    INPUT:
        - ``K`` : a number field such that `\zeta_3\not\in K`
        - ``S`` : a list of prime ideals of `K`
       
    OUTPUT:
        A list with all cubic extensions of `K` unramified outside `S` which have zero defining coefficient
        in their defining polynomial and a list of the same extensions with a defining polynomial with `nice'
        coefficients.
    
    EXAMPLE::
        
        sage: K.<a> = NumberField(x-1)
        sage: S = sum([K.primes_above(p) for p in [2,3]],[])
        sage: c3_z3_not(K,S)
            [Number Field in c3 with defining polynomial x^3 - 3*x - 1 over its base field]
            
        sage: K.<a> = QuadraticField(-2)
        sage: S = sum([K.primes_above(p) for p in [2,5]],[])
        sage: S
            [Fractional ideal (a), Fractional ideal (5)]
        sage: for L in c3_z3_not(K,S):
        sage:    L.relative_discriminant().factor(),L.is_galois_relative()
            (Fractional ideal (5))^2 True
    """

    RK = PolynomialRing(K,'t')
    T = suitable_element_of_Kz(K,S)
    SQ = []
    for prime in S:
        p = prime.smallest_integer()
        if p not in SQ:
            SQ.append(p)

    cubic_extensions = []
    j = 0
    for beta,trace in T:
        #we evaluate a 3 degree polynomial 'g'

        g = RK([-trace,-3*beta,0,1])

        #if 'g' is irreducible and its relative discriminant is a S unit then it is a defining
        # polynomial for a possible extension

        if g.is_irreducible():
            L = K.extension(g,'c3')

            if K.ideal(L.relative_discriminant()).is_S_unit(S = S):
                cubic_extensions.append(L)

    return cubic_extensions#,nice_cubic_extensions


def cubic_extensions(K,S):
    r"""
    
    INPUT:
        - ``K`` : a number field
        - ``S`` : a list of prime ideals of `K`
        
    OUTPUT:
        A list with all cubic extensions of `K` unramified outside `S`
        
    EXAMPLE::
        
        sage: K.<a> = QuadraticField(-2)
        sage: S = sum([K.primes_above(p) for p in [2,5]],[])
        sage: S
            [Fractional ideal (a), Fractional ideal (5)]
        sage: for L in cubic_extensions(K,S):
        sage:    L.relative_discriminant().factor(),L.is_galois_relative()
            (Fractional ideal (5))^2 True
            
        sage:K.<a> = NumberField(x-1)
        sage: S = sum([K.primes_above(p) for p in [2,3,5,7]],[])
        sage: for L in cubic_extensions(K,S):
        sage:     L.is_galois_absolute(),L.absolute_discriminant().factor()
            True 7^2
            True 3^4
            True 3^4 * 7^2
            True 3^4 * 7^2
    
        sage: K.<a> = QuadraticField(-3)
        sage: S = sum([K.primes_above(p) for p in [2,3]],[])
        sage: S
            [Fractional ideal (2), Fractional ideal (-a)]
        sage: for L in cubic_extensions(K,S):
        sage:     L.is_galois_relative(),L.relative_discriminant().factor()
            True (Fractional ideal (-a))^6
            True (Fractional ideal (-a))^8
            True (Fractional ideal (-a))^8
            True (Fractional ideal (-a))^8
            True (Fractional ideal (2))^2 * (Fractional ideal (-a))^4
            True (Fractional ideal (2))^2 * (Fractional ideal (-a))^6
            True (Fractional ideal (2))^2 * (Fractional ideal (-a))^6
            True (Fractional ideal (2))^2 * (Fractional ideal (-a))^8
            True (Fractional ideal (2))^2 * (Fractional ideal (-a))^8
            True (Fractional ideal (2))^2 * (Fractional ideal (-a))^8
            True (Fractional ideal (2))^2 * (Fractional ideal (-a))^8
            True (Fractional ideal (2))^2 * (Fractional ideal (-a))^8
            True (Fractional ideal (2))^2 * (Fractional ideal (-a))^8
    """
    RK = PolynomialRing(K,'t')
    if RK([3,0,1]).is_irreducible():
        return c3_z3_not(K,S)
    else:
        return c3_z3_in(K,S)


def s3_extensions(K,S):
    r"""
    
    INPUT:
        - ``K`` : a number field `K`
        - ``S`` : a list of prime ideals of `K`
        
    OUTPUT:
        - A list of cubic polynomial with coefficients in `K` which have as a splitting field a `S_3` Galois extension of `K` unramified outside `S`.
        - The splitting fields of the polynomials
        - All the qudratic extensions of `K` unramified outside `S`
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x-1)
        sage: S = sum([K.primes_above(p) for p in [3]],[])
        sage: s3_extensions(K,S)
            [[x^3 + 9], [Number Field in c3 with defining polynomial x^3 + c2 over
            its base field], [Number Field in c2 with defining polynomial x^2 + 3
            over its base field]]
            
        sage: K.<a> = NumberField(x-1)
        sage: S = sum([K.primes_above(p) for p in [2]],[])
        sage: s3_extensions(K,S) 
            [[], [], [Number Field in c2 with defining polynomial x^2 + 1 over its
            base field, Number Field in c2 with defining polynomial x^2 - 2 over its
            base field, Number Field in c2 with defining polynomial x^2 + 2 over its
            base field]]
            
        sage: K.<a> = NumberField(x^2-2)
        sage: S = sum([K.primes_above(p) for p in [3]],[])
        sage: s3_extensions(K,S)  
            [[x^3 - a - 1, x^3 + 18*a + 27, x^3 + 9, x^3 - 9*a - 9], [Number Field
            in c3 with defining polynomial x^3 - a - 1 over its base field, Number
            Field in c3 with defining polynomial x^3 + (2*a + 3)*c2 over its base
            field, Number Field in c3 with defining polynomial x^3 - c2 over its
            base field, Number Field in c3 with defining polynomial x^3 + (-a -
            1)*c2 over its base field], [Number Field in c2 with defining polynomial
            x^2 + 3 over its base field]]
    """
    RK = PolynomialRing(K,'t')
    
    #we evaluate all quadratic extensions of K unramified outside S

    quadratic = quadratic_extensions(K,S)
    polynomials = []
    fields = []
    for M in quadratic:
        g = [e for e in M.automorphisms() if e(M.gen()) != M.gen()][0]  #the generator of Gal(M/K)
        SM = sum([M.primes_above(p) for p in S],[])                   

        cubics = cubic_extensions(M,SM) #all the cubic extensions of M unramified outside SM
        eKM = [e for e in K.embeddings(M) if e.preimage(M(K.gen())) == K.gen()][0] #the compatible embbeding of K in M

        #we check when L is an S3 extension and we give a 3-degree polynomial over K such that its splitting is L. By

        for L in cubics:
            f = L.defining_polynomial()
            # print f.discriminant().is_square(), L.is_galois_relative()
            #by construction the quadratic coefficient of f is 0. The coefficients of 'f' and 'f_bar'
            
            f0 = f[0]                        
            f1 = f[1]
            f0bar = g(f0)
            f1bar = g(f1)
            
            #the case when f has coefficients in K
            
            if f0bar == f0 and f1bar == f1:
                f0 = eKM.preimage(f0)
                f1 = eKM.preimage(f1)
                f = RK([f0,f1,0,1])

                #it can not evaluate f.discriminant() if K has absolute degree 1
                if K.absolute_degree() == 1:
                    f = f.change_ring(QQ)

                #if the discriminant of f is not a square we have a S3 extension
                if not f.discriminant().is_square():
                    #we make a `nice' choice of defining polynomials

                    fields.append(L)
                    polynomials.append(f)
            else:              

                #f doesn't have coefficients in K
                
                RL = PolynomialRing(L,'p')
                fbar = RL([f0bar,f1bar,0,1]) #the conjugate of f

                #if fbar is not irreducible in L[x] then the extension is Galois

                if not fbar.is_irreducible():
                    
                    #we evaluate the sum of a root of f and a root of fbar such that the sum is not 0

                    rf = f.change_ring(L).roots()
                    rfbar = fbar.roots()

                    r = rf[0][0]+rfbar[0][0]
                    if r.is_zero():
                        #we take an other root of rfbar for which we have proved that r!=0
                        r = rf[0][0]+rfbar[1][0]
                        
                    #h is a 3-degree polynomial and should have coefficients in K
                                  
                    h = r.minpoly()
                    if g(h[2]) == h[2] and g(h[1]) == h[1] and g(h[0]) == h[0]:
                        
                        h0 = eKM.preimage(h[0])
                        h1 = eKM.preimage(h[1])
                        h2 = eKM.preimage(h[2])
                        h = RK([h0,h1,h2,1])
                        
                        if K.absolute_degree() == 1: #it can not evaluate f.discriminant() if K has absolute degree 1
                            h = h.change_ring(QQ)
                        
                        #we check if the discriminant of 'h' is not a square

                        if not h.discriminant().is_square():
                            #we make a `nice' choice of defining polynomials

                            fields.append(M.extension(h,'c3'))
                            polynomials.append(h)
             
    return polynomials, fields, quadratic


def reduced_defining_polynomial(L):
    r"""

    INPUT:
        - ``L`` : a number field

    OUTPUT:

        A defining polynomial of ``L`` with nicer defining polynomial.
    """

    K = L.base_field()
    RQ = PolynomialRing(QQ,'x')
    fabs = RQ(pari(L).nfinit(3)[0][0].list())

    for fac in fabs.change_ring(K).factor():
        L1 = K.extension(fac[0],'b')
        if L1.is_isomorphic_relative(L):
            return fac[0]


def two_division_fields(K,S):
    r"""
    
    INPUT:
        - ``K`` : a number field
        - ``S`` : a list of prime ideals of `K`
        
    OUTPUT:
        - ``c2`` : a list of quadratic extensions of `K` unramified outside `S`
        - ``c3`` : a list of cubic extensions of `K` unramified outside `S`
        - ``s3_polynomials`` : a list of cubic polynomials with coefficients in `K` which have splitting field an `S_3` extension of `K` unramified outside `S`
        - ``s3`` : a list of `S_3` extensions of `K` unramified outside `S`
    
    EXAMPLE::
        
        sage: K.<a> = NumberField(x-1)
        sage: S = sum([K.primes_above(p) for p in [2]],[])
        sage: two_division_fields(K,S)
            ([Number Field in c2 with defining polynomial x^2 + 1 over its base
            field, Number Field in c2 with defining polynomial x^2 - 2 over its base
            field, Number Field in c2 with defining polynomial x^2 + 2 over its base
            field], [], [], [])
        sage: S = sum([K.primes_above(p) for p in [2,5]],[])
        sage: two_division_fields(K,S)
            ([Number Field in c2 with defining polynomial x^2 + 1 over its base
            field, Number Field in c2 with defining polynomial x^2 - 5 over its base
            field, Number Field in c2 with defining polynomial x^2 + 5 over its base
            field, Number Field in c2 with defining polynomial x^2 - 2 over its base
            field, Number Field in c2 with defining polynomial x^2 + 2 over its base
            field, Number Field in c2 with defining polynomial x^2 - 10 over its
            base field, Number Field in c2 with defining polynomial x^2 + 10 over
            its base field], [], [x^3 + 45*x + 270], [Number Field in c3 with
            defining polynomial x^3 + 15*x - 40*c2 over its base field])
        sage: S = sum([K.primes_above(p) for p in [2,3]],[])
        sage: two_division_fields(K,S)
            ([Number Field in c2 with defining polynomial x^2 + 1 over its base
            field, Number Field in c2 with defining polynomial x^2 - 3 over its base
            field, Number Field in c2 with defining polynomial x^2 + 3 over its base
            field, Number Field in c2 with defining polynomial x^2 - 2 over its base
            field, Number Field in c2 with defining polynomial x^2 + 2 over its base
            field, Number Field in c2 with defining polynomial x^2 - 6 over its base
            field, Number Field in c2 with defining polynomial x^2 + 6 over its base
            field], [Number Field in c3 with defining polynomial x^3 - 3*x - 1 over
            its base field], [x^3 - 3*x - 14, x^3 - 2, x^3 + 9, x^3 + 18, x^3 + 36,
            x^3 - 9*x + 18, x^3 - 18*x + 24, x^3 + 3*x + 2], [Number Field in c3
            with defining polynomial x^3 + 3*c2*x + c2 - 1 over its base field,
            Number Field in c3 with defining polynomial x^3 - 2 over its base field,
            Number Field in c3 with defining polynomial x^3 + c2 over its base
            field, Number Field in c3 with defining polynomial x^3 + 2*c2 over its
            base field, Number Field in c3 with defining polynomial x^3 + 4*c2 over
            its base field, Number Field in c3 with defining polynomial x^3 - 3*x -
            2*c2 over its base field, Number Field in c3 with defining polynomial
            x^3 + (-3*c2 - 9)*x + 5*c2 + 12 over its base field, Number Field in c3
            with defining polynomial x^3 + 3*x + 2 over its base field])
    """
    c3 = cubic_extensions(K,S)

    s3_polynomials,s3,c2 = s3_extensions(K,S)

    #we make reduction theory in the defining polynomials

    return c2,c3,s3_polynomials,s3

