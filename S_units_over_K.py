###### INITIAL BOUND ######


def round(a):
    r"""
    
    INPUT:
        - ``a`` : a real number
       
    OUTPUT:
        The closest integer to ``a``
    """

    if a == Infinity or a == -Infinity:
        raise ValueError("Infinity and an input")

    if a in ZZ:
        return a
    else:
        return a.round()


def modified_height_infinite_case(a,place):
    r"""
    
    INPUT:
        - ``a`` : an element of the number field `K`
        - ``place`` (ring morphism): an infinite place of `K`
    
    OUTPUT:
        The modified absolute height for `a` as it is defined in the reference
        
    REFERENCE:
        A. Baker and G. Wustholz. Logarithmic forms and group varieties. J. Reine Angew. Math., 442:19-62, 1993.
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^2-2)
        sage: place = K.places()[0]
        sage: modified_height_infinite_case(a,place)
            1.580325730234823217013360503412    
        sage: modified_height_infinite_case(0,place)
            ValueError: a has not to be 0 or 1
            
        sage: K.<a> = NumberField(x-1)
        sage: place = K.places()[0]
        sage: modified_height_infinite_case(5,place)
            1.609437912434100374600759333226
    """
    
    if a == 0 or a == 1:
        raise ValueError('a has not to be 0 or 1')

    precision = place.codomain().precision()
    K = place.domain()
    a = K(a)
    d = K.absolute_degree()
    height  = max([d*(a.global_height(place.codomain().precision())),log(place(a)).abs(),1])/d
    if RR(height) == Infinity:
        return modified_height_infinite_case(a,higher_precision(place,2*precision))
    return max([d*(a.global_height(place.codomain().precision())),log(place(a)).abs(),1])/d
    

def e_s_real(a,place):
    r"""
    
    INPUT: 
        - ``a`` : an element of a number field `K`
        - ``place`` (ring morphism): an real place of `K`
        
    OUTPUT:
        Reurn `a` if `place(a)>=0`, otherwise `-a`
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^4-7)
        sage: place = K.places()[0]
        sage: e_s_real(a,place)
            -a
        sage: e_s_real(-a,place)
            -a
        sage: place(a)
            1.626576561697785743211232345494
    """
    
    if place(a) < 0:
        return (-1)*a
    else:
        return a
 
    
def Baker_Wustholz_low_lattice_bound(A,place):
    r"""
    
    INPUT:
        - ``A`` : a list of elements of a number field `K`
        - ``place`` (ring morphism): an infinite place of `K`
    
    OUTPUT:
        The constant of the low bound of the main theorem(page 20) of the reference
        
    REFERENCE:
        A. Baker and G. Wustholz. Logarithmic forms and group varieties. J. Reine Angew. Math., 442:19-62, 1993.
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^2-7)
        sage: place = K.places()[0]
        sage: Baker_Wustholz_low_lattice_bound([a,a^2+1],place)
            4.956654367093510940632396859094e10*log(8)
    """
    
    if len(A) == 0:
        raise ValueError('The list A is empty')
    
    d = A[0].parent().absolute_degree()
    n = len(A)
    c = 18*(factorial(n+1))*n**(n+1)*(32*d)**(n+2)*log(2*n*d)

    return c*prod([modified_height_infinite_case(a,place) for a in A])
    

def a_basis_with_0_order_at_p(prime,G):
    r"""
    
    INPUT:
        - ``prime`` : a prime ideal of a number field `K`
        - ``G`` : a list of generators of a subgroup of `K^*`
        
    OUTPUT:
        - ``M0`` : a list of elements in `K^*` which contains all `\mu_0` that can appear to lemma IX.3 page 139 of the reference
        - ``M`` : a list of elements in `K^*` which contains all `\mu_i` for `i>0` that appear to lemma IX.3 page 139 of the reference
        -  the index of the generator in ``G`` which has the property as it is defined in lemma IX.3 page 139 of the reference
    REFERENCE:
        Nigel P. Smart. The Algorithmic Resolution of Diophantine Equations. Number 41 in Students Texts. London Mathematical Society, 1998.
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^2+5)
        sage: SK = K.primes_above(30)
        sage: prime = K.prime_above(7)
        sage: SuK = K.S_unit_group(S = SK)
        sage: G = SuK.gens_values()
        sage: M0, M ,k= a_basis_with_0_order_at_p(prime,G)
        sage: G
            [-1, 2, a + 1, a - 1, -a]
        sage: M0,M,k
            ([-1, 1], [2, a + 1, a - 1, -a])
        sage: prime = K.prime_above(5)
        sage: a_basis_with_0_order_at_p(prime,G)
            ([-1, 1], [2, a + 1, a - 1])
    """ 
    K = prime.ring() 
    g0 = [g for g in G if g.multiplicative_order() != Infinity]
    Gfree = [g for g in G if g.multiplicative_order() == Infinity]
    if len(g0) ==1:
        g0 = g0[0]
    else:
        g0 = K(1)
    
    if len(Gfree) == 0:
        raise ValueError('The group does not have free part')
    if g0 == 0 or len([g for g in Gfree if g == 0]) != 0:
        raise ValueError('Either g0 = 0 or there is a zero element in G')
           
    e = prime.absolute_ramification_index()
    f = prime.residue_class_degree()
    ordprime = lambda x: x.valuation(prime)
    
    
    N = [ordprime(K(g)) for g in Gfree]        #N has the valuations of G
    n_k = min(N)

    #we check if our initial basis satisfies the condition ord(g0)=0 and ord(g)=0 for eacj g in Gfree
    
    if len([a for a in N if a != 0]) == 0:
        return [-g0**i for i in range(g0.multiplicative_order())],Gfree,0
    
    #In the following lines we evaluate sigma,n_k and the other parameters that appear in Lemma IX.3 of reference
        
    N_abs = [a.abs() for a in N]
    n_k_abs = min([a for a in N_abs if a > 0])
    k = N_abs.index(n_k_abs)
    n_k = N[k]
    N2 = [N[i] for i in range(len(N)) if i != k]   #N2 has all n_i except for that one with minimal absolute value.
    G2 = [Gfree[i] for i in range(len(Gfree)) if i != k]   #G2 has all the generator excepr for that one associate to n_k
    
    M0 = []
    for vec in cartesian_product_iterator([xrange(n_k_abs)]*len(N2)):
        sigma = -(vector(vec)*vector(N2))
        if sigma % n_k == 0:
            for g in [g0**i for i in range(g0.multiplicative_order())]:
                m0 = -g * prod([a**b for a,b in zip(G2,vec)]) * Gfree[k]**(sigma/n_k)
                if m0 not in M0:
                    M0.append(m0)
    return M0,[(g**n_k)*(Gfree[k]**(-n)) for g,n in zip (G2,N2)],k+1


def upper_bound_modified_height_finite_case(a,embeddings,prime):
    r"""
    
    INPUT:
        - ``a`` : an element of a number field `K`
        - ``embeddings`` : a list of all embeddings of `K` to `\mathbb C`
        - ``prime`` : a prime ideal of `K`
        
    OUTPUT:
        An upper bound for the modified height with respect to `prime`. See the appendix of the reference
    
    REFERENCE:
        N. Tzanakis and B. M. M. De Weger. Solving a specific Thue-Mahler equation. Mathematics of Computation, 57(196):799-815, 1991.
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^2+5)
        sage: prime = K.prime_above(2)
        sage: em = K.embeddings(ComplexField(100))
        sage: upper_bound_modified_height_finite_case(a^4,em,prime)
            3.2188758248682007492015186665
    """
        
    K = prime.ring()
    p = prime.absolute_norm().factor()[0][0]
    f = prime.residue_class_degree()
    d = K.absolute_degree()
    prec = embeddings[0].codomain().precision()
    
    t = polygen(K)
    if ( p > 2 and not (t**2+1).is_irreducible() ) or ( p == 2 and  not (t**2+3).is_irreducible() ):
        D = d
    else:
        D = 2*d
    height = max([a.global_height(prec),max([log(em(a)).abs() for em in embeddings])/(2*pi*D),(f*log(p))/d])
    if RR(height) == Infinity:
        return upper_bound_modified_height_finite_case(a,[higher_precision(em,2*prec) for em in embeddings],prime)
    return max([a.global_height(prec),max([log(em(a)).abs() for em in embeddings])/(2*pi*D),(f*log(p))/d])


def Yu_theorem(A,prime,embeddings):
    r"""
    
    INPUT:
        - ``A`` : a list of elements of a number field `K`
        - ``prime`` : a prime ideal of `K`
        - ``embeddings`` : a list of all embeddings of `K` to `\mathbb C`
        
    OUTPUT:
        `(C_1C_2C_3 , C_1C_2C_3C_4)`, where `C_1, C_2, C_3` and `C_4` are defined in the theorem of the appendix of the
        reference.
        
    REFERENCE:
         N. Tzanakis and B. M. M. De Weger. Solving a specific Thue-Mahler equation. Mathematics of Computation,
         57(196):799-815, 1991.
         
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^3 - 3*x - 1)
        sage: em = K.embeddings(ComplexField(50))
        sage: Yu_theorem(K.S_unit_group(S=K.primes_above(6)).gens_values(),em,K.prime_above(7))
            (1063465350238590566400000000000*log(2654208*log(7))/log(7),
            2126930700477181132800000000000*log(6)*log(2654208*log(7))/log(7))
    """    
    if len(A) == 0:
        raise ValueError('The list A is empty')
    
    if len([a for a in A if a.valuation(prime) != 0]) != 0:
        raise ValueError('There is an element in A which does not have 0 valuation')
    
    K = prime.ring()
    d = K.absolute_degree()
    t = polygen(K)
    p = prime.absolute_norm().factor()[0][0]   #p is the prime integer below 'prime'
    n = len(A)
    f = prime.residue_class_degree()
    
    D = 2*d
    if ( p > 2 and not (t**2+1).is_irreducible() ) or ( p == 2 and  not (t**2+3).is_irreducible() ):
        D = d
    
    #we evaluate the constants C1, C2, C3, C4 that appear on the theorem we mentioned 
    
    if p % 4 == 1:
        c1 = 35009 * (45/2)**n;
    elif p % 4 == 3:
        c1 = 30760 * 25**n;
    else:
        c1 = 197142 * 36**n;
    
    c4 = 2 * log(D)
    v = [upper_bound_modified_height_finite_case(a,embeddings,prime) for a in A]
    V = max(v)
    
    if p != 2:
        c3 = log( 2**11 * (n+1)**2 * D**2 * V )
    else:
        c3 = log( 3 * 2**10 * (n+1)**2 * D**2 * V )
    c2 = (n+1)**(2*n+4) * p**((D*f)/d) * (f*log(p))**(-n-1) * D**(n+2) * prod(v)

    return c1*c2*c3,c1*c2*c3*c4


def higher_precision(place,new_prec):
    r"""
    
    INPUT:
        - ``place`` (ring morphism): an infinite place of a number field `K`
        - ``new_prec`` : the new precision
        
    OUTPUT:
        The ``place`` but with precision equal with ``new_prec``
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^2-2)
        sage: place = K.places()[0]
        sage: place
            Ring morphism:
              From: Number Field in a with defining polynomial x^2 - 2
              To:   Real Field with 106 bits of precision
              Defn: a |--> -1.414213562373095048801688724210
        sage: higher_precision(place,50)
            Ring morphism:
              From: Number Field in a with defining polynomial x^2 - 2
              To:   Real Field with 50 bits of precision
              Defn: a |--> -1.4142135623731
              
        sage: K.<a> = NumberField(x^4-2)
        sage: place = K.places()[0]
        sage: place
            Ring morphism:
              From: Number Field in a with defining polynomial x^4 - 2
              To:   Real Field with 106 bits of precision
              Defn: a |--> -1.189207115002721066717492233629
        sage: higher_precision(place,150)
            Ring morphism:
              From: Number Field in a with defining polynomial x^4 - 2
              To:   Real Field with 150 bits of precision
              Defn: a |--> -1.1892071150027210667174999705604759152929721
    """
    K = place.domain()
    old_prec = place.codomain().precision()
    Kplaces = K.places(prec = new_prec)
    gens = K.gens()
    
    #Below we check which of the candidates in Kplaces has values quite close to the initial place.
    
    i = 1
    while i <= old_prec:
        Q = [q for q in Kplaces if len([0 for a in gens if (q(a)-place(a)).abs() <= 2**(-i)]) == len(gens)]
        if len(Q) == 1:
            return Q[0]
        else:
            i += 1
    if i > old_prec:
        raise ValueError('I cannot find the place')
    

def is_real_place(place):
    r"""
    
    INPUT:
        - ``place`` (ring morphism): an infinite place of a number field `K`
        
    OUTPUT:
        `True` if it a real place, otherwise `False`
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^4-2)
        sage: place = K.places()[0]
        sage: place
            Ring morphism:
              From: Number Field in a with defining polynomial x^4 - 2
              To:   Real Field with 106 bits of precision
              Defn: a |--> -1.189207115002721066717492233629
        sage: is_real_place(place)
            True
    """
    prec = place.codomain().precision()
    if place.codomain() == RealField(prec):
        return True
    else:
        return False
    

def reduction_step_real_case(place,B0,G,c7):
    r"""
    
    INPUT:
        - ``place`` (ring morphism): an infinite place of a number field `K`
        - ``B0`` : the initial bound
        - ``G`` : a set of generators of the free part of the group
        - ``c7`` : a positive real number
        
    OUTPUT:
        - a new upper bound 
        - ``True`` if we have to increase precision, otherwise ``False``
        
    COMMENT:
        The constant ``c7`` in the reference page 137
        
    REFERENCE:
         Nigel P. Smart. The Algorithmic Resolution of Diophantine Equations. Number 41 in Students Texts.
         London Mathematical Society, 1998.
         
    EXAMPLE::
        
        sage: K.<a> = NumberField(x**3-2)
        sage: SK = sum([K.primes_above(p) for p in [2,3,5]],[])
        sage: G = [g for g in K.S_unit_group(S = SK).gens_values() if g.multiplicative_order() == Infinity]
        sage: p1 = K.real_places(prec = 200)[0]
        sage: reduction_step_real_case(p1,10**10,G,2)
            (54,False)
    """   
    n = len(G)
    Glog = [log(place(e_s_real(g,place))) for g in G]
    if len([1 for g in G if place(e_s_real(g,place)).is_zero()]) > 0:
        return 0,True

    #We choose the initial value of C such that the vector v not to have 0 everywhere
    C = round(max([1/l.abs() for l in Glog if l != 0])+1)
    
    #if the precision we have is not high enough we have to increase it and evaluate c7 again
    if place.codomain().precision() < log(C)/log(2):
        return 0,True

    S = (n-1) * (B0)**2
    T = (1 + n * B0)/2
    finish = False
    while  not finish:
        A = copy(identity_matrix(ZZ,n))
        v = vector([round(g*C) for g in Glog])
        
        if v[n-1] == 0: #we replace the last element of v with an other non zero
            k = [i for i,a in enumerate(v) if not a.is_zero()][0]
            v[n-1] = v[k]
            v[k] = 0
        A[n-1] = v
        
        #We have to work with rows because of the .LLL() function
        
        A = A.transpose()
        y = copy(zero_vector(ZZ,n))
        l = minimal_vector(A,y)
             
        #On the following lines I apply Lemma VI.1 from Smart's book page 83
        
        if l <= T**2 + S:
            C = 2 * C
            #Again if our precision is not high enough
            if place.codomain().precision() < log(C)/log(2):
                return 0,True
        else:
            if sqrt(l-S) - T > 0:
                return round((log(C * 2)-log(sqrt(l-S) - T))/c7),False
            else:
                return B0,False   
    

def reduction_step_complex_case(place,B0,G,g0,c7):
    r"""
    
    INPUT:
        - ``place`` (ring morphism): an infinite place of a number field `K`
        - ``B0`` : the initial bound
        - ``G`` : a set of generators of the free part of the group
        - ``g0`` : an element of the torsion part of the group
        - ``c7`` : a positive real number
        
    OUTPUT:
        - a new upper bound 
        - ``True`` if we have to increse precision, otherwise ``False``
        
    COMMENT:
        The constant ``c7`` in the reference page 138
        
    REFERENCE:
         Nigel P. Smart. The Algorithmic Resolution of Diophantine Equations. Number 41 in Students Texts. London Mathematical Society, 1998.
         
    EXAMPLE::
        
        sage: K.<a> = NumberField([x^3-2])
        sage: SK = sum([K.primes_above(p) for p in [2,3,5]],[])
        sage: G = [g for g in K.S_unit_group(S = SK).gens_values() if g.multiplicative_order() == Infinity]
        sage: p1 = K.places(prec = 100)[1]
        sage: reduction_step_complex_case(p1,10^5,G,-1,2)
            (18,False)
    """
    
    precision = place.codomain().precision()
    n = len(G)
    Glog_imag = [(log(place(g))).imag_part() for g in G]
    Glog_real = [(log(place(g))).real_part() for g in G]
    Glog_imag = Glog_imag + [2 * pi]
    Glog_real = Glog_real + [0]
    a0log_imag = (log(place(-g0))).imag_part()
    a0log_real = (log(place(-g0))).real_part()

    #the case when the real part is 0 for all log(a_i)
    
    pl = higher_precision(place,2 * place.codomain().precision())
    if len([g for g in G if (pl(g).abs()-1).abs() > 2**(-place.codomain().precision())]) == 0:
        
        #we have only imaginary numbers and we are in case 2 as Smart's book says on page 84

        C = 1#round(min((B0**n/100),max([1/l.abs() for l in Glog_imag if l != 0]+[0])))+1
        S = n * B0**2

        #if the precision we have is not high enough we have to increase it and evaluate c7 again
        # if precision < log(C)/log(2):
        #     return 0,True
        
        T = ((n+1) * B0 + 1)/2
        finish = False
        while not finish:
            A = copy(identity_matrix(ZZ,n+1))
            v = vector([round(g * C) for g in Glog_imag])
            
            if v[n] == 0:
                #we replace the last element of v with an other non zero

                k = [i for i,a in enumerate(v) if not a.is_zero()][0]
                v[n] = v[k]
                v[k] = 0
            A[n] = v

            if A.is_singular():
                C *= 2
            else:
                #We have to work with rows because of the .LLL() function

                A = A.transpose()
                y = copy(zero_vector(ZZ,n+1))
                y[n] = (-1) * round(a0log_imag * C)
                l = minimal_vector(A,y)

                #On the following lines I apply Lemma VI.1 of the reference page 83

                if l <= T**2 + S:
                    C = 2 * C

                    #The same as above if for the new C the precision is low
                    if precision < log(C)/log(2):
                       return 0,True
                else:
                    Bnew = round((log(C * 2)-log(sqrt(l-S)-T))/c7)
                    finish = True
                    if mod(y[n],A[n,n]) == 0:
                        return max(Bnew,(y[n]/A[n,n]).abs()),False
                    else:
                        return Bnew,False
        
    else:
        
        #the case when the real part is not 0 for all log(a_i)
        C = 1
        S = (n-1) * B0**2
        T = ((n+1)*B0+1)/sqrt(2)
        finish = False
        
        #we are relabeling the Glog_real and Glog_imag s.t. the condition Real(a_n)*Im(a_(n-1))-Real(a_(n-1))*Im(a_n)!=0 to be satisfied. See page 84 of the reference.
                
        k = [i for i in range(len(Glog_real)) if Glog_real[i] != 0][0]
        a = Glog_real[k]
        Glog_real[k] = Glog_real[n-1]
        Glog_real[n-1] = a
        
        a = Glog_imag[k]
        Glog_imag[k] = Glog_imag[n-1]
        Glog_imag[n-1] = a
        
        while not finish:

            A = copy(identity_matrix(ZZ,n+1))
            A[n-1] = vector([round(g * C) for g in Glog_real])
            A[n] = vector([round(g * C) for g in Glog_imag])

            if A.is_singular():
                C *= 2
            else:
                #On the following lines I apply Lemma VI.2 of the reference page 85

                A = A.transpose()
                y = copy(zero_vector(ZZ,n+1))
                y[n] = (-1) * round(a0log_imag * C)
                y[n-1] = (-1) * round(a0log_real*C)
                l = minimal_vector(A,y)


                if l <= T**2 + S:
                    C *= 2
                    #The same as above if for the new C the precision is low
                    if precision < log(C)/log(2):
                        return 0,True
                else:
                    Bnew = round((log(C * 2)-log(sqrt(l-S)-T))/c7)

                    #we take into account the second case of the theorem VI.2 of the reference page 85

                    M = matrix(ZZ,2,[A[n-1,n-1],A[n-1,n],A[n,n-1],A[n,n]])
                    b = vector(ZZ,2,[-y[n-1],-y[n]])
                    if M.determinant() == 1 or M.determinant() == -1:
                        x = M.inverse() * b
                        return max(Bnew,x[0].abs(),x[1].abs()),False
                    else:
                        return Bnew,False


def log_p_of_a_list(L,prime,precision):
    r"""
    
    INPUT:
        - ``L`` : a list of elements of a number field `K`
        - ``prime`` : a prime ideal of `K`
        - ``precision`` : a positive natural number
        
    OUTPUT:
        A list with the `\mathfrak p-adic` logarithms of ``L``    
        
    COMMENT:
        `K` has to be an absolute extension
        
    EXAMPLE::
        
        sage: K.<a> = QuadraticField(17)
        sage: p = K.prime_above(13); p
            Fractional ideal (a - 2)
        sage: log_p_of_a_list([3*a^3+1,2*a^2+a+7],p,20)
            [228743122076416000464228/13*a + 31623834113854898674930/13,
            182612486178943231909010/13*a + 188811596701233257654644/13]
    """
    K = prime.ring()
    if not K.is_absolute():
        raise ValueError('K has to be an absolute extension')

    return [log_p(a,prime,precision) for a in L]


def reduction_step_finite_case(prime,B0,M,M_logp,m0,c3,precision):
    r"""
    
    INPUT:
        - ``prime`` : a prime ideal of a number field `K`
        - ``B0`` : the initial bound
        - ``M`` : a list of elements of `K`
        - ``M_logp`` : the p-adic logarithm of elements in `K`
        - ``m0`` : an element of `K`
        - ``c3`` : a positive real constant
        - ``precision`` : the precision of the calculations
        
    OUTPUT:
        - a new upper bound 
        - ``True`` if we have to increase precision, otherwise ``False``
    
    COMMENT:
        The constant `c_5` is the constant `c_5` at the page 89 of the reference which is equal to the constant `c_{10}`
         at the page 139 of the reference.
        
    REFERENCE:
        Nigel P. Smart. The Algorithmic Resolution of Diophantine Equations. Number 41 in Students Texts.
        London Mathematical Society, 1998.
    """
    if len([g for g in M+[m0] if g.valuation(prime) != 0]) > 0:
        raise ValueError('There is an element with non zero valuation at prime')
    
    K = prime.ring()
    p = prime.absolute_norm().factor()[0][0]
    f = prime.residue_class_degree()
    e = prime.absolute_ramification_index()
    c5 = c3/(f * e * log(p))
    theta = K.gen()
    
    #if M is empty then it is easy to give an upper bound
    if len(M) == 0:
        if m0 != 1:
            return RR(max(log(p) * f * (m0-1).valuation(prime)/c3,0)).floor(),False
        else:
            return 0,False
    #we evaluate the p-adic logarithms of m0 and we embedd it in the completion of K with respect to prime

    m0_logp = log_p(m0,prime,precision)
    m0_logp = embedding_to_Kp(m0_logp,prime,precision)
    n = len(M_logp)
    #Below we implement paragraph VI.4.2 of the reference, pages 89-93
    
    #we evaluate the order of discriminant of theta
    
    Theta = [theta**i for i in range(K.absolute_degree())]
    ordp_Disc = (K.disc(Theta)).valuation(p)
    
    #We evaluate lambda
    
    c8 = min([min([a.valuation(p) for a in g]) for g in M_logp])
    l = p**c8
    
    #we apply lemma VI.5 of Smart's book page 90
    
    low_bound = round(1/c5)
    for a in m0_logp:
        if a != 0:
            if c8 > a.valuation(p):
                B1 = (c8 + ordp_Disc/2)/c5
                if B1 > low_bound:
                    return RR(B1).floor(),False
                else:
                    return low_bound,False
    
    c8 = min([a.valuation(p) for a in m0_logp]+[c8])
    B = [g/l for g in M_logp]
    b0 = m0_logp/l
    c9 = c8 + ordp_Disc/2

    #We evaluate 'u' and we construct the matrix A
    
    m = e * f
    u = 1
    finish = False
    while not finish:
        if u > (precision * log(2))/log(p):
            return 0,True
           
        #We construct the matrix A as a block matrix
        
        A11 = copy(identity_matrix(ZZ,n))
        A12 = copy(zero_matrix(ZZ,n,m))
        A21 = copy(zero_matrix(ZZ,n,m))
        A22 = p**u * copy(identity_matrix(ZZ,m))
        for i,b in enumerate(B):
            A21[i] = vector([mod(b[j],p**u) for j in range(m)])
        A = block_matrix([[A11,A12],[A21.transpose(),A22]])

        y = copy(zero_vector(ZZ,n+m))
        for i in range(m):
            y[i+n] = -mod(b0[i],p**u)
            
        l = minimal_vector(A.transpose(),y)
        if l > n * B0**2:
            B2 = (u + c9)/c5
            if B2 > low_bound:
                return RR(B2).floor(),False
            else:
                return low_bound,False
        else:
            u += 1


def c_constants(G,precision):
    r"""

    INPUT:
        - ``G`` : a list with the generators of the free part of a subgroup of `K^*`
        - ``precision`` : the precision

    OUTPUT:
        The constants `c_1,c_2,c_3` that appear on the page 136 of the reference with checking numerical mistakes

    REFERENCE:
        Nigel P. Smart. The Algorithmic Resolution of Diophantine Equations. Number 41 in Students Texts.
        London Mathematical Society, 1998.

    COMMENT:
        `K` has to be an absolute number field

    EXAMPLE::

        sage: K.<a> = NumberField(x^3-2)
        sage: S = K.primes_above(5)
        sage: G = [g for g in K.S_unit_group(S = S).gens_values() if g.multiplicative_order() == Infinity]
        sage: c_constants(G,50)
            (1.6094379124341, 0.6213349,3455961, 0.20504052840467)

        sage: K.<a> = NumberField(x^8 + 1)
        sage: g = K.gen()
        sage: G = [g^6+g^4+g^2,-(g^4+g^3+g^2),1+g^3-g^5,1-g]
        sage: c_constants(G,80)
            (1.4497321111770749035704, 0.68978261038039241636303, 0.170721196069147)
    """
    Real = RealField(prec = precision)
    c1, c2,c3 = c_constants_without_check(G,2 * precision)
    c1double, c2double,c3double = c_constants_without_check(G,2 * precision)
    if (c1-c1double).abs() > 1:
        c1,c2,c3 = c_constants(G,2 * precision)
        return Real(c1),Real(c2),Real(c3)
    else:
        return c1,c2,c3


def c_constants_without_check(G,precision):
    r"""
    
    INPUT:
        - ``G`` : a list with the generators of the free part of a subgroup of `K^*`
        - ``precision`` : the precision
    
    OUTPUT:
        The constants `c_1,c_2,c_3` that appear on the page 136 of the reference without checking numerical
        mistakes.
        
    REFERENCE:
        Nigel P. Smart. The Algorithmic Resolution of Diophantine Equations. Number 41 in Students Texts. London Mathematical Society, 1998.
    
    COMMENT:
        `K` has to be an absolute number field
            
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^3-2)
        sage: S = K.primes_above(5)
        sage: G = [g for g in K.S_unit_group(S = S).gens_values() if g.multiplicative_order() == Infinity]
        sage: c_constants(G,50)
            (1.6094379124341, 0.6213349,3455961, 0.20504052840467)
            
        sage: K.<a> = NumberField(x^8 + 1)
        sage: g = K.gen()
        sage: G = [g^6+g^4+g^2,-(g^4+g^3+g^2),1+g^3-g^5,1-g]
        sage: c_constants(G,80)
            (1.4497321111770749035704, 0.68978261038039241636303, 0.170721196069147)
    """
    if len(G) == 0:
        raise ValueError('G is empty')
    if len([g for g in G if g.multiplicative_order() != Infinity]) > 0:
        raise ValueError('G has an element with finite myltiplicative order')

    finiteSup,realSup,complexSup = support_of_G(G,precision)

    if len([s for s in realSup if not is_real_place(s)]) > 0:
        raise ValueError('realSup has a complex place')
    if len([s for s in complexSup if is_real_place(s)]) > 0:
        raise ValueError('complexSup has a real place')
    
    if len(realSup) > 0:
        K = realSup[0].domain()
        #infinite_prec = realSup[0].codomain().precision()
    elif len(complexSup) > 0:
        K = complexSup[0].domain()
        #infinite_prec = complexSup[0].codomain().precision()
    else:
        K = finiteSup[0].ring()

    A = copy(zero_matrix(RealField(precision),len(finiteSup)+len(complexSup)+len(realSup),len(G)))

    #we create the matrix which has as rows the logarithms of the absolute value with respect a place for the lements in G
    
    #finite places
    
    for i,p in enumerate(finiteSup):
        #we have to be careful with the logarithm of 1 because sometimes does not give 0
        
        v = [0] * len(G)
        for j,g in enumerate(G):
            if (K(g)).abs_non_arch(p,prec = precision) != 1:
                v[j] = log((K(g)).abs_non_arch(p,prec = precision))
        A[i] = vector(v)
    
    #real infinite places     
        
    for i,s in enumerate(realSup):
        v = [0] * len(G)
        vbar = [0] * len(G)
        for j,g in enumerate(G):
            if abs(s(g)) != 1:
                v[j] = log(abs(s(g)))
        A[i + len(finiteSup)] = vector(v)
    
    #complex infinite places    
    
    for i,s in enumerate(complexSup):
        v = [0] * len(G)
        vbar = [0] * len(G)
        for j,g in enumerate(G):
            if abs(s(g)) != 1:
                v[j] = 2 * log(abs(s(g)))
        A[i + len(finiteSup) + len(realSup)] = vector(v)

    #We find the minimum infinite norm of all the invertible submatrices of A 

    n = len(finiteSup) + len(complexSup) + len(realSup)
    s = Set(range(n))
    X = s.subsets(len(G)).list()
    c1 = -Infinity
    for g in X: 
        M = A[g.list(),:] #the submatrix associate to g
        d = M.determinant()
        #if the precision is high enough the determinant of M can not be 'quite small'

        if d > 2**(-RR(precision/2).floor()):
            B = M.inverse()
            a = max([sum([b.abs() for b in row]) for row in B.rows()])
            if a > c1:
                c1 = a

    c2 = 1/c1
    c3 = c2/len(G)
    c3 = (99 * c3)/100

    return c1,c2,c3


def initial_bound_real_case(G2free,place,c3):
    r"""
    
    INPUT:
        - ``G2free`` : the generator of the free part of a finitely generated subgroup of `K^*`, where `K` is a number field
        - ``place`` (ring morhpism) : an infinite real place of `K`
        - ``c3`` : is defined in the page 136 of the reference
        
    OUTPUT:
        An upper bound associate to ``place`` according to IX.1.1 of the reference page 137
    
    REFERENCE:
        Nigel P. Smart. The Algorithmic Resolution of Diophantine Equations. Number 41 in Students Texts. London Mathematical Society, 1998.
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^3-2)
        sage: p1,p2 = K.places(prec = 50)
        sage: S = K.primes_above(5)
        sage: G = [g for g in K.S_unit_group(S = S).gens_values() if g.multiplicative_order() == Infinity]
        sage: c3 = 99*c1_constant(G,S,[p1],[p2])/(100*len(G))
        sage: initial_bound_real_case(G,p1,c3)
            2.7776062935760e14*log(18)*log(1.3888031467880e14*log(18)) +
            3.7656662700583*log(2)
    """
    if not is_real_place(place):
        raise ValueError('place is not real')

    c5 = log(2)/c3
    c7 = c3
    c8 = Baker_Wustholz_low_lattice_bound([e_s_real(g,place) for g in G2free],place)

    return max([c5,(2 * (log(2) + c8 * log(c8/c7) ) )/c7,0])
    
    
def initial_bound_complex_case(G2free,place,g0,c3):
    r"""
    
    INPUT:
        - ``G2free`` : the generator of the free part of a finitely generated subgroup of `K^*`, where `K` is a number field
        - ``place`` (ring morhpism) : an infinite real place of `K`
        - ``g0`` : the generator of the torsion part of the group `G_2`
        - ``c3`` : is defined in the page 136 of the reference
    
    OUTPUT:
        An upper bound associate to ``place`` according to IX.1.2 of the reference page 138
    
    REFERENCE:
        Nigel P. Smart. The Algorithmic Resolution of Diophantine Equations. Number 41 in Students Texts. London Mathematical Society, 1998.
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^3-2)
        sage: p1,p2 = K.places(prec = 50)
        sage: S = K.primes_above(5)
        sage: G = [g for g in K.S_unit_group(S = S).gens_values() if g.multiplicative_order() == Infinity]
        sage: g0 = [g for g in K.S_unit_group(S = S).gens_values() if g.multiplicative_order() != Infinity][0]
        sage: c3 = 99*c1_constant(G,S,[p1],[p2])/(100*len(G))
        sage: initial_bound_complex_case(G,p2,g0,c3)
            2.0771265747068e23*log(30)*log(4) +
            2.0771265747068e23*log(30)*log(1.0385632873534e23*log(30)) +
            7.5313325401165*log(2)
    """
    if is_real_place(place):
        raise ValueError('place is not real')
    if g0.multiplicative_order() == Infinity:
        raise ValueError('g0 does not have finite multiplicative order')
    
    c5 = (2 * log(2))/c3
    c7 = c3/2
        
    #we find a bound for its element of the torsion part and we get the maximum among them
    
    Gtorsion = [g0**i for i in range(g0.multiplicative_order())]
    B = 0
    n = len(G2free)
    for ad in Gtorsion:
        if ad != -1:
            c8 = Baker_Wustholz_low_lattice_bound(G2free + [(-1) * ad,-1],place)
            B = max([c5,(2 * (log(2) + c8 * log(c8/c7) + c8 * log(n+1)) )/c7,B])
        else:
            c8 = Baker_Wustholz_low_lattice_bound(G2free + [-1],place)
            B = max([c5,(2 * (log(2) + c8 * log(c8/c7) + c8 * log(n+1)) )/c7,B])
        
    return B
    

def initial_bound_finite_case(G2free,prime,g0,c3,embeddings):
    r"""
    
    INPUT:
       - ``G2free`` : the generator of the free part of a finitely generated subgroup of `K^*`, where `K` is a number field
       - ``prime`` : a prime ideal of K`
       - ``g0`` : the generator of the torsion part of the group `G_2`
       - ``c3`` : is defined in the page 136 of the reference
       - ``embeddings`` : a list of all embendings of `K` to `\mathbb C`
    
    OUTPUT:
        - an upper bound associate to ``prime`` according to IX.1.3 of the reference page 139
        - a list of elements in `K^*` which contains all `\mu_0` that can appear to lemma IX.3 page 139 of the reference
        - a list of elements in `K^*` which contains all `\mu_i` for `i>0` that appear to lemma IX.3 page 139 of the reference
        - the constant `c_9` that appears to IX.1.3 of the reference page 139
    
    REFERENCE:
        Nigel P. Smart. The Algorithmic Resolution of Diophantine Equations. Number 41 in Students Texts. London Mathematical Society, 1998.
        
    EXAMPLE::
        
        sage: K.<a> = NumberField(x^3-2)
        sage: p1,p2 = K.places(prec = 50)
        sage: S = K.primes_above(5)
        sage: prime = S[0]; prime
            Fractional ideal (-a^2 - 1)
        sage: G = [g for g in K.S_unit_group(S = S).gens_values() if g.multiplicative_order() == Infinity]
        sage: g0 = [g for g in K.S_unit_group(S = S).gens_values() if g.multiplicative_order() != Infinity][0]
        sage: c3 = 99*c1_constant(G,S,[p1],[p2])/(100*len(G))
        sage: initial_bound_finite_case(G,prime,g0,c3,[p1,p2])
            (-5.1276394965735e20*(-2.0000000000000*log(6)/log(5)^2 -
            log(2.5638197482868e20/log(5))/log(5)^2)*log(5), [-1, 1], [a - 1, a^2 -
            2*a - 1], 0.53111451110325/log(5))    
    """
             
    p = (prime.norm()).factor()[0][0]
    f = prime.residue_class_degree()
    e = prime.absolute_ramification_index()
    c9 = c3/(e * f * log(p))

    M0,M,k = a_basis_with_0_order_at_p(prime,[g0]+G2free)
    B = 0
    for m0 in M0:
        c11 , c12 = Yu_theorem([m0]+M,prime,embeddings)
        B = max([B,(2 * (c12 + c11 * log(c11/(e * c9))) )/(e * c9)])
    
    return B,M0,M


def solutions_when_no_free_part(g0,G2):
    r"""
    
    INPUT:
        - ``g0`` : the generator of the torsion part of the group `G_1` where `x` lies
        - ``G2`` : the generators of the groups `G_2` where `y` lies
    
    OUTPUT:
        All `x` which are solutions of the S-unit equation `x+y=1`
        
    EXAMPLE::
        
        sage: K.<a> = QuadraticField(2)
        sage: SK = sum([K.primes_above(p) for p in [2,3]],[])
        sage: g0 = K.unit_group().torsion_generator().value()
        sage: solutions_when_no_free_part(g0,K.S_unit_group(S = SK).gens_values())
            [-1]
            
        sage: K.<a> = CyclotomicField(19)
        sage: SK = sum([K.primes_above(p) for p in [2,3,5]],[])
        sage: g0 = K.unit_group().torsion_generator().value()
        sage: solutions_when_no_free_part(a,K.S_unit_group(S = SK).gens_values())
            [-a^8, -a^5, -a^2, a^17 + a^16 + a^15 + a^14 + a^13 + a^12 + a^11 + a^10
            + a^9 + a^8 + a^7 + a^6 + a^5 + a^4 + a^3 + a^2 + a + 1, -a^15, -a^12,
            -a^9, -a^6, -a^3, -1, -a^16, -a^13, -a^10, -a^7, -a^4, -a, -a^17, -a^14,
            -a^11]
    """
    if g0.multiplicative_order() == Infinity:
        raise ValueError('g0 has infinity multiplicative order')
    if len(G2) == 0:
        raise ValueError('G2 is empty')
    
    solutions = []
    for x in [g0**i for i in range(g0.multiplicative_order())]:
        if x != 1:
            if is_in_G(1-x,G2):
                if x not in solutions:
                    solutions.append(x)
    return solutions


def reduce_the_bound_absolute_field(K,G1,G2,precision):
    r"""
    
    INPUT:
       - ``K`` : a number field
       - ``G1`` : a list of generators of a multiplicative subgroup of `K^*` where `x` lies
       - ``G2`` : a list of generators of a multiplicative subgroup of `K^*` where `y` lies
       - ``precision`` : the precision for the calculations
       
    OUTPUT:
        All the solutions `x` of the `S-unit` equation `x+y=1` when `x\in G_1` and `y\in G_2`
        
    COMMENT:
        K has to be a absolute field

    EXAMPLE::
        
        sage: 
    
    """
    if len(G1) == 0:
        raise ValueError('G1 is the empty list')
    if len(G2) == 0:   
         raise ValueError('G2 is empty list')

    if G1 == G2:
        sameG1G2 = True
    else:
        sameG1G2 = False

    Kplaces = K.places(prec = precision)
    Krealplaces = K.real_embeddings(prec = precision)
    Kcomplexplaces = [s for s in Kplaces if not is_real_place(s)]
    Kembeddings = Krealplaces + Kcomplexplaces

    finiteSup1, realSup1, complexSup1 = support_of_G(G1,precision)
    finiteSup2, realSup2, complexSup2 = support_of_G(G2,precision)

    #the generators for the free part of each G1 and G2

    G1free = [g for g in G1 if g.multiplicative_order() == Infinity]
    G2free = [g for g in G2 if g.multiplicative_order() == Infinity]

    lenG1free = len(G1free)
    lenG2free = len(G2free)

    #the generator of the torsion part of G1 and G2

    if len([g for g in G1 if g.multiplicative_order() != Infinity]) > 0:
        g01 = [g for g in G1 if g.multiplicative_order() != Infinity][0]
    else:
        g01 = K(1)
        
    if len([g for g in G2 if g.multiplicative_order() != Infinity]) > 0:
        g02 = [g for g in G2 if g.multiplicative_order() != Infinity][0]
    else:
        g02 = K(1)

    #Since both groups have the same torsion part we define a global torsion

    if lenG1free == 0:
        return g01.multiplicative_order()
    elif lenG2free == 0 and not sameG1G2:
        return g02.multiplicative_order()

    G1c1 ,G1c2, G1c3= c_constants(G1free,precision)
    G2c1,G2c2, G2c3 = c_constants(G2free,precision)
    c1 = max([G1c1,G2c1])

    S1 = finiteSup1+complexSup1+realSup1
    S2 = finiteSup2+complexSup2+realSup2

    ##  STEP 1 - Initial bound  ##
    
    #Calculating initial bound for the real case

    G1B1real = max([initial_bound_real_case(G2free,prime,G1c3) for prime in realSup1] + [0])
    G2B1real = max([initial_bound_real_case(G1free,prime,G2c3) for prime in realSup2] + [0])
    B1real = max(G1B1real,G2B1real)
    # print('B1real',RR(G1B1real),RR(G2B1real))
    
    #Calculating initial bound for the complex case
    
    G1B1complex = max([initial_bound_complex_case(G2free,prime,g02,G1c3) for prime in complexSup1] + [0])
    G2B1complex = max([initial_bound_complex_case(G1free,prime,g01,G2c3) for prime in complexSup2] + [0])
    B1complex = max(G1B1complex,G2B1complex)
    # print('B1complex',RR(B1complex).n(21))
    
    #Calculating initial bound for the finite case and objects we need for the reduction step
    
    G1B1finite = 0
    G1finite_initialization = []
    for prime in finiteSup1:
        B1, M0, M= initial_bound_finite_case(G2free,prime,g02,G1c3,Kembeddings)
        G1finite_initialization.append([prime, M0, M])
        G1B1finite = max(G1B1finite,B1)
        
    G2B1finite = 0 
    G2finite_initialization = []
    for prime in finiteSup2:
        B1, M0, M = initial_bound_finite_case(G1free,prime,g01,G2c3,Kembeddings)
        G2finite_initialization.append([prime, M0, M])
        G2B1finite = max(G2B1finite,B1)
    B1finite = max(G1B1finite,G2B1finite)
    # print('B1finite',RR(B1finite).n(21))
    B1 = RR(max(B1real,B1complex,B1finite)).floor()
    # print 'B1',B1

    # return B1

    ##  STEP 2 - Reduction step  ##
    
    # Real case
    # print 'real'
    #G1
    G1B2real = 0
    for place in realSup1:
        Bold = B1
        finish = False
        while not finish:
            Bnew , increase_precision = reduction_step_real_case(place,Bold,G2free,G1c3)

            #if we have to increase the precision we evaluate c1,c2,c3 constants again

            if not increase_precision:
                if Bnew < Bold:
                    Bold = Bnew
                    if Bold <= 2:
                        finish = True
                        Bold = 2
                else:
                    finish = True
            else:
                #we evaluate with higher precision G1c1 , G1c2 and G1c3

                G1c1 ,G1c2, G1c3 = c_constants(G1free,2*place.codomain().precision())
                place = higher_precision(place,2*place.codomain().precision())

        G1B2real = max(G1B2real,Bold)

    #G2
    if not sameG1G2:
        G2B2real = 0
        for place in realSup2:
            Bold = B1
            finish = False
            while not finish:
                Bnew , increase_precision = reduction_step_real_case(place,Bold,G1free,G2c3)

                #if we have to increase the precision we evaluate c1,c2,c3 constants again

                if not increase_precision:
                    if Bnew < Bold:
                        Bold = Bnew
                        if Bold <= 2:
                            finish = True
                            Bold = 2
                    else:
                        finish = True
                else:
                    #we evaluate with higher precision G2c1 , G2c2 and G2c3

                    G2c1 ,G2c2, G2c3 = c_constants(G2free,2*place.codomain().precision())
                    place = higher_precision(place,2*place.codomain().precision())

            G2B2real = max(G2B2real,Bold)
        B2real = max(G1B2real,G2B2real)
    else:
        B2real = G1B2real
    # print 'B2real',B2real

    # Complex case
    # print 'complex'
    #G1
    # print 'G1'
    G1B2complex = 0
    for place in complexSup1:
        B_place = 0
        for g0 in [g02**i for i in range(g02.multiplicative_order())]:
            Bold_g0 = B1
            finish = False
            while not finish:
                Bnew_g0 ,increase_precision = reduction_step_complex_case(place,Bold_g0,G2free,g0,G1c3/2)

                #if we have to increase the precision we evaluate c1,c2,c3 constants again
                if not increase_precision:
                    if Bnew_g0 < Bold_g0:
                        Bold_g0 = Bnew_g0
                        if Bold_g0 <= 2:
                            finish = True
                            Bold_g0 = 2
                    else:
                        finish = True
                else:
                    #we evaluate with higher precision G1c1 , G1c2 and G1c3

                    G1c1 ,G1c2, G1c3 = c_constants(G1free,2*place.codomain().precision())
                    place = higher_precision(place,2*place.codomain().precision())
            B_place = max(B_place,Bold_g0)
        G1B2complex = max(G1B2complex,B_place)

    # print 'G2'
    #G2
    if not sameG1G2:
        G2B2complex = 0
        for place in complexSup2:
            B_place = 0
            for g0 in [g01**i for i in range(g01.multiplicative_order())]:
                Bold_g0 = B1
                finish = False
                while not finish:
                    Bnew_g0 ,increase_precision = reduction_step_complex_case(place,Bold_g0,G1free,g0,G2c3/2)

                    #if we have to increase the precision we evaluate c1,c2,c3 constants again
                    if not increase_precision:
                        if Bnew_g0 < Bold_g0:
                            Bold_g0 = Bnew_g0
                            if Bold_g0 <= 2:
                                finish = True
                                Bold_g0 = 2
                        else:
                            finish = True
                    else:
                        #we evaluate with higher precision G2c1 , G2c2 and G2c3

                        G2c1 ,G2c2, G2c3 = c_constants(G2free,2*place.codomain().precision())
                        place = higher_precision(place,2*place.codomain().precision())
                B_place = max(B_place,Bold_g0)
            G2B2complex = max(G2B2complex,B_place)
        B2complex = max(G1B2complex,G2B2complex)
    else:
        B2complex = G1B2complex
    # print 'B2complex',B2complex

    #  Finite case
    # print 'finite'
    # print 'G1'
    G1B2finite = 0
    for P in G1finite_initialization:
        B_place = 0
        if len(P[2]) !=0:
            prec = precision
            M_logp = [log_p(m,P[0],prec) for m in P[2]]
            M_logp = [embedding_to_Kp(m,P[0],prec) for m in M_logp]
            for m0 in P[1]:
                Bold_m0 = B1
                finish = False
                while not finish:
                    # return P[0],Bold_m0,P[2],M_logp,m0,G1c3,prec
                    Bnew_m0,increase_precision = reduction_step_finite_case(P[0],Bold_m0,P[2],M_logp,m0,G1c3,prec)

                    #if we have to increase the precision we evaluate c1,c2,c3 constants again
                    if not increase_precision:
                        if Bnew_m0 < Bold_m0:
                            Bold_m0 = Bnew_m0
                            if Bold_m0 <= 2:
                                finish = True
                                Bold_m0 = 2
                        else:
                            finish = True
                    else:
                        #we evaluate with higher precision G1c1, G1c2 and G1c3
                        prec *= 2
                        G1c1 ,G1c2, G1c3 = c_constants(G1free,prec)
                        M_logp = [log_p(m,P[0],prec) for m in P[2]]
                        M_logp = [embedding_to_Kp(m,P[0],prec) for m in M_logp]
                B_place = max(B_place,Bold_m0)
        G1B2finite = max(G1B2finite,B_place)

    # print 'G2'
    if not sameG1G2:
        G2B2finite = 0
        for P in G2finite_initialization:
            B_place = 0
            if len(P[2]) != 0:
                prec = precision
                M_logp = [log_p(m,P[0],prec) for m in P[2]]
                M_logp = [embedding_to_Kp(m,P[0],prec) for m in M_logp]
                for m0 in P[1]:
                    Bold_m0 = B1
                    finish = False
                    while not finish:
                        Bnew_m0,increase_precision = reduction_step_finite_case(P[0],Bold_m0,P[2],M_logp,m0,G2c3,prec)

                        #if we have to increase the precision we evaluate c1,c2,c3 constants again
                        if not increase_precision:
                            if Bnew_m0 < Bold_m0:
                                Bold_m0 = Bnew_m0
                                if Bold_m0 <= 2:
                                    finish = True
                                    Bold_m0 = 2
                            else:
                                finish = True
                        else:
                            #we evaluate with higher precision G2c1 , G2c2 and G2c3
                            prec *= 2
                            G2c1 ,G2c2, G2c3 = c_constants(G2free,prec)
                            M_logp = [log_p(m,P[0],prec) for m in P[2]]
                            M_logp = [embedding_to_Kp(m,P[0],prec) for m in M_logp]
                    B_place = max(B_place,Bold_m0)
            G2B2finite = max(G2B2finite,B_place)
        B2finite = max(G1B2finite,G2B2finite)
    else:
        B2finite = G1B2finite

    return RR(max(B2real,B2complex,B2finite)).floor()


def reduce_the_bound(K,G1,G2,precision):
    r"""

    INPUT:
       - ``K`` : a number field
       - ``G1`` : a list of generators of a multiplicative subgroup of `K^*` where `x` lies
       - ``G2`` : a list of generators of a multiplicative subgroup of `K^*` where `y` lies
       - ``precision`` : the precision for the calculations

    OUTPUT:
        An upper bound for the exponents of the solutions `x,y` of the `S-unit` equation `x+y=1`
        when `x\in G_1` and `y\in G_2`

    EXAMPLE::

        sage:

    """
    if len(G1) == 0:
        raise ValueError('G1 is the empty list')
    if len(G2) == 0:
         raise ValueError('G2 is empty list')

    if K.is_absolute():
        return reduce_the_bound_absolute_field(K,G1,G2,precision)
    else:
        Kabs = K.absolute_field('b')
        KembKabs = K.embeddings(Kabs)[0]
        G1abs = [KembKabs(g) for g in G1]
        G2abs = [KembKabs(g) for g in G2]
        return reduce_the_bound_absolute_field(Kabs,G1abs,G2abs,precision)


def simple_loop_for_S_unit_equation(G1,G2,B):
    r"""

    INPUT:
        - ``G1`` : a list of generators of a `S_1`-unit group of a number field `K`
        - ``G2`` : a list of generators of a `S_2`-unit group of a number field `K`
        - ``B`` : An upper bound for the exponents of the solutions `x,y` of the `S-unit` equation `x+y=1`
            when `x` is a `S_1`-unit and `y` is a `S_2`-unit

    OUTPUT:

        A list of all `x` of the solutions `(x,y)` of the `S-unit` equation `x+y=1`
        when `x` is a `S_1`-unit and `y` is a `S_2`-unit

    EXAMPLE::

        sage:
    """
    if len(G1) == 0:
        return []
    K = G1[0].parent()
    S2 = support_of_G(G2,10)[0]
    SunitG2 = K.S_unit_group(S = S2)
    torsion_order = G1[0].multiplicative_order()
    print('torsion_order = ',torsion_order  )
    solutions = []
    for v in cartesian_product_iterator([xrange(torsion_order)]+(len(G1)-1)*[xrange(-B,B+1)]):
        x = prod([g**e for e,g in zip(v,G1)])
        if is_S_unit_element(SunitG2,1-x):
            print("v = ",v)
            solutions.append(x)
    return solutions




###### SIEVE ######


def simple_loop_over_K(Gl,bounds,S):
    r"""

    INPUT:
        - ``Gl`` : a list of generators of a multiplicative subgroup of `K^*` for a number field `K`
        - ``bounds`` a list of upper bounds of the absolute value of the exponents of ``Gl``
        - ``S`` :  a list of prime ideals of `K`

    OUTPUT:
        A list of all `\lambda\in G_\lambda` such that `1-\lambda` is an ``S``-unit
    """

    K = Gl[0].parent()
    Smunit_group = K.S_unit_group(S=S)
    Sunits = []
    for v in cartesian_product_iterator([xrange(bounds[0])]+[xrange(-b,b+1) for b in bounds[1:]]):
        l = prod([g**e for g,e in zip(Gl,v)])
        if is_S_unit_element(Smunit_group,1-l):
            if l not in Sunits:
                Sunits.append(l)

    #we throw away 0 and 1

    while 0 in Sunits:
        Sunits.remove(0)
    while 1 in Sunits:
        Sunits.remove(1)

    return Sunits


def reduce_the_bound_for_unit_generators(G,bounds,R):
    r"""

    INPUT:
        - ``G`` : a list of generators of the group
        - ``bounds`` : a list of upper bounds for each generator
        - ``R`` : a real number such that `\mid\log\mid\mu\mid_{\mathfrak p}\mid\leq\log(R)` for all infinite primes `\mathfrak p`
    """


def reduce_the_bound_for_p_in_support_of_G(prime,G,B):
    r"""

    INPUT:
        - ``prime`` : a prime ideal which lies in the support of ``G``
        - ``G`` : a list of generators of the group
        - ``B`` : an upper bound for the exponents of the solutions `\lambda ,\mu`

    OUTPUT:
        A reduced upper bound for the valuation of `\lambda` at the prime ideal ``prime``.

    COMMENT:
        We use Smart's ideas to prove that the inequality `\mid\mu -1\mid_{\mathfrak p}\leq\delta` has not nontrivial
        solutions.
    """

    Blow = 1
    Bupp = B
    Bmid = RR((Blow+Bupp)/2).floor()

    L = prime.ring()
    Labs = L.absolute_field('a')
    eLLabs = L.embeddings(Labs)[0]
    prime_abs = eLLabs(prime)
    G_abs = [eLLabs(g) for g in G]
    p = prime_abs.absolute_norm().factor()[0][0]
    f = prime_abs.residue_class_degree()
    precision = 200

    #we evaluate the new basis of Gm of elements with zero valuation at prime and their p-adic logarithms
    new_G0_abs, new_G_abs, k = a_basis_with_0_order_at_p(prime_abs,G_abs)
    new_G_abs_logp = [log_p(m,prime_abs,precision) for m in new_G_abs]
    new_G0_abs_logp = [log_p(m0,prime_abs,precision) for m0 in new_G0_abs]

    while Bupp-Blow > 1:

        trivial, new_G0_abs_logp, new_G_abs_logp, precision = trivial_Tp_finite_place(B,prime_abs,new_G0_abs,new_G_abs,new_G0_abs_logp,new_G_abs_logp,p**(-Bmid*f),precision)
        if trivial:
            Bupp = Bmid
        else:
            Blow = Bmid
        Bmid = RR((Blow+Bupp)/2).floor()
    return Bupp


def general_sieve(G,B,precision):
    r"""

    INPUT:
        - ``G`` : a list of generators of the group ``G_\mu``
        - ``B`` : an upper bound for the exponents of the solutions `\lambda ,\mu`.
        - ``precision`` : the precision of the calculations

    OUTPUT:
        All solutions of the `S`-unit equation `\lambda+\mu=1` where `\lambda,\mu\in G`.

    COMMENT:
        We assume that both `\lambda` and `\mu` lie in ``G``.
    """

    supp = support_of_G(G,precision)
    bounds = [G[0].multiplicative_order()]+[B]*(len(G)-1)


    # bounds_S = [0]*len(supp[0])

    #We find smaller upper bounds for the valuation of the solutions in prime ideals

    bound_S = [reduce_the_bound_for_p_in_support_of_G(prime,G,B) for prime in supp[0]]
    bounds = bounds_for_exponents_from_bounds_for_primes(G,supp[0],bound_S,bounds)

    return bounds
