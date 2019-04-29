from binascii import hexlify
from CompactFIPS202 import SHA3_256, SHAKE256

class Vision:
    def __init__( self, security_level, n, m ):
        self.security_level = security_level
        assert n >= security_level, "state size (n) must be at least as large as security level"
        assert n % m == 0, "m must divide n"
        self.n = n
        self.m = m
        self.rate = floor(m/2)
        self.capacity = m - self.rate
        self.Nb = 2*ceil((1.0 * security_level) / (5.5*m))

        self.F = self.field(n,m)
        self.B, self.Binv, self.initial_constant, self.constants_matrix, self.constants_constant = Vision.sample_parameters(self.F, self.m)
        self.MDS = Vision.MDS_matrix(self.F, self.m)

    # generate a mxm MDS matrix over F
    @staticmethod
    def MDS_matrix( F, m ):
        z = F.primitive_element()
        mat = matrix([[z^(i*j) for j in range(0, 2*m)] for i in range(0, m)])
        return mat.echelon_form()[:, m:]

    # get the right defining polynomial for the extension field
    # i.e., lexicographically the first irreducible polynomial of
    # the right degree
    @staticmethod
    def field( n, m ):
        GF2 = FiniteField(2)
        GF2x.<x> = PolynomialRing(GF2, "x")

        i = -1
        have_polynomial = False
        while have_polynomial == False:
            i = i + 2
            bits = (bin(i)[2:])
            polynomial = x^(n/m ) + sum(x^(len(bits)-1-j) for j in range(0,len(bits)) if bits[j] == '1')
            have_polynomial = polynomial.is_irreducible()

        F = FiniteField(2^(n/m), "x", modulus=polynomial)
        return F

    # get the parameters B, Binv, and the constants; extract them
    # from SHAKE seeded with a memorable string
    @staticmethod
    def sample_parameters( F, m ):
        seed = "winteriscoming"
        seed = bytearray(seed)

        buf_len = 1 # bytes
        have_params = False
        while have_params == False:
            buf_len = buf_len * 2
            randomness = SHAKE256(seed, buf_len)
            try:
                constants = Vision.sample_constants(F, m, randomness)
                break
            except BufferError:
                continue

        B = constants[0:4]
        Binv = Vision.affine_inverse(B)
        initial_constant = matrix([[constants[4+i]] for i in range(0, m)])
        constants_matrix = matrix([[constants[4+m+i*m+j] for j in range(0,m)] for i in range(0,m)])
        constants_constant = matrix([[constants[4+m+m^2+i]] for i in range(0,m)])
        return B, Binv, initial_constant, constants_matrix, constants_constant

    # sample the given number of constants randomly from the given
    # field using the randomness provided; if there is not enough
    # randomness, throw a buffer error
    @staticmethod
    def sample_constants( F, m, randomness ):
        counter = 0
        constants = []
        chunk_size = ceil(F.modulus().degree() / 8 )
        while len(constants) != 4 + 2*m + m^2:
            have_constant = False
            while have_constant == False:
                if counter+chunk_size > len(randomness):
                    raise BufferError
                constant = Vision.field_element_from_bytes(F, randomness[counter:(counter+chunk_size)])
                counter += chunk_size

                # only if the sampled constant is not in any
                # subfields do we accept it
                if Vision.is_generator(F, constant):
                    constants.append(constant)
                    break

            # if constants 1,2,3 do not define an invertible
            # linearized polynomial, reject them
            if len(constants) == 4:
                if not Vision.linearized_is_invertible(constants[1:]):
                    constants = [constants[0]]

            # if the m^2 constants after the affine polynomial B do
            # define an invertible matrix, reject them
            if len(constants) == 4 + m^2:
                mat = matrix([[constants[4+i*m+j] for j in range(0,m)] for i in range(0,m)])
                if not mat.is_invertible():
                    constants = constants[0:4]
        return constants

    # determine if the given list of coefficients represents an
    # invertible linearized transform
    @staticmethod
    def linearized_is_invertible( coefficients ):
        F = coefficients[0].parent()
        deg = F.modulus().degree()
        mat = copy(MatrixSpace(F, deg, deg).zero())
        for i in range(0, min(deg, len(coefficients))):
            mat[0,i] = coefficients[i]
        for i in range(1, deg):
            for j in range(1, deg):
                mat[i,j] = mat[i-1,j-1]
            mat[i,0] = mat[i-1,deg-1]
        for i in range(1, deg):
            for j in range(0, deg):
                mat[i,j] = mat[i,j]^(2^i)
        return mat.is_invertible()

    # turn a string of bytes into an element from the given field;
    # assuming there are enough bytes
    @staticmethod
    def field_element_from_bytes( F, randomness ):
        x = F.gen()
        integer = sum(randomness[i] * 256^i for i in range(0, len(randomness)))
        bits = bin(integer)[2:]
        element = sum(x^i for i in range(0, min(F.modulus().degree(), len(bits))) if bits[i] == '1')
        return element

    # decide if a given element generates the entire field (and not
    # just a subfield)
    @staticmethod
    def is_generator( F, constant ):
        deg = F.modulus().degree()
        factorization = factor(deg)
        # for all possible subfield orders, try raising the power order
        for fact, multiplicity in factorization:
            if constant^(2^(deg/fact)) == constant: # if that power sends the element to itself, it generates only the subfield
                return False
        # all tests succeed
        return True

    # get the inverse of an affine transform, as represented by a
    # list of coefficients
    @staticmethod
    def affine_inverse( B ):
        F = B[0].parent()
        deg = F.modulus().degree()
        MS = MatrixSpace(F, deg, deg)
        mat = copy(MS.zero())
        mat[0,0] = B[1]
        mat[0,1] = B[2]
        mat[0,2] = B[3]

        for i in range(1,deg):
            for j in range(1, deg):
                mat[i,j] = mat[i-1,j-1]
            mat[i,0] = mat[i-1,deg-1]
        for i in range(1, deg):
            for j in range(0, deg):
                mat[i,j] = mat[i,j]^(2^i)
        mat = mat.inverse()
        coefficients = [mat[0,i] for i in range(0,deg)]
        constant = sum(coefficients[i] * B[0]^(2^i) for i in range(0, deg))
        return [constant] + coefficients

    # print parameters
    def Parameters( self ):
        print "# Parameters"
        print "security level:", self.security_level
        print "n: %i \t m: %i \t Nb: %i" % (self.n, self.m, self.Nb)
        print "rate:", self.rate, " \t capacity:", self.capacity
        print "field:", self.F, "... with modulus:", self.F.modulus()
        print "B[0]:", self.B[0]
        print "B[1]:", self.B[1]
        print "B[2]:", self.B[2]
        print "B[3]:", self.B[3]
        print "initial constant:"
        print self.initial_constant
        print "constants matrix:"
        print self.constants_matrix
        print "constants constant:"
        print self.constants_constant

    # evaluate the block cipher
    def BlockCipher( self, key, ptxt ):
        key_state = key
        data_state = ptxt

        key_injection = self.initial_constant
        key_state += key_injection
        data_state += key_state
        for r in range(0, 2*self.Nb):
            # constants
            key_injection = self.constants_matrix * key_injection + self.constants_constant

            # key schedule
            key_state = matrix([[key_state[i,0]^(2^(self.n/self.m)-2)] for i in range(0,self.m)])
            if r % 2 == 0:
                key_state = matrix([[self.Binv[0] + sum(key_state[i,0]^(2^(j-1)) * self.Binv[j] for j in range(1, len(self.Binv)))] for i in range(0, self.m)])
            else:
                key_state = matrix([[self.B[0] + sum(key_state[i,0]^(2^(j-1)) * self.B[j] for j in range(1, len(self.B)))] for i in range(0, self.m)])
            key_state = self.MDS * key_state
            key_state += key_injection

            # data path
            data_state = matrix([[data_state[i,0]^(2^(self.n/self.m)-2)] for i in range(0,self.m)])
            if r % 2 == 0:
                data_state = matrix([[self.Binv[0] + sum(data_state[i,0]^(2^(j-1)) * self.Binv[j] for j in range(1, len(self.Binv)))] for i in range(0, self.m)])
            else:
                data_state = matrix([[self.B[0] + sum(data_state[i,0]^(2^(j-1)) * self.B[j] for j in range(1, len(self.B)))] for i in range(0, self.m)])
            data_state = self.MDS * data_state
            data_state += key_state

        return data_state

    # evaluate the sponge function
    def Sponge( self, inputs, num_out ):
        key = matrix(self.F, [[self.F.zero()]] * self.m)
        state = matrix(self.F, [[self.F.zero()]] * self.m)
        for i in range(0, len(inputs)):
            if i != 0 and i%self.rate == 0:
                state = self.BlockCipher(key, state)
            state[i%self.rate,0] += inputs[i]

        outputs = []
        for i in range(0, num_out):
            if i%self.rate == 0:
                state = self.BlockCipher(key, state)
            outputs.append(state[i%self.rate,0])

        return outputs

class Rescue:
    def __init__( self, security_level, q, m ):
        assert log(1.0*q, 2.0) * m >= security_level , "state must have as least security_level-many bits!"
        self.security_level = security_level
        self.F = Rescue.first_field(q)
        self.m = m
        self.rate = floor(m/2)
        self.capacity = m - self.rate

        # We set alpha = 3. This can be chanegd but requires an adaptation to the number of rounds
        self.alpha = 3
        while gcd(self.alpha, q-1) != 1:
            self.alpha += 2;
        g, a, b = xgcd(self.alpha, q-1)
        self.invalpha = a

        self.Nb = 2*ceil((1.0 * security_level) / (4*m))

        self.MDS = Rescue.MDS_matrix(self.F, self.m)
        self.initial_constant, self.constants_matrix, self.constants_constant = Rescue.sample_parameters(self.F, self.m)

    # generate a mxm MDS matrix over F
    @staticmethod
    def MDS_matrix( F, m ):
        z = F.primitive_element()
        mat = matrix([[z^(i*j) for j in range(0, 2*m)] for i in range(0, m)])
        return mat.echelon_form()[:, m:]

    # get the first field, lexicographically speaking, of the given order
    @staticmethod
    def first_field( q ):
        factorization = factor(q)
        assert(len(factorization) == 1), "cannot sample field with order not equal to a prime power"

        p = factorization[0][0]
        d = factorization[0][1]
        Fp = FiniteField(p)
        Fpx.<x> = PolynomialRing(Fp, "x")

        integer = 1
        expansion = []
        int_cpy = copy(integer)
        while int_cpy > 0:
            expansion.append(int_cpy % p)
            int_cpy = int_cpy // p
        poly = Fp(1) * x^d + sum(Fp(expansion[i]) * x^i for i in range(0, len(expansion)))
        while not poly.is_irreducible():
            integer += 1
            int_cpy = copy(integer)
            expansion = []
            while int_cpy > 0:
                expansion.append(int_cpy % p)
                int_cpy = int_cpy // p
            poly = Fp(1) * x^d + sum(Fp(expansion[i]) * x^i for i in range(0, len(expansion)))

        return FiniteField(q, "x", modulus=poly)

    # turn a string of bytes into a field element
    @staticmethod
    def field_element_from_bytes( F, buff ):
        p = F.characteristic()
        d = F.modulus().degree()
        x = F.modulus().parent().gen()
        integer = sum(256^i * buff[i] for i in range(0, len(buff)))

        if d == 1:
            return F(integer % p)

        expansion = []
        while integer > 0:
            expansion.append(integer % p)
            integer = integer // p

        poly = sum(F(expansion[i]) * x^i for i in range(0, len(expansion)))
        return F(poly)

    # extract the constants
    # from SHAKE seeded with a memorable string
    @staticmethod
    def sample_parameters( F, m ):
        seed = "winteriscoming"
        seed = bytearray(seed)

        buf_len = 1 # bytes
        have_params = False
        while have_params == False:
            buf_len = buf_len * 2
            randomness = SHAKE256(seed, buf_len)
            try:
                constants = Rescue.sample_constants(F, m, randomness)
                break
            except BufferError:
                continue

        initial_constant = matrix([[constants[i]] for i in range(0, m)])
        constants_matrix = matrix([[constants[m+i*m+j] for j in range(0,m)] for i in range(0,m)])
        constants_constant = matrix([[constants[m+m^2+i]] for i in range(0,m)])
        return initial_constant, constants_matrix, constants_constant

    # sample the given number of constants randomly from the given
    # field using the randomness provided; if there is not enough
    # randomness, throw a buffer error
    @staticmethod
    def sample_constants( F, m, randomness ):
        counter = 0
        constants = []
        chunk_size = ceil(log(1.0*F.order(),2.0) / 8 ) + 1
        while len(constants) != 2*m + m^2:
            have_constant = False
            while have_constant == False:
                if counter+chunk_size > len(randomness):
                    raise BufferError
                constant = Rescue.field_element_from_bytes(F, randomness[counter:(counter+chunk_size)])
                counter += chunk_size

                # only if the sampled constant is not in any
                # subfields do we accept it
                if Rescue.is_generator(F, constant):
                    constants.append(constant)
                    break

            # if the m^2 first constants do not
            # define an invertible matrix, reject them
            if len(constants) == m^2:
                mat = matrix([[constants[i*m+j] for j in range(0,m)] for i in range(0,m)])
                if not mat.is_invertible():
                    constants = []
        return constants

    # decide if a given element generates the entire field (and not
    # just a subfield)
    @staticmethod
    def is_generator( F, constant ):
        p = F.characteristic()
        deg = F.modulus().degree()
        factorization = factor(deg)
        # for all possible subfield orders, try raising to the power order
        for fact, multiplicity in factorization:
            if constant^(p^(deg/fact)) == constant: # if that power sends the element to itself, it generates only the subfield
                return False
        # all tests succeed
        return True

    # print the parameters
    def Parameters( self ):
        print "# Parameters"
        print "security level:", self.security_level
        print "q:", self.F.order(), "\tm:", self.m, "\tNb:", self.Nb
        print "rate:", self.rate, "\tcapacity:", self.capacity
        print "field:", self.F
        print "initial constant:\n", self.initial_constant
        print "constants matrix:\n", self.constants_matrix
        print "constants constant:\n", self.constants_constant

    # evaluate the block cipher in forward direction
    def BlockCipher( self, key, ptxt ):
        key_state = key
        data_state = ptxt

        key_injection = self.initial_constant
        key_state += key_injection
        data_state += key_state

        for r in range(0, 2*self.Nb):
            if r % 2 == 0:
                for i in range(0,self.m):
                    key_state[i,0] = key_state[i,0]^self.invalpha
                    data_state[i,0] = data_state[i,0]^self.invalpha
            else:
                for i in range(0,self.m):
                    key_state[i,0] = key_state[i,0]^self.alpha
                    data_state[i,0] = data_state[i,0]^self.alpha
            key_injection = self.constants_matrix * key_injection + self.constants_constant
            key_state = self.MDS * key_state + key_injection
            data_state = self.MDS * data_state + key_state

        return data_state

    # evaluate the sponge function
    def Sponge( self, inputs, num_out ):
        key = matrix(self.F, [[self.F.zero()]] * self.m)
        state = matrix(self.F, [[self.F.zero()]] * self.m)
        for i in range(0, len(inputs)):
            if i != 0 and i%self.rate == 0:
                state = self.BlockCipher(key, state)
            state[i%self.rate,0] += inputs[i]

        outputs = []
        for i in range(0, num_out):
            if i%self.rate == 0:
                state = self.BlockCipher(key, state)
            outputs.append(state[i%self.rate,0])

        return outputs
