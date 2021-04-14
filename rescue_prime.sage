from CompactFIPS202 import SHAKE256

def get_round_constants( p, m, capacity, security_level, N ):
    # generate pseudorandom bytes
    bytes_per_int = ceil(len(bin(p)[2:]) / 8) + 1
    num_bytes = bytes_per_int * 2 * m * N
    seed_string = "Rescue-XLIX(%i,%i,%i,%i)" % (p, m, capacity, security_level)
    byte_string = SHAKE256(bytes(seed_string, "ascii"), num_bytes)

    # process byte string in chunks
    round_constants = []
    Fp = FiniteField(p)
    for i in range(2*m*N):
        chunk = byte_string[bytes_per_int*i : bytes_per_int*(i+1)]
        integer = sum(256^j * ZZ(chunk[j]) for j in range(len(chunk)))
        round_constants.append(Fp(integer % p))

    return round_constants

def get_number_of_rounds( p, m, capacity, security_level, alpha ):
    # get number of rounds for Groebner basis attack
    rate = m - capacity
    dcon = lambda N : floor(0.5 * (alpha-1) * m * (N-1) + 2)
    v = lambda N : m*(N-1) + rate
    target = 2^security_level
    for l1 in range(1, 25):
        if binomial(v(l1) + dcon(l1), v(l1))^2 > target:
            break

    # set a minimum value for sanity and add 50%
    return ceil(1.5 * max(5, l1))

def get_alphas( p ):
    for alpha in range(3, p):
        if gcd(alpha, p-1) == 1:
            break
    g, alphainv, garbage = xgcd(alpha, p-1)
    return (alpha, (alphainv % (p-1)))

def get_mds_matrix( p, m ):
    # get a primitive element
    Fp = FiniteField(p)
    g = Fp(2)
    while g.multiplicative_order() != p-1:
        g = g + 1

    # get a systematic generator matrix for the code
    V = matrix([[g^(i*j) for j in range(0, 2*m)] for i in range(0, m)])
    V_ech = V.echelon_form()

    # the MDS matrix is the transpose of the right half of this matrix
    MDS = V_ech[:, m:].transpose()
    return MDS

def rescue_prime_parameters( p, m, capacity, security_level ):
    alpha, alphainv = get_alphas(p)
    N = get_number_of_rounds(p, m, capacity, security_level, alpha)
    MDS = get_mds_matrix(p, m)
    round_constants = get_round_constants(p, m, capacity, security_level, N)
    return p, m, capacity, security_level, alpha, alphainv, N, MDS, round_constants

def rescue_prime_wrapper( parameters, input_sequence ):
    p, m, capacity, security_level, alpha, alphainv, N, MDS, round_constants = parameters
    rate = m - capacity
    Fp = FiniteField(p)

    padded_input = input_sequence + [Fp(1)]
    while len(padded_input) % rate != 0:
        padded_input.append(Fp(0))

    return rescue_prime_hash(parameters, padded_input)

def rescue_prime_hash( parameters, input_sequence ):
    p, m, capacity, security_level, alpha, alphainv, N, MDS, round_constants = parameters
    rate = m - capacity
    Fp = FiniteField(p)

    assert len(input_sequence) % rate == 0

    # initialize state to all zeros
    state = matrix([[Fp(0)] for i in range(m)])

    # absorbing
    absorb_index = 0
    while absorb_index < len(input_sequence):
        for i in range(0, rate):
            state[i,0] += input_sequence[absorb_index]
            absorb_index += 1
        state = rescue_XLIX_permutation(parameters, state)

    # squeezing
    output_sequence = []
    for i in range(0, rate):
        output_sequence.append(state[i,0])

    return output_sequence

def rescue_XLIX_permutation( parameters, state ):
    p, m, capacity, security_level, alpha, alphainv, N, MDS, round_constants = parameters
    Fp = state[0,0].parent()

    for i in range(N):
        # S-box
        for j in range(m):
            state[j,0] = state[j,0]^alpha
        # mds
        state = MDS * state
        # constants
        for j in range(m):
            state[j,0] += round_constants[i*2*m+j]

        # inverse S-box
        for j in range(m):
            state[j,0] = state[j,0]^alphainv
        # mds
        state = MDS * state
        # constants
        for j in range(m):
            state[j,0] += round_constants[i*2*m+m+j]

    return state

def get_number_of_rounds1( p, m, capacity, security_level, alpha ):
    # get number of rounds for Groebner basis attack
    rate = m - capacity
    dcon = lambda N : floor(0.5 * (alpha-1) * m * (N-1) + 2)
    v = lambda N : m*(N-1) + rate
    target = 2^security_level
    for l1 in range(1, 25):
        if binomial(v(l1) + dcon(l1), v(l1))^2 > target:
            break

    # get number of rounds for differential attack
    l0 = 2*security_level / ( log(1.0*p^(m+1), 2.0) - log(1.0*(alpha - 1)^(m+1), 2.0) )

    # take minimum of numbers, sanity factor, and add 50%
    return ceil(1.5 * max(5, l0, l1))

def rescue_prime_DEC( parameters, input_sequence, output_length ):
    p, m, capacity, security_level, alpha, alphainv, N, MDS, round_constants = parameters
    rate = m - capacity
    Fp = FiniteField(p)

    padded_input = input_sequence + [Fp(1)]
    while len(padded_input) % rate != 0:
        padded_input.append(Fp(0))

    return rescue_prime_sponge(parameters, padded_input, output_length)

def rescue_prime_sponge( parameters, input_sequence, output_length ):
    p, m, capacity, security_level, alpha, alphainv, N, MDS, round_constants = parameters
    rate = m - capacity
    Fp = FiniteField(p)

    assert len(input_sequence) % rate == 0

    # initialize state to all zeros
    state = matrix([[Fp(0)] for i in range(m)])

    # absorbing
    absorb_index = 0
    while absorb_index < len(input_sequence):
        for i in range(0, rate):
            state[i,0] += input_sequence[absorb_index]
            absorb_index += 1
        state = rescue_XLIX_permutation(parameters, state)

    # squeezing
    output_sequence = []
    squeeze_index = 0
    while squeeze_index < output_length:
        for i in range(0, rate):
            output_sequence.append(state[i,0])
            squeeze_index += 1
        if squeeze_index < output_length:
            state = rescue_XLIX_permutation(parameters, state)

    return output_sequence[:output_length]

