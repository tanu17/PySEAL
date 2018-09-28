import time
import random
import threading
import seal
import multiprocessing 

from seal import ChooserEvaluator,     \
                 Ciphertext,           \
                 Decryptor,            \
                 Encryptor,            \
                 EncryptionParameters, \
                 Evaluator,            \
                 IntegerEncoder,       \
                 FractionalEncoder,    \
                 KeyGenerator,         \
                 MemoryPoolHandle,     \
                 Plaintext,            \
                 SEALContext,          \
                 EvaluationKeys,       \
                 GaloisKeys,           \
                 PolyCRTBuilder,       \
                 ChooserEncoder,       \
                 ChooserEvaluator,     \
                 ChooserPoly


def example_batching():
    print_example_banner("Example: Batching with PolyCRTBuilder");

    parms = EncryptionParameters()
    parms.set_poly_modulus("1x^4096 + 1")
    parms.set_coeff_modulus(seal.coeff_modulus_128(4096))

    parms.set_plain_modulus(40961)

    context = SEALContext(parms)
    print_parameters(context)

    qualifiers = context.qualifiers()

    keygen = KeyGenerator(context)
    public_key = keygen.public_key()
    secret_key = keygen.secret_key()

    gal_keys = GaloisKeys()
    keygen.generate_galois_keys(30, gal_keys)

    #ev_keys = EvaluationKeys()
    #keygen.generate_evaluation_keys(30, ev_keys)

    encryptor = Encryptor(context, public_key)
    evaluator = Evaluator(context)
    decryptor = Decryptor(context, secret_key)

    crtbuilder = PolyCRTBuilder(context)

    slot_count = (int)(crtbuilder.slot_count())
    row_size = (int)(slot_count / 2)
    print("Plaintext matrix row size: " + (str)(row_size))

    def print_matrix(matrix):
        print("")
        print_size = 5

        current_line = "    ["
        for i in range(print_size):
            current_line += ((str)(matrix[i]) + ", ")
        current_line += ("..., ")
        for i in range(row_size - print_size, row_size):
            current_line += ((str)(matrix[i]))
            if i != row_size-1: current_line += ", "
            else: current_line += "]"
        print(current_line)

        current_line = "    ["
        for i in range(row_size, row_size + print_size):
            current_line += ((str)(matrix[i]) + ", ")
        current_line += ("..., ")
        for i in range(2*row_size - print_size, 2*row_size):
            current_line += ((str)(matrix[i]))
            if i != 2*row_size-1: current_line += ", "
            else: current_line += "]"
        print(current_line)
        print("")

    #     [ 0,  1,  2,  3,  0,  0, ...,  0 ]
    #     [ 4,  5,  6,  7,  0,  0, ...,  0 ]
    pod_matrix = [0]*slot_count
    pod_matrix[0] = 0
    pod_matrix[1] = 1
    pod_matrix[2] = 2
    pod_matrix[3] = 3
    pod_matrix[row_size] = 4
    pod_matrix[row_size + 1] = 5
    pod_matrix[row_size + 2] = 6
    pod_matrix[row_size + 3] = 7

    print("Input plaintext matrix:")
    print_matrix(pod_matrix)

    plain_matrix = Plaintext()
    crtbuilder.compose(pod_matrix, plain_matrix)

    encrypted_matrix = Ciphertext()
    print("Encrypting: ")
    encryptor.encrypt(plain_matrix, encrypted_matrix)
    print("Done")
    print("Noise budget in fresh encryption: " +
        (str)(decryptor.invariant_noise_budget(encrypted_matrix)) + " bits")

    pod_matrix2 = []
    for i in range(slot_count): pod_matrix2.append((i % 2) + 1)
    plain_matrix2 = Plaintext()
    crtbuilder.compose(pod_matrix2, plain_matrix2)
    print("Second input plaintext matrix:")
    print_matrix(pod_matrix2)

    print("Adding and squaring: ")
    evaluator.add_plain(encrypted_matrix, plain_matrix2)
    evaluator.square(encrypted_matrix)
    evaluator.relinearize(encrypted_matrix, ev_keys)
    print("Done")

    print("Noise budget in result: " + (str)(decryptor.invariant_noise_budget(encrypted_matrix)) + " bits")

    plain_result = Plaintext()
    print("Decrypting result: ")
    decryptor.decrypt(encrypted_matrix, plain_result)
    print("Done")

    crtbuilder.decompose(plain_result)
    pod_result = [plain_result.coeff_at(i) for i in range(plain_result.coeff_count())]

    print("Result plaintext matrix:")
    print_matrix(pod_result)

    encryptor.encrypt(plain_matrix, encrypted_matrix)
    print("Unrotated matrix: ")
    print_matrix(pod_matrix)
    print("Noise budget in fresh encryption: " +
        (str)(decryptor.invariant_noise_budget(encrypted_matrix)) + " bits")

    # Now rotate the rows to the left 3 steps, decrypt, decompose, and print.
    evaluator.rotate_rows(encrypted_matrix, 3, gal_keys)
    print("Rotated rows 3 steps left: ")
    decryptor.decrypt(encrypted_matrix, plain_result)
    crtbuilder.decompose(plain_result)
    pod_result = [plain_result.coeff_at(i) for i in range(plain_result.coeff_count())]
    print_matrix(pod_result)
    print("Noise budget after rotation" +
        (str)(decryptor.invariant_noise_budget(encrypted_matrix)) + " bits")

    # Rotate columns (swap rows), decrypt, decompose, and print.
    evaluator.rotate_columns(encrypted_matrix, gal_keys)
    print("Rotated columns: ")
    decryptor.decrypt(encrypted_matrix, plain_result)
    crtbuilder.decompose(plain_result)
    pod_result = [plain_result.coeff_at(i) for i in range(plain_result.coeff_count())]
    print_matrix(pod_result)
    print("Noise budget after rotation: " +
        (str)(decryptor.invariant_noise_budget(encrypted_matrix)) + " bits")

    # Rotate rows to the right 4 steps, decrypt, decompose, and print.
    evaluator.rotate_rows(encrypted_matrix, -4, gal_keys)
    print("Rotated rows 4 steps right: ")
    decryptor.decrypt(encrypted_matrix, plain_result)
    crtbuilder.decompose(plain_result)
    pod_result = [plain_result.coeff_at(i) for i in range(plain_result.coeff_count())]
    print_matrix(pod_result)
    print("Noise budget after rotation: " +
        (str)(decryptor.invariant_noise_budget(encrypted_matrix)) + " bits")


def main():
    example_batching()

    th_count = ((int)(input('Thread count: ')))
    if th_count > 0: example_performance_mt(th_count)
    else: print('Invalid thread count.')
    input('Press ENTER to exit')

def print_example_banner(title, ch='*', length=78):
    spaced_text = ' %s ' % title
    print(spaced_text.center(length, ch))

def print_parameters(context):
    print("/ Encryption parameters:")
    print("| poly_modulus: " + context.poly_modulus().to_string())
    # Print the size of the true (product) coefficient modulus
    print("| coeff_modulus_size: " + (str)(context.total_coeff_modulus().significant_bit_count()) + " bits")
    print("| plain_modulus: " + (str)(context.plain_modulus().value()))
    print("| noise_standard_deviation: " + (str)(context.noise_standard_deviation()))

if __name__ == '__main__':
    main()
