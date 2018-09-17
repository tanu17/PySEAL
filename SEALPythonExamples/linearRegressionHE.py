#!/usr/bin/env python3
from functools import partial
#import random
import math
import os
import numpy
import time
import itertools
import seal
import gc
import scipy
from scipy.stats import norm
import multiprocessing 
try:
    import cPickle as pickle
except ModuleNotFoundError:
    import pickle

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


########################## matrixOperations ######################################

class matrixOperations:

	@staticmethod
	# returns dot vector of two vectors by successive multiplication and final addition, faster than one-by-one addition
	def dot_vector(row,col):
		D=[]
		for i in range(len(row)):
			temp=Ciphertext()
			evaluator.multiply(row[i], col[i], temp)
			D.append(temp)
			#D.append(pool.starmap(matrixOperations.parallel_Multiplication, zip(row, col)))
		#empty_ctext=Ciphertext()
		evaluator.add_many(D,temp)	
		return(temp)

	"""
	@staticmethod
	def parallel_Multiplication(element1,element2):
		# have to create new ciphertext object as row X column multiplication of matrix enforces no change in matrix elements
		temp=Ciphertext()
		evaluator.multiply(element1, element2, temp)
		return (temp)

	@staticmethod
	def dot_vector_Parallel(row,col):
		pool = multiprocessing.Pool(processes=num_cores)
		D = pool.starmap(matrixOperations.parallel_Multiplication, zip(row, col))
		empty_ctext=Ciphertext()
		evaluator.add_many(D,empty_ctext)
		del(D)
		pool.close()
		return(empty_ctext)
	"""

	@staticmethod
	# multipliess two matrix and returns a new matrix as result
	def matMultiply(T,K):
		X=[]
		Mul_pool= multiprocessing.Pool(processes=num_cores)

		# K is a vector
		if ( type(K[0]) != list ):
			#print("Dimension of T: %dx%d\nDimension of K: %dx1"%(len(T),len(T[0]),len(K)))
			X= Mul_pool.starmap(matrixOperations.dot_vector, zip(T, itertools.repeat(K)))

		# T is a vector
		elif ( type(T[0]) != list ):
			#print("Dimension of T: %dx1\nDimension of K: %dx%d\n"%(len(T),len(K),len(K[0])))
			tK=[list(tup) for tup in zip(*K)]
			X= Mul_pool.starmap(matrixOperations.dot_vector, zip(itertools.repeat(T), tK))
			del(tK)

		else:
			#print("Dimension of T: %dx%d  Dimension of K: %dx%d"%(len(T),len(T[0]),len(K),len(K[0])))
			tK=[list(tup) for tup in zip(*K)]
			for i in range(len(T)):
				row_x = Mul_pool.starmap(matrixOperations.dot_vector, zip(itertools.repeat(T[i]), tK))
				X.append( row_x )
			del(tK)

		Mul_pool.close()
		return(X)


	@staticmethod
	# multiplies a matrix L with a scaler s, changes the same matrix
	def multScaler(s, L):
		for x in L:
			for y in x:
				evaluator.multiply(y,s)


	@staticmethod
	# calculates trace of a matrix 
	def trace(M):
		t=Ciphertext(M[0][0])
		for i in range(1,len(M)):
			evaluator.add(t,M[i][i])
		return (t)


	@staticmethod
	def iden_matrix(n):
	# returns an identity matrix of size n 
		X=[]
		for i in range(n):
			x=[]
			for j in range(n):
				encrypted_data= Ciphertext()
				if (i==j):
					encryptor.encrypt(encoderF.encode(1), encrypted_data)
				else:
					encryptor.encrypt(encoderF.encode(0), encrypted_data)
				x.append(encrypted_data)
			X.append(x)
		return(X)


	@staticmethod
	def parallel_subtraction(element1,element2):
		evaluator.sub(element1,element2)
		return(element1)


	@staticmethod
	# subtracts the first matrix by second matrix, the result are returned in new matrix
	def subtractMatrix(T,K):
		Sub_pool = multiprocessing.Pool(processes=num_cores)
		X=[]
		if ( type(T[0]) != list):
			X=Sub_pool.starmap(matrixOperations.parallel_subtraction, zip(T,K))
		else:
			for i in range(len(T)):
				X.append(Sub_pool.starmap(matrixOperations.parallel_subtraction,zip(T[i],K[i])))
		Sub_pool.close()
		del(T)
		#Sub_pool.join()
		return(X)


	@staticmethod
	# returns sums of squares of each element in a column of a matrix. Returns a vector with length equal to number of columns in a matrix
	def colSquare_Sum(M):
		tM = [list(tup) for tup in zip(*M)]
		# last step for finding p values, hance can delete the original matrix
		del(M)
		X=[]
		rowM=len(tM)
		for i in range(rowM):
			x=Ciphertext()
			encryptor.encrypt(encoderF.encode(0),x)
			for j in range(len(tM[i])):
				y=Ciphertext()
				evaluator.square(tM[i][j])
				#~~~~~~~~~~~~~ can have need to relinearize or changing parameter ~~~~~~~~~~
				evaluator.add(x,tM[i][j])
			del(y)
			X.append(x)
		del(tM)
		return(X)


	@staticmethod
	def inverseMatrix(K):
		# function for finding inverse of the matrix via Cayley-Hamilton theorem 
		# http://scipp.ucsc.edu/~haber/ph116A/charpoly_11.pdf
		n=len(K)
		matrixPower_vector=[K]
		trace_vector=[matrixOperations.trace(K)]

		for i in range(1,n):
#~~~~~~~~~~~~~ can have need to relinearize or changing parameter ~~~~~~~~~~
			matrixPower_vector+=[matrixOperations.matMultiply(K, matrixPower_vector[i-1])]
			trace_vector+=[matrixOperations.trace(matrixPower_vector[i])]

		# c vector is coefficient vector for powers of matrix in characteristic equation
		c=[Ciphertext(trace_vector[0])]
		evaluator.negate(c[0])

		# application of  newton identities to find coefficient {refer to paper cited above}
		for i in range(1,n):
			c_new=Ciphertext(trace_vector[i])
			for j in range(i):
				tc=Ciphertext()
				evaluator.multiply(trace_vector[i-1-j],c[j],tc)
				evaluator.add(c_new,tc)
			evaluator.negate(c_new)
			frac=encoderF.encode(1/(i+1))
			evaluator.multiply_plain(c_new,frac)
			c.append(c_new)

		matrixPower_vector=[matrixOperations.iden_matrix(n)]+matrixPower_vector
		c0=Ciphertext()
		encryptor.encrypt(encoderF.encode(1),c0)
		c=[c0]+c

		K_inv=[]
		# creating null matrix of size n*n
#~~~~~~~~~~~~~ can be parallelized
		for i in range(n):
			k_i=[]
			for j in range(n):
				enc_dat=Ciphertext()
				encryptor.encrypt(encoderF.encode(0), enc_dat)
				k_i.append(enc_dat)
			K_inv.append(k_i)

		# Adding the matrices multiplied by their coefficients
		for i in range(len(matrixPower_vector)-1):
			for j in range(len(c)):
				if (i+j == n-1):
					matrixOperations.multScaler(c[j],matrixPower_vector[i])
					for t in range(n):
						for s in range(n):
							evaluator.add(K_inv[t][s],matrixPower_vector[i][t][s])

		determinant= c[n]
		# have to multiply K_inv with (-1/determinant) as -k_inv * determinant is returned
		return(K_inv, determinant)


	@staticmethod
	def parallel_plainMultiplication(element,D):
		# have to create new ciphertext object as row X column multiplication of matrix enforces no change in matrix elements
		evaluator.multiply_plain(element, D)
		return(element)

	@staticmethod
	def multiplyDeterminant(M, determinant):
		p=Plaintext()
		# need to send user D so that user can send back -1/D either in encrypted form or decrypted form
		decryptor.decrypt(determinant, p)
		d= (-1/encoderF.decode(p))
		delta=encoderF.encode(d)
		plainMul_pool = multiprocessing.Pool(processes=num_cores)
		del(p)
		X=[]
		for i in range(len(M)):
			X.append(plainMul_pool.map(partial(matrixOperations.parallel_plainMultiplication,D= delta), M[i]))
		plainMul_pool.close()
		plainMul_pool.join()
		return(X)




########################## rest of functions neeeded ###########################


def print_plain(D):
    # function to print out all elements in a matrix/vector
    D_new= decrypt_matrix(D)
    for row in D_new:
    	print(row)
    del(D_new)

def print_value(s):
	# print value of an encoded ciphertext
	p=Plaintext()
	decryptor.decrypt(s,p)
	print(encoderF.decode(p))

def normalize(M):
	# normalizes raw data on user end
	for i in range(len(M)):
		maxR=max(M[i])
		minR=min(M[i])
		for j in range(len(M[i])):
			M[i][j]= (M[i][j] - minR) / float(maxR-minR)
	return(M)


def parallel_decryption(element):
	p=Plaintext()
	decryptor.decrypt(element, p)
	temp= encoderF.decode(p)
	return(temp)

def parallel_encryption(element):
	temp=Ciphertext()
	encryptor.encrypt(encoderF.encode(element), temp)
	return(temp)

def decrypt_matrix(M):
	M_dec= []
	dec_Pool= multiprocessing.Pool(processes=num_cores)

	# M is vector
	if ( type(M[0]) != list ):
		M_dec= dec_Pool.map(parallel_decryption, M)
	else:
		for i in range(len(M)):
			M_dec.append(dec_Pool.map(parallel_decryption, M[i]))
	del(M)
	dec_Pool.close()
	dec_Pool.join()
	return(M_dec)

def encrypting_Matrix(M):
	enc_M=[]
	Enc_pool = multiprocessing.Pool(processes=num_cores)

	# M is vector
	if ( type(M[0]) != list ):
		enc_M= Enc_pool.map(parallel_encryption, M)

	else:
		for i in range(len(M)):
			enc_M.append(Enc_pool.map(parallel_encryption, M[i]))
	del(M)
	Enc_pool.close()
	Enc_pool.join()
	return(enc_M)


if __name__ == '__main__':

	multiprocessing.freeze_support()

	########################## paramaters required #################################

	parms = EncryptionParameters()
	parms.set_poly_modulus("1x^16384 + 1")
	parms.set_coeff_modulus(seal.coeff_modulus_128(16384))
	parms.set_plain_modulus(1 << 16)
	context = SEALContext(parms)

	encoderF = FractionalEncoder(context.plain_modulus(), context.poly_modulus(), 30, 34, 3) 
	keygen = KeyGenerator(context)
	public_key = keygen.public_key()
	secret_key = keygen.secret_key()

	encryptor = Encryptor(context, public_key)
	evaluator = Evaluator(context)
	decryptor = Decryptor(context, secret_key)

	num_cores = multiprocessing.cpu_count() 


	########################## processing main matrix ################################

	t1 = time.time()

	dir_path=os.path.dirname(os.path.realpath(__file__))

	snp = open(dir_path+"/snpMat.txt","r+")
	S=[]
	for row in snp.readlines():
		S.append(row.strip().split())
	S=S[1:]
	S = numpy.array(S).astype(numpy.float)
	S.tolist()

	n= len(S) # n=245
	m= len(S[0])# m=1064

	gc.collect()

	################ processing covariate matrix and derivatives ######################

	covariate= open(dir_path+"/covariates.csv")
	# appending with average in data where NA is there
	cov=[]
	for row in covariate.readlines():
		cov.append(row.strip().split(","))
	cov=cov[1:]
	cov_sum=[[0,0],[0,0],[0,0]]
	for i in range (len(cov)):
		for j in range(2,5):
			if cov[i][j]!="NA":
				cov_sum[j-2][0]+=int(cov[i][j])
				cov_sum[j-2][1]+=1.0

	for i in range(len(cov_sum)):
		cov_sum[i]=cov_sum[i][0]/cov_sum[i][1]
	cov_new=[]
	for i in range(len(cov)):
		cov_new_row=[]
		for j in range(1,5):
			if cov[i][j] =="NA":
				cov_new_row.append(cov_sum[j-2])
			else:
				cov_new_row.append(int(cov[i][j]))
		cov_new.append(cov_new_row)

	# splitting off of covariate matrix
	Tcov= [list(tup) for tup in zip(*cov_new)]
	del(cov_new)
	gc.collect()
	y= Tcov[0]
	rawX0= Tcov[1:4]

	rawX0=normalize(rawX0)
	# have to find a way to make normalize an encrytped function

	tX=[[1]*245]+ rawX0

	###################### encrypting tX and y #####################################
	print("[+] Starting enrypting matrices")
	row_tX=len(tX) #row_tX= 3
	col_tX=len(tX[0]) #col_tX= 245

	# encrypting matrix tX

	tX_encrypted= encrypting_Matrix(tX)
	try:
		del(rawX0)
		del(tX)
	except:
		pass
	gc.collect()

	X=[list(tup) for tup in zip(*tX_encrypted)]
	print("[+] Encrypted X")

	#encrypting y
	y_encrypted= encrypting_Matrix(y)
	try:
		del(y)
		del(tX_encrypted)
	except:
		pass


	print("[+] Encrypted y")

	########################### encrypting S #######################################

	tS=[list(tup) for tup in zip(*S)]
	#S_encRECON=[]
	#S_enc=[]

	del(S)

	#for i in range(0,,2):
		#a= matrixEncryptRows(tS[i:i+2])
		#del(a)
	S_enc=encrypting_Matrix(tS[0:8 ])
	#del(a)
	print("[+] Matrix S encrytped")
	S_enc=[list(tup) for tup in zip(*S_enc)]
	########################## linear regression Pt. 1 ##############################

	print('Time cost: {} seconds'.format(time.time()-t1))
	gc.collect()
	t2 = time.time()

	print("\n[+] Proceding to homomorphic functions")

	# dimension of X ->  n (number of individuals) rows and 1+k (1+ number of covariates) cols
	# dimension of y -> vector of length n (number of individuals)
	# dimension of S ->  n (number of individuals) rows and m (number of SNPs)

	k= len(X[0]) # k= 3
	"""

	U1= matrixOperations.matMultiply(tX_encrypted,y_encrypted)
	print("Noise budget of U1[2]:"+ str(decryptor.invariant_noise_budget(U1[2])))
	print("[+] Calculated U1")
	# dimension of U1 ->  vector of length k+1 (1+ number of covariates)
	"""
	U1= encrypting_Matrix([ 108.0 ,42.37975927,44.43704984,52.77309281])

	"""
	cross_X= matrixOperations.matMultiply(tX_encrypted,X)
	print("Noise budget of cross_X[1][1]:"+ str(decryptor.invariant_noise_budget(cross_X[1][1])))
	print("[+] Calculated cross_X")
	# dimension of cross_X ->  1+k rows and 1+k cols
	"""
	cross_X= encrypting_Matrix( [[ 245.0,91.26565954,95.24248535,118.42642904],[  91.26565954 ,39.67640403 ,35.41864926,43.98636322] ,[  95.24248535 ,35.41864926 ,41.46235818 ,48.28531555],[ 118.42642904,43.98636322,48.28531555 ,61.48756469]])

	"""
	print("{=} Size to inverse: ", len(cross_X))
	X_Star, determinant_X_star= matrixOperations.inverseMatrix(cross_X)
	X_star=matrixOperations.multiplyDeterminant(X_Star, determinant_X_star)
	print("Noise budget of X_Star[1][1]:"+ str(decryptor.invariant_noise_budget(X_Star[1][1])))
	print("[+] Calculated inverse")
	"""

	X_Star= encrypting_Matrix( [[ 0.09094401, -0.06817554 ,-0.04070801 ,-0.09442204],[-0.06817554,  0.17621681, -0.00043033,  0.00558531],[-0.04070801, -0.00043033,  0.30799719, -0.16315345],[-0.09442204,  0.00558531, -0.16315345,  0.32224894]])
	gc.collect()

	"""
	U2=matrixOperations.matMultiply(X_Star, U1) 
	print("Noise budget of U2[1]:"+ str(decryptor.invariant_noise_budget(U2[1])))
	print("[+] Calculated U2")
	# dimension of U2 ->  vector of length k+1 (1+ number of covariates)
	"""
	del(U1)

	U2= encrypting_Matrix([ 0.14080326, 0.38069974, 0.6616717, -0.20486026])

	intermediateYStar=matrixOperations.matMultiply(X, U2)
	del(U2)
	# dimension of intermediateYStar ->  vector of length n (number of individuals)
	# not returning new matrix after subtraction as the original matrix has to be deleted
	y_star=matrixOperations.subtractMatrix(y_encrypted,intermediateYStar)
	print("Noise budget of Y*[3]:"+ str(decryptor.invariant_noise_budget(y_encrypted[3])))
	print("Noise budget of Y*[3]:"+ str(decryptor.invariant_noise_budget(y_star[3])))
	print("[+] Calculated Y*\n")
	# dimension of y_star -> vector of length n (number of individuals)
	del(intermediateYStar)
	gc.collect()


	U3= matrixOperations.matMultiply([list(tup) for tup in zip(*X)],S_enc)
	# dimension of U3 -> 1+k rows and m (number of SNPs)
	print("Noise budget of U3[1][3]:"+ str(decryptor.invariant_noise_budget(U3[1][3])))
	print("[+] Calculated U3\n")

	U4= matrixOperations.matMultiply(X_Star, U3)
	del(U3)
	print("Noise budget of U4[1][3]:"+ str(decryptor.invariant_noise_budget(U4[1][3])))
	print("[+] Calculated U4\n")
	# dimension of U4 -> 1+k rows and m (number of SNPs)

	gc.collect()
	S_star_temp=matrixOperations.matMultiply(X,U4)
	del(U4)
	print("Noise budget of S_star_temp[1][3]:"+ str(decryptor.invariant_noise_budget(S_star_temp[1][3])))
	S_star=matrixOperations.subtractMatrix(S_enc,S_star_temp)
	try:
		# S-enc should be deleted first
		del(S_enc)
		del(S_star_temp)
	except:
		pass
	print("Noise budget of S*[1][3]:"+ str(decryptor.invariant_noise_budget(S_star[1][3])))
	print("[+] Calculated S*\n")

	# dimension of S_star -> n (number of individuals) rows and m (number of SNPs)

	b_temp= matrixOperations.matMultiply(S_star,y_star)
	# dimension of b_temp -> vector of length m (number of SNPs)

	print("^"*30)
	print_plain(b_temp)
	S_star2=matrixOperations.colSquare_Sum(S_star)
	del(S_star)
	# dimension of S_star2 -> vector of length m (number of SNPs)

	print("[=] Finished with homomorphic functions")

	print('Time cost: {} seconds'.format(time.time()-t2))

	t3 = time.time()

	########################## linear regression Pt. 2 ##############################
	######## after returning some matrix to decrypt and to evaluate by user #########

	gc.collect()
	print("\n[+] User-end calculations started")

	b_temp_dec= decrypt_matrix(b_temp)
	S_star2_dec= decrypt_matrix(S_star2)
	y_str= decrypt_matrix(y_star)

	y_star2_dec= numpy.square(y_str)


	try:
		del(b_temp)
		del(S_star2)
		del(y_star)
	except:
		pass

	b=numpy.divide(b_temp_dec, S_star2_dec)
	print("\nb:\n",b)
	# dimension of b -> vector of length m (number of SNPs)

	b2= numpy.square(b)
	sig = numpy.subtract(numpy.sum(y_star2_dec),numpy.multiply(b2,S_star2_dec)) / (n-k-2)

	err= numpy.sqrt(sig*(numpy.reciprocal(S_star2_dec)))

	f=numpy.divide(b,err)
	f=-abs(f)
	p=[]
	for x in f:
		p.append( 1 - (norm(0, 1).cdf(x)) )
	logp= -numpy.log10(p)
	logp.tolist()

	print("\n[+] P-Values: ")
	print(len(logp))
	print("\n"+"_"*30 + "\nlogp:\n")
	print(logp)
