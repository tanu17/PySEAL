#!/usr/bin/env python3
#from functools import partial
#import random
import math
import os
import numpy
import time
import seal
import gc
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
#                 GaloisKeys,           \
#                 PolyCRTBuilder,       \
                 ChooserEncoder,       \
                 ChooserEvaluator,     \
                 ChooserPoly


############################ matrixEncryptRows ####################################

class matrixEncryptRows:
	
	def __init__(self, starting_rowNumber, encodedRows):
		# as ciphertext object is not pickleable, new class is created to store data as matrix object of class 
		# self.i used for marking encrypted files to be saved for recovering 

		self.i= starting_rowNumber
		#self.S_block= encodedRows
		self.nrow= len(encodedRows)
		self.ncol= len(encodedRows[0])
		self.encrypt_matrix_row(encodedRows)
		self.X=[]
		#print("Created matrixEncryptRows object")

	def encrypt_matrix_row(self,encodedRows):
		self.X=encrypting_Matrix(encodedRows)

	def __del__(self):
		with open(str(self.i)+'.matrix', 'wb') as f:
			pickle.dump(self,f)

########################## matrixOperations ######################################

class matrixOperations:

	@staticmethod
	def parallel_Multiplication(element1,element2):
		# have to create new ciphertext object as row X column multiplication of matrix enforces no change in matrix elements
		temp=Ciphertext()
		evaluator.multiply(element1, element2, temp)
		return (temp)

	@staticmethod
	def dot_vector(row,col):
		#global num_cores
		# returns dot vector between two vectors
		pool = multiprocessing.Pool(processes=num_cores)
		D = pool.starmap(matrixOperations.parallel_Multiplication, zip(row, col))
		empty_ctext=Ciphertext()
		evaluator.add_many(D,empty_ctext)
		del(D)
		return(empty_ctext)


	@staticmethod
	def matMultiply(T,K):
	# multipliess two matrix and returns a new matrix as result
		X=[]

		if ( type(K[0]) != list ):
			# K is a vector 
			#print("Dimension of T: %dx%d\nDimension of K: %dx1\n"%(len(T),len(T[0]),len(K)))
			for i in range(len(T)):
				# print("K vector: ",i)
				X.append(matrixOperations.dot_vector(T[i], K))


		elif (type(T[0]) != list ):
			# T is a vector instead of matrix
			tK=[list(tup) for tup in zip(*K)]
			#print("Dimension of T: %dx1\nDimension of K: %dx%d\n"%(len(T),len(K),len(K[0])))
			del(K)

			for i in range(len(tK)):
				X.append( matrixOperations.dot_vector(tK[i], T) )

		else:
			tK=[list(tup) for tup in zip(*K)]
			#print("Dimension of T: %dx%d\nDimension of K: %dx%d"%(len(T),len(T[0]),len(K),len(K[0])))

			for i in range(len(T)):
				row_X=[]
				for j in range(len(tK)):
					#print("No vector: %d ; %d"%(i,j))
					row_X.append(matrixOperations.dot_vector(T[i], tK[j]))
				X.append( row_X )
			del(tK)

		return(X)


	@staticmethod
	def multScaler(s, L):
	# multiplies a matrix L with a scaler s, changes the same matrix
		for x in L:
			for y in x:
				evaluator.multiply(y,s)

	@staticmethod
	def trace(M):
	# calculates trace of a matrix 
		print(M)
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
	def subtractMatrix(T,K):
		# subtract the first matrix bt second matrix, the result are overridden in the first matrix itself
		for i in range(len(T)):
			if ( type(T[0]) != list):
				evaluator.sub(T[i], K[i])
			else:
				for j in range(len(T[0])):
					evaluator.sub(T[i][j], K[i][j])

	@staticmethod
	def colSquare_Sum(M):
		# returns sums of squares of each element in a column of a matrix. Returns a vector with length ewual to number of columns in a matrix
		tM = [list(tup) for tup in zip(*M)]
		# last step for finding p values, hance can delete the original matrix
		del(M)
		X=[] 
		rowM=len(tM)
		for i in range(rowM):
			x=Ciphertext()
			encryptor.encrypt(encoderF.encode(0),x)
			for element in (tM[i]):
				y=Ciphertext()
				evaluator.square(element,y)
				evaluator.add(x,y)
			del(y)
			X.append(x)
		return(X)

	@staticmethod
	def inverseMatrix(K):
		# function for finding inverse of the matrix via Cayley-Hamilton theorem 
		# http://scipp.ucsc.edu/~haber/ph116A/charpoly_11.pdf
		n=len(K)
		matrixPower_vector=[K]
		trace_vector=[matrixOperations.trace(K)]

		for i in range(1,n):
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
		# can be parallelized
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
		# have to multiply K_inv with 
		return(K_inv, determinant)

	@staticmethod
	def multiplyDeterminant(M, determinant):
		p=Plaintext()
		# need to send user D so that user can send back -1/D either in encrypted form or decrypted form
		decryptor.decrypt(determinant, p)
		d= (-1/encoderF.decode(p))
		delta=encoderF.encode(d)
		for i in range(len(M)):
			for j in range(len(M[0])):
				evaluator.multiply_plain(M[i][j], delta)


########################## rest of functions neeeded ###########################


def print_plain(D):
	# function to print out all elements in a matrix
	for row in D:
		for values in row:
			p=Plaintext()
			decryptor.decrypt(values, p)
			print(encoderF.decode(p), end=" ")
		print()

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

def encode_Matrix(row):
	x=[]
	for element in row:
		x.append(encoderF.encode(element))
	return(x)

def reconstructMatrix():
#^^^^^^^^^^^^^^^^Need to parallelize reconstruction
	global S_encRECON
	for i in range(0,4,2):
		target=str(i)+'.matrix'
		if os.path.getsize(target)>0:
			with open(target, 'rb') as f:
				print("opened")
				row2=pickle.load(f)
				S_encRECON+=row2.X
				f.close()
		else:
			print("[-] Error occured while reconstructing matrix")

def decrypt_matrix(M):
	M_dec=[]
	for x in M:
		m=[]
		for y in x:
			p=Plaintext()
			decryptor.decrypt(y, p)
			m.append(encoderF.decode(p))
		M.append(m)
	return(M)


def parallel_encryption(element):
	temp=Ciphertext()
	encryptor.encrypt(encoderF.encode(element, temp))
	return(temp)

def encrypting_Matrix(M):
	enc_M=[]
	Enc_pool = multiprocessing.Pool(processes=num_cores)

	# M is vector
	if ( type(M[0]) != list ):
		enc_M= Enc_pool.map(parallel_encryption, M)

	else:
		for i in range(len(M)):
			X.append(Enc_pool.map(parallel_encryption, M[i]))
	del(M)
	del(Enc_pool)
	return(X)

if __name__ == '__main__':

	multiprocessing.freeze_support()

	########################## paramaters required #################################

	parms = EncryptionParameters()
	parms.set_poly_modulus("1x^8192 + 1")
	parms.set_coeff_modulus(seal.coeff_modulus_128(8192))
	parms.set_plain_modulus(1 << 21)
	context = SEALContext(parms)

	encoderF = FractionalEncoder(context.plain_modulus(), context.poly_modulus(), 30, 34, 3) 
	keygen = KeyGenerator(context)
	public_key = keygen.public_key()
	secret_key = keygen.secret_key()

	encryptor = Encryptor(context, public_key)
	evaluator = Evaluator(context)
	decryptor = Decryptor(context, secret_key)

	num_cores = multiprocessing.cpu_count()


	########################## encoding main matrix ################################


	dir_path=os.path.dirname(os.path.realpath(__file__))

	snp = open(dir_path+"/snpMat.txt","r+")
	S=[]
	for row in snp.readlines():
		S.append(row.strip().split())
	S=S[1:]
	S = numpy.array(S).astype(numpy.float)
	S.tolist()

	n= len(S) # n=245
	m= len(S[0])# m=10643

	#encodiing matrix parallely
	pool = multiprocessing.Pool(processes=num_cores)
	S_encoded= pool.map(encode_Matrix, S)

	del(S)
	del(pool)
	gc.collect()
	print("\n[+] Matrix S has been encoded")


	#################### covariate matrix and derivatives ##########################

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
	del(rawX0)

	###################### encrypting tX and y #####################################

	row_tX=len(tX) #row_tX= 3
	col_tX=len(tX[0]) #col_tX= 245

	# encrypting matrix tX

	tX_encrypted= encrypting_Matrix(tX)
	try:
		del(tX)
	except:
		pass
	gc.collect()

	#X=[list(tup) for tup in zip(*tX_encrypted)]

	#encrypting y
	y_encrypted= encrypting_Matrix(y)
	try:
		del(y)
	except:
		pass

	########################### encrypting S #######################################


	tS_encoded=[list(tup) for tup in zip(*S_encoded)]
	del(S_encoded)

	for i in range(0,4,2):
		a= matrixEncryptRows(i, tS_encoded[i:i+2])
		#del(a)
	del(a)
	print("[+] Matrix saved. Will be recovered later")
	S_encRECON=[]
	reconstructMatrix()
	#gc.collect()


	########################## linear regression Pt. 1 ##############################

	print("\n[+] Proceding to homomorphic functions")

	# dimension of X ->  n (number of individuals) rows and 1+k (1+ number of covariates) cols
	# dimension of y -> vector of length n (number of individuals)
	# dimension of S ->  n (number of individuals) rows and m (number of SNPs)


	#restricting to 10 for calculation  purposes
	   #########
	y_encrypted=y_encrypted[:10]
	for j in range(len(tX_encrypted)):
		tX_encrypted[j]=tX_encrypted[j][:10]
		#########

	X=[list(tup) for tup in zip(*tX_encrypted)]
	k= len(X[0]) # k= 3


	U1= matrixOperations.matMultiply(tX_encrypted,y_encrypted)
	print("[+] Calculated U1")
	# dimension of U1 ->  vector of length k+1 (1+ number of covariates)


	cross_X= matrixOperations.matMultiply(tX_encrypted,X)
	print("[+] Calculated cross_X")
	# dimension of cross_X ->  1+k rows and 1+k cols

	print("{=} Size to inverse: ", len(cross_X))
	X_Star, determinant_X_star= matrixOperations.inverseMatrix(cross_X)
	# ^^^^ need to return determinant to user so that user can decrypt and return -1/D
	matrixOperations.multiplyDeterminant(X_Star, determinant_X_star)

	U2=matMultiply(X_Star, U1) 
	del(U1)
	print("[+] Calculated U2")
	# dimension of U2 ->  vector of length k+1 (1+ number of covariates)

	intermediateYStar=matrixOperations.matMultiply(X, U2)
	# dimension of intermediateYStar ->  vector of length n (number of individuals)
	# not returning new matrix after subtraction as the original matrix has to be deleted
	y_star= matrixOperations.subtractMatrix(y,intermediateYStar)
	del(U2)
	del(intermediateYStar) 
	# dimension of y_star -> vector of length n (number of individuals)

	U3= matrixOperations.matMultiply(tX_encrypted,S)
	# dimension of U3 -> 1+k rows and m (number of SNPs)
	print("[+] Calculated U3")
	U4= matrixOperations.matMultiply(X_Star, U3)
	del(U3)
	print("[+] Calculated U4")
	# dimension of U4 -> 1+k rows and m (number of SNPs)


	S_star_temp=matrixOperations.matMultiply(X,U4)
	del(U4)
	S_star=matrixOperations.subtractMatrix(S,S_star_temp)
	del(S_star_temp)
	# dimension of S_star -> n (number of individuals) rows and m (number of SNPs)

	tY_star= [list(tup) for tup in zip(*y_star)]
	b_temp= matrixOperations.matMultiply(tY_star, S_star)
	# dimension of b_temp -> vector of length m (number of SNPs)
	del(tY_star)

	for elementY in y_star:
		evaluator.square(elementY)
	y_star2=y_star
	del(y_star)

	S_star2=matrixOperations.colSquare_Sum(S_star)
	# dimension of S_star2 -> vector of length m (number of SNPs)

	print("[=] Finished with homomorphic functions")

	########################## linear regression Pt. 2 ##############################
	######## after returning some matrix to decrypt and to evaluate by user #########

	print("\n[+] User-end calculations started")

	b_temp_dec= decrypt_matrix(b_temp)
	S_star2_dec= decrypt_matrix(S_star2)
	y_star2_dec= decrypt_matrix(y_star2)

	del(b_temp)
	del(S_star2)
	del(y_star2)

	b=numpy.divide(b_temp, S_star2)
	# dimension of b -> vector of length m (number of SNPs)

	b2= numpy.square(b)
	sig = numpy.subtract(numpy.sum(y_star2_dec),numpy.multiply(b2,S_star2_dec)) / (n-k-2)

	err= numpy.sqrt(sig*(1/S_star2_dec))

	f=numpy.divide(b,err)
	f=-abs(f)
	p=[]
	for x in f:
		p.append( 1 - (norm(0, 1).cdf(x)) )
	logp= -numpy.log10(p)
	logp.tolist()

	print("\n[+] P-Values: ")
	print(len(logp))
