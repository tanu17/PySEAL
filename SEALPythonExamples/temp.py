"""
Python Parallel Processing (in 60 seconds or less)
https://dbader.org/blog/python-parallel-computing-in-60-seconds

import collections
import multiprocessing

Scientist = collections.namedtuple('Scientist', ['name','born'])

scientists = (
    Scientist(name='Ada Lovelace', born=1815),
    Scientist(name='Emmy Noether', born=1882),
    Scientist(name='Marie Curie', born=1867),
    Scientist(name='Tu Youyou', born=1930),
    Scientist(name='Ada Yonath', born=1939),
    Scientist(name='Vera Rubin', born=1928),
    Scientist(name='Sally Ride', born=1951),
)

def process_item(item):
    return {
        'name': item.name,
        'age': 2017 - item.born
    }

pool = multiprocessing.Pool()
result = pool.map(process_item, scientists)

print(tuple(result))



from multiprocessing import Pool

def square(x):  
    # calculate the square of the value of x
    return x*x

if __name__ == '__main__':

    # Define the dataset
    dataset = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

    # Output the dataset
    print ('Dataset: ' + str(dataset))

    # Run this with a pool of 5 agents having a chunksize of 3 until finished
    agents = 5
    chunksize = 3
    with Pool(processes=agents) as pool:
        result = pool.map(square, dataset, chunksize)

    # Output the result
    print ('Result:  ' + str(result))

"""
import multiprocessing
 
def doubleTrouble(number):
    return number * 2
 
if __name__ == '__main__':
    numbers = [5, 10, 20]
    pool = multiprocessing.Pool(processes=3)
    num_cores = multiprocessing.cpu_count()
    print(num_cores)

