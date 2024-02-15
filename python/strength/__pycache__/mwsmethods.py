import numpy as np
import matplotlib.pyplot as plt

def method1(sum, deg, am1, am2):
    return (deg-am1)/(sum-am1-am2)

def method2(sum, deg, am):
    return (deg-am)/(sum-am)

def get_params():
    am2 = np.random.randint(1, 10)
    am1 = np.random.randint(am2, 15)
    deg = np.random.randint(am1+am2+1, 50)
    sum = np.random.randint(deg+1, 70)

    return deg, sum, am1, am2

count1 = 0
count2 = 0

count1_alt = 0

heur = 0
heur_wrong = 0

for _ in range(10000):

    deg, sum, am1, am2 = get_params()

    # for elm in [deg, sum, am1, am2]:
    #     print(elm, end=" ")
    # print()

    # print("Method 1: ", method1(sum, deg, am1, am2))
    # print("Method 2: ", method2(sum, deg, am2))

    if method1(sum, deg, am1, am2) > method2(sum, deg, am2):
        count1 += 1
    elif method1(sum, deg, am1, am2) < method2(sum, deg, am2):
        count2 += 1

    if -am1*sum > -deg*am1-am2*sum + am2**2:
        count1_alt += 1

    if am1 < 2*am2:
        heur += 1

    if not (-am1*sum > -deg*am1-am2*sum + am2**2) and am1 < 2*am2:
        heur_wrong += 1


    

print("Method 1 wins: ", count1)
print("Method 2 wins: ", count2)

print(count1_alt)
assert count1 == count1_alt

print(heur)
print(heur_wrong)
