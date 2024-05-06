import numpy as np
import copy

# np.random.seed(0)

def generate_constraint(max_vars):
    length = np.random.randint(max_vars // 3, max_vars)
    constraint = np.random.randint(1, 10, length)
    # pad constraint with 0s
    constraint = np.sort(constraint)
    sum_constraint = sum(constraint)
    constraint = np.append(constraint, np.random.randint(constraint[-1], sum_constraint))
    constraint = np.append(np.zeros(max_vars - length), constraint)

    return constraint[::-1]

def const_len(const):
    return len(np.nonzero(const)[0]) - 1

def normalised_len(const):
    return const_len(const) / (len(const)-1)

def generalised_slack(constraint):
    return sum(constraint[1:]) - constraint[0]

def normalised_slack(constraint):
    return 1 - generalised_slack(constraint) / sum(constraint[1:]) # 1 - (sum-deg)/sum = deg/sum = heur

def heuristic(constraint):
    return constraint[0]/sum(constraint[1:])

def heuristic_with_stddev(constraint, value=0.5):
    return heuristic(constraint) * (1 - np.std(np.array(constraint[1:])/constraint[1]) / value)

def heuristic_with_length(constraint, value=56): # this loses the property of > 1 being unsatisfiable
    return heuristic(constraint) * (1 + const_len(constraint) / value)

def heuristic_with_size(constraint, value=200):
    return heuristic(constraint) * (1 - constraint[1] / value)

def heuristic_with_size_and_length(constraint, value=130):
    return heuristic_with_size(constraint, value) * (1 + const_len(constraint) / value)

def normalised_size(constraint):
    return constraint[1] / constraint[0]

def min_vars_to_satisfy(constraint):
    sum = 0
    i = 0
    while sum < constraint[0]:
        i += 1
        sum += constraint[i]
    return i

def norm_min_sat(constraint):
    return min_vars_to_satisfy(constraint) / (len(constraint) - 1)

def max_sat(constraint):
    sum = 0
    i = 1
    while sum < constraint[0]:
        i += 1
        sum += constraint[-i]
    return i - 1

def norm_max_sat(constraint):
    return max_sat(constraint) / (len(constraint) - 1)

def get_stddev(constraint):
    return np.std(np.array(constraint[1:])/constraint[0])

def get_stddev_with_min_sat(constraint):
    min_sat = min_vars_to_satisfy(constraint)
    constraint = constraint[:min_sat+1]
    return get_stddev(constraint) 

def get_stddev_with_length(constraint):
    length = const_len(constraint)
    constraint = constraint[:length+1]
    return get_stddev(constraint)

def get_slack(constraint, truth_table):
    table_copy = copy.deepcopy(truth_table)
    table_copy = table_copy != 0
    return sum(constraint[1:] * table_copy) - constraint[0]

def assigned_slack(constraint, truth_table):
    table_copy = copy.deepcopy(truth_table)
    table_copy = table_copy == 1
    return sum(constraint[1:] * table_copy) - constraint[0]

def propagate(constraint, truth_table):
    table_copy = copy.deepcopy(truth_table)
    slack = get_slack(constraint, table_copy)
    # print(f'Slack: {slack}')
    # set truth table to 1 if element is larger than slack
    mask = (constraint[1:] > slack) & (table_copy == -1)
    table_copy[mask] = 1
    return table_copy

def decide(truth_table, value):
    table_copy = copy.deepcopy(truth_table)
    # find the first -1 in the truth table
    # print(f'truth table: {table_copy}')
    index = np.where(table_copy == -1)[0][0]
    # set the value
    table_copy[index] = value
    return table_copy

def solve(constraint, truth_table=None):
    if truth_table is None:
        truth_table = np.zeros(len(constraint) - 1) - 1

    # print(truth_table)
   
    truth_table = propagate(constraint, truth_table)

    # print(f'table after propagation: {truth_table}')
    if assigned_slack(constraint, truth_table) >= 0:
        # number of -1s in truth table
        # print(f'table when returning: {truth_table}')
        return 2**len(np.where(truth_table == -1)[0])
    
    return solve(constraint, decide(truth_table, 0)) + solve(constraint, decide(truth_table, 1))

def sols_cut(const):
    nb_sols = solve(const)
    max_vars = len(const) - 1
    return 2**max_vars - nb_sols

if __name__ == '__main__':

    # # print(generate_constraint(10))
    # const0 = [3, 3, 0, 0]
    # const1 = [3, 2, 1, 0]
    # const2 = [3, 2, 1, 1] # 5 sols cut
    # const3 = [3, 1, 1, 1]
    # const4 = [3, 2, 2, 0] # 6 sols cut
    # const5 = [3, 2, 2, 1]
    # const6 = [3, 2, 2, 2]
    # const7 = [3, 3, 3, 0]
    # const8 = [3, 3, 3, 3]

    # consts = [const0, const1, const2, const3, const4, const5, const6, const7, const8]

    # # const0 = np.array([12, 6, 3, 3, 1, 0, 0, 0, 0, 0, 0])
    # # const1 = np.array([12, 4, 3, 3, 1, 1, 1, 0, 0, 0, 0])
    # # const2 = np.array([12, 4, 3, 3, 2, 1, 0, 0, 0, 0, 0])
    # # const3 = np.array([12, 4, 3, 3, 2, 1, 1, 1, 0, 0, 0])
    # # const4 = np.array([12, 4, 3, 3, 2, 2, 1, 0, 0, 0, 0])

    # # consts = [const0, const1, const2, const3, const4]

    # const0 = np.array([15, 10, 8, 7, 7, 5, 3, 0, 0, 0, 0])
    # const1 = np.array([15, 8, 7, 7, 5, 5, 3, 3, 2, 0, 0])
    # const2 = np.array([15, 8, 7, 7, 5, 5, 5, 3, 0, 0, 0])
    # const3 = np.array([15, 10, 5, 5, 5, 5, 3, 3, 2, 2, 0])

    # consts = [const0, const1, const2, const3]

    const0 =  [5] + [1 for _ in range(10)] # Sum i Cr 10 {i elm 5..10}
    const1 = [9, 9] + [1 for _ in range(9)] 
    const2 = [6, 8] + [1 for _ in range(9)]
    consts = [const0, const1, const2]

    functions = [sols_cut, heuristic, get_stddev, lambda x: len(np.nonzero(x)[0]) - 1, lambda x: x[1]/x[0], min_vars_to_satisfy, get_stddev_with_min_sat, get_stddev_with_length]
    

    for const in consts:
        print(const)
        for function in functions:
            print(f'{function.__name__}: {function(const)}')


    # print(sols_cut(const))


    # # a + b >= 1
    # # 5a + 4b + c + e >= 5


    # # 3a >= 3
    # # 2a + b >= 3
    # # 2a + b + c >= 3
    # # b + c >= 1

    # const = generate_constraint(30)
    # # const = np.array([73,  9,  9,  9,  9,  9,  8,  8,  7,  7,  7,  6,  6,  6,  5,  5,  5,  5, 4,  3,  3,  3,  3,  3,  3,  3,  3,  2,  2,  2,  2])
    # print(f'Constraint: {const}')
    # print(const_len(const))
    # print(f'Generalised slack: {generalised_slack(const)}')

    # nb_cut_sols = sols_cut(const)
    # print(f'nb_cut_sols: {nb_cut_sols}')
    # print(2**30)
    # print(1073741824 - 1073733269)
    # shuffled = np.arange(1000)
    # np.random.shuffle(shuffled)

    # print(np.corrcoef(np.arange(1000), shuffled))

   