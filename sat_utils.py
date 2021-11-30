# For SAT solving:
import z3
from itertools import combinations

def range_intersection(range_A, range_B):
    return set(range_A).intersection(set(range_B))

def at_least_one(bool_vars):
    return z3.Or(bool_vars)

def at_most_one(bool_vars):
    return [z3.Not(z3.And(pair[0], pair[1])) for pair in combinations(bool_vars, 2)]

def exactly_one(solver, bool_vars):
    solver.add(at_most_one(bool_vars))
    solver.add(at_least_one(bool_vars))

def create_solver_from_instance(instance):
    with open(instance, mode='r', encoding='UTF8') as f_inst:
        grid_width = int(f_inst.readline().replace('\n', ''))  # Parse first line
        n_circuits = int(f_inst.readline().replace('\n', ''))  # Parse second line
        
        circuit_dimensions = [] # Parse all the remaining lines
        for line in f_inst:
            coordinates = line.replace("\n", "").split()
            circuit_dimensions.append([int(coordinates[0]),int(coordinates[1])])
    
    blocks_range = range(n_circuits)
    width_range = range(grid_width - min([circuit_dimensions[i][0] for i in blocks_range]))
    height_range = range(sum([circuit_dimensions[i][1] for i in blocks_range]))
        
    # Here we build the solver and we feed it with the constraints
    s = z3.Solver()
    
    # Here we prepare all the variables we need
    x = [[z3.Bool(f'x{i}_{n}') for n in width_range] for i in blocks_range]
    y = [[z3.Bool(f'y{i}_{m}') for m in height_range] for i in blocks_range]
    
    # Constraint #1: each block must have exactly one X coordinate and exactly one Y coordinate
    for i in blocks_range:
        exactly_one(s, [x[i][n] for n in width_range])
        exactly_one(s, [y[i][m] for m in height_range])
    
    # Constraint #2: each pair of blocks cannot overlap
    for i in blocks_range:
        for j in blocks_range:
            if i < j:
                for n in width_range:
                    for m in height_range:
                        for p in range_intersection(width_range, range(n, n + circuit_dimensions[i][0] + 1)):
                            for q in range_intersection(height_range, range(m, m + circuit_dimensions[i][1] + 1)):
                                s.add(z3.And(x[i][n], y[i][m]) == z3.And(z3.Not(x[j][p]), z3.Not(y[j][q])))
    
    if s.check() == z3.sat:
        model = s.model()  # Finds a model that satisfies the SAT formula
        print(model)
        solution = []
        for i in blocks_range:
            pos_x = -1
            pos_y = -1
            for n in width_range:
                if model.evaluate(x[i][n]):
                    pos_x = n
                    break
            for m in height_range:
                if model.evaluate(y[i][m]):
                    pos_y = m
                    break
            
            if pos_x < 0 or pos_y < 0:
                raise Exception('UNSAT')
            else:
                solution.append([pos_x, pos_y])
        return solution
    else:
        raise Exception('UNSAT')    