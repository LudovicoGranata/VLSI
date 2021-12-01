from plot import *
import time

# For SAT solving:
import z3
from itertools import combinations

def save_solution(instance_index, grid_width, max_heigth, n_circuits, circuit_dimensions, circuit_positions):
    with open(f'./out_sat/ins-{instance_index}.txt', 'w') as f_result:
        f_result.write(f'{grid_width} {max_heigth}\n')
        f_result.write(f'{n_circuits}\n')
        for i in range(n_circuits):
            f_result.write(f'{circuit_dimensions[i][0]} {circuit_dimensions[i][1]} {circuit_positions[i][0]} {circuit_positions[i][0]}\n')

def range_intersection(range_A, range_B):
    return set(range_A).intersection(set(range_B))

def no_one(bool_vars):
    return z3.Not(z3.Or(bool_vars))

def at_least_one(bool_vars):
    return z3.Or(bool_vars)

def at_most_one(bool_vars):
    return [z3.Not(z3.And(pair[0], pair[1])) for pair in combinations(bool_vars, 2)]

def exactly_one(solver, bool_vars):
    solver.add(at_most_one(bool_vars))
    solver.add(at_least_one(bool_vars))

def solve_SAT_instance(instance_index):
    start = time.time()
    with open(f'./instances_SAT/ins-{instance_index}.txt', mode='r', encoding='UTF8') as f_inst:
        grid_width = int(f_inst.readline().replace('\n', ''))  # Parse first line
        n_circuits = int(f_inst.readline().replace('\n', ''))  # Parse second line
        
        circuit_dimensions = [] # Parse all the remaining lines
        for line in f_inst:
            coordinates = line.replace("\n", "").split()
            circuit_dimensions.append([int(coordinates[0]),int(coordinates[1])])
    
    blocks_range = range(n_circuits)

    block_widths = [circuit_dimensions[i][0] for i in blocks_range]
    block_heights = [circuit_dimensions[i][1] for i in blocks_range]

    width_range = range(grid_width - min(block_widths) + 1)
    #height_range = range(sum(block_heights) - min(block_heights) + 1)
    height_range = range(12)
        
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
                for n in width_range:  # x_pos of block [i]
                    for m in height_range:  # y_pos of block [i]
                        pos_i_formula = z3.And(x[i][n], y[i][m])
                        for p in width_range:  # x_pos of block [j]
                            for q in height_range:  # y_pos of block [j]
                                pos_j_formula = z3.And(x[j][p], y[j][q])
                                if (n <= p <= n + block_widths[i] and m <= q <= m + block_heights[i]):
                                    s.add(z3.Implies(pos_i_formula, z3.Not(pos_j_formula)))
                                if (p <= n <= p + block_widths[j] and q <= m <= q + block_heights[j]):
                                    s.add(z3.Implies(pos_j_formula, z3.Not(pos_i_formula)))


    # Constraint #3: blocks must be entirely contained inside the grid (only horizontally contrained!)
    for i in blocks_range:
        max_x_pos = grid_width - circuit_dimensions[i][0]
        forbidden_width_range = range(max_x_pos + 1, width_range[-1] + 1)
        for n in forbidden_width_range:
            s.add(z3.Not(x[i][n]))
    
    biggest_block = -1
    max_area = -1
    for i in blocks_range:
        block_area = block_widths[i] * block_heights[i]
        if block_area > max_area:
            max_area = block_area
            biggest_block = i
    
    s.add(z3.And(x[biggest_block][0], y[biggest_block][0]))

                for n in width_range:
                    for m in height_range:
                        for p in range_intersection(width_range, range(n, n + circuit_dimensions[i][0] + 1)):
                            for q in range_intersection(height_range, range(m, m + circuit_dimensions[i][1] + 1)):
                                s.add(z3.And(x[i][n], y[i][m]) == z3.And(z3.Not(x[j][p]), z3.Not(y[j][q])))
    
    s.set(timeout=300)
    status = s.check()
    if status == z3.sat:
        model = s.model()  # Finds a model that satisfies the SAT formula
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
                raise Exception('Formula was SATisfiable but at least a block was not positioned in the grid. Please check again the constraints!')
            else:
                solution.append([pos_x, pos_y])
        
        end = time.time()
        print(f'Elapsed time: {end - start} seconds.')
        save_solution(instance_index, grid_width, -1, n_circuits, circuit_dimensions, solution)

        plot('./out_sat', f'ins-{instance_index}.txt', './out_sat/images')
        return solution
    elif status == z3.unsat:
        raise Exception('unSATisfiable formula.')
    elif status == z3.unknown:
        raise Exception('The Z3 solver faced the following problem: ' + s.reason_unknown())