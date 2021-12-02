from plot import *
import time
from math import *

# For SAT solving:
import z3
from itertools import combinations

def save_solution(instance_index, grid_width, max_heigth, n_circuits, circuit_dimensions, circuit_positions):
    with open(f'./out_sat/ins-{instance_index}.txt', 'w') as f_result:
        f_result.write(f'{grid_width} {max_heigth}\n')
        f_result.write(f'{n_circuits}\n')
        for i in range(n_circuits):
            f_result.write(f'{circuit_dimensions[i][0]} {circuit_dimensions[i][1]} {circuit_positions[i][0]} {circuit_positions[i][1]}\n')

def toSMT2Benchmark(solver, status="unknown", name="benchmark", logic=""):
    v = (z3.Ast * 0)()
    if isinstance(solver, z3.Solver):
        a = solver.assertions()
        if len(a) == 0:
            solver = z3.BoolVal(True)
        else:
            solver = z3.And(*a)
        return z3.Z3_benchmark_to_smtlib_string(solver.ctx_ref(), name, logic, status, "", 0, v, solver.as_ast())

def range_intersection(range_A, range_B):
    return set(range_A).intersection(set(range_B))

def no_one(bool_vars):
    return z3.Not(z3.Or(bool_vars))

def at_least_one(bool_vars):
    return z3.Or(bool_vars)

def at_most_one(bool_vars):
    return [z3.Not(z3.And(pair[0], pair[1])) for pair in combinations(bool_vars, 2)]

def exactly_one(bool_vars):
    # 'at_most_one' returns a list to which we concatenate the 'at_least_one' clause!
    return at_most_one(bool_vars) + [at_least_one(bool_vars)]

def solve_SAT_instance(instance_index):
    start = time.time()
    block_widths = []
    block_heights = []
    with open(f'./instances_SAT/ins-{instance_index}.txt', mode='r', encoding='UTF8') as f_inst:
        grid_width = int(f_inst.readline().replace('\n', ''))  # Parse first line
        n_circuits = int(f_inst.readline().replace('\n', ''))  # Parse second line
        
        for i in range(n_circuits):
            coordinates = f_inst.readline().replace("\n", "").split()
            block_widths.append(int(coordinates[0]))
            block_heights.append(int(coordinates[1]))
    
    grid_height = sum(block_heights)
    blocks_range = range(n_circuits)

    width_range = range(grid_width - min(block_widths) + 1)
    #height_range = range(grid_height - min(block_heights) + 1)
    areas = [block_widths[i] * block_heights[i] for i in blocks_range]
    height_range = range(sum(areas) // grid_width - min(block_heights) + 1)

    max_x = width_range[-1]
    max_y = height_range[-1]
        
    # Here we build the solver and we feed it with the constraints
    s = z3.Solver()
    
    # Here we prepare all the variables we need
    v = [[[z3.Bool(f'v{i}_[{n}, {m}]') for m in height_range] for n in width_range] for i in blocks_range]
    
    # First of all, we remove all variables that we already know will always be False:
    # we do this by redefining the n,m ranges foreach block.
    range_for_block = []
    for i in blocks_range:
        # Compute minimal range over n for block [i]
        max_x_for_block_i = grid_width - block_widths[i]
        forbidden_width_range = range(max_x_for_block_i + 1)

        # Compute minimal range over m for block [i]
        max_y_for_block_i = max_y + min(block_heights) - block_heights[i]
        forbidden_height_range = range(max_y_for_block_i + 1)

        range_for_block.append([forbidden_width_range, forbidden_height_range])
    
    constraints = []
    # Constraint #1: each block must have exactly one X coordinate and exactly one Y coordinate
    for i in blocks_range:
        position_for_block_i = [v[i][n][m] for n in range_for_block[i][0] for m in range_for_block[i][1]]
        constraints.extend(exactly_one(position_for_block_i))

    
    # Constraint #2: each pair of blocks cannot overlap
    for i in blocks_range:
        for n in range_for_block[i][0]:
            for m in range_for_block[i][1]:
                # This line is reached for every possible position for the block [i]
                for j in blocks_range:
                    if i < j:
                        forbidden_width_range = range(max(n - block_widths[j] + 1, 0), min(n + block_widths[i] - 1, max_x) + 1)
                        forbidden_height_range = range(max(m - block_heights[j] + 1, 0), min(m + block_heights[i] - 1, max_y) + 1)

                        #constraints.append(z3.Implies(v[i][n][m], z3.And([z3.Not(v[j][p][q]) for p in forbidden_width_range for q in forbidden_height_range])))
                        constraints.extend([z3.Implies(v[i][n][m], z3.Not(v[j][p][q])) for p in forbidden_width_range for q in forbidden_height_range])
                        #constraints.append(z3.Implies(at_least_one([v[j][p][q] for p in forbidden_width_range for q in forbidden_height_range]), z3.And(z3.Not(v[i][n][m]))))
        
    # Constraint #3: the biggest block must be in position (0, 0)
    biggest_block = -1
    max_area = -1
    for i in blocks_range:
        block_area = block_widths[i] * block_heights[i]
        if block_area > max_area:
            max_area = block_area
            biggest_block = i
    
    s.add(v[biggest_block][0][0])

    s.add(constraints)

    # Save the model in SMT2 format
    # with open('constraints.txt', mode='w', encoding='UTF-8') as file:
    #     file.writelines([str(constraints[i]) + '\n' for i in range(len(constraints))])
    #with open('./instances_SAT/smt2_models/ins-1.smt2', mode='w', encoding='UTF-8') as f_model:
    #    f_model.write(toSMT2Benchmark(s))

    num_threads = 8
    s.set("sat.threads", num_threads - 1)
    s.set("sat.local_search", True)
    s.set("sat.local_search_threads", 1)
    
    s.set("sat.lookahead_simplify", True)
    s.set("sat.lookahead.use_learned", True)
    
    s.set(timeout=int(5*60 - (time.time() - start))*1000)  # 5 minutes
    status = s.check()
    end = time.time()
    if status == z3.sat:
        model = s.model()  # Finds a model that satisfies the SAT formula
        solution = []
        for i in blocks_range:
            pos_i = [-1, -1]
            possible_pos_i = [[n, m] for n in range_for_block[i][0] for m in range_for_block[i][1]]
            for [n, m] in possible_pos_i:
                if model.evaluate(v[i][n][m]):
                    pos_i[0] = n
                    pos_i[1] = m
                    break
            
            if pos_i[0] < 0 or pos_i[1] < 0:
                raise Exception('Formula was SATisfiable but at least a block was not positioned in the grid. Please check again the constraints!')
            else:
                solution.append(pos_i)
        
        reached_height = max([solution[i][1] + block_heights[i] for i in blocks_range])

        print(f'Elapsed time: {round(end - start, 3)} seconds.')
        save_solution(instance_index, grid_width, reached_height, n_circuits, [[block_widths[i], block_heights[i]] for i in blocks_range], solution)

        plot('./out_sat', f'ins-{instance_index}.txt', './out_sat/images')
        return solution
    elif status == z3.unsat:
        raise Exception('unSATisfiable formula.')
    elif status == z3.unknown:
        raise Exception('The Z3 solver faced the following problem: ' + s.reason_unknown())