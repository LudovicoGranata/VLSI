import numpy as np
import time

# For SAT solving:
import z3
from itertools import combinations, product

class SAT_Circuit():
    def __init__(self, x = 0, y = 0):
        self.x = x
        self.y = y


class SAT_Model():

    def __init__(self, instance_idx = 1):
        self.instance_idx = instance_idx
        self.grid_width = 0
        self.n_circuits = 0
        self.block_widths = []
        self.block_heights = []
        self.optimal_packing_height = 0
        self.reached_height = 0
        self.solution = []

    def save_solution(self):
        with open(f'./SAT/out/base/out-{self.instance_idx}.txt', 'w') as f_result:
            f_result.write(f'{self.grid_width} {self.reached_height}\n')
            f_result.write(f'{self.n_circuits}\n')
            for i in range(self.n_circuits):
                circuit_i = self.solution[i]
                f_result.write(f'{self.block_widths[i]} {self.block_heights[i]} {circuit_i.x} {circuit_i.y}\n')

    @staticmethod
    def range_intersection(range_a, range_b):
        if range_a.step == range_b.step:
            return range(max(range_a.start, range_b.start), min(range_a.stop, range_b.stop), range_a.step)
        else:
            return set(range_a).intersection(range_b)

    def get_range_for_block(self, i, dimension='width'):
        if dimension == 'width':
            max_x_for_block_i = self.grid_width - self.block_widths[i]
            return range(max_x_for_block_i + 1)
        elif dimension == 'height':
            max_y_for_block_i = self.optimal_packing_height - self.block_heights[i]
            return range(max_y_for_block_i + 1)
        else:
            raise ValueError("Provided dimension MUST be either 'width' or 'height'.")

    @staticmethod
    def at_least_one(bool_vars):
        return z3.Or(bool_vars)

    @staticmethod
    def at_most_one(bool_vars):
        return [z3.Not(z3.And(pair[0], pair[1])) for pair in combinations(bool_vars, 2)]

    @staticmethod
    def exactly_one(bool_vars):
        # 'at_most_one' returns a list to which we concatenate the 'at_least_one' clause!
        return SAT_Model.at_most_one(bool_vars) + [SAT_Model.at_least_one(bool_vars)]

    def read_instance(self):
        self.block_widths = []
        self.block_heights = []
        with open(f'./SAT/ins/ins-{self.instance_idx}.txt', mode='r', encoding='UTF8') as f_inst:
            self.grid_width = int(f_inst.readline().replace('\n', ''))  # Parse first line
            self.n_circuits = int(f_inst.readline().replace('\n', ''))  # Parse second line
            
            for i in range(self.n_circuits):
                coordinates = f_inst.readline().replace("\n", "").split()
                self.block_widths.append(int(coordinates[0]))
                self.block_heights.append(int(coordinates[1]))

    def solve_SAT_instance(self):
        start = time.time()
        
        self.read_instance()  # This must be done immediately, since it initialises all the fields needed by the algorithm
        blocks_range = range(self.n_circuits)
            
        max_x = self.grid_width - min(self.block_widths)
        areas = [self.block_widths[i] * self.block_heights[i] for i in blocks_range]
        self.optimal_packing_height = sum(areas) // self.grid_width
        max_y = self.optimal_packing_height - min(self.block_heights)
        
        width_range = range(max_x + 1)
        height_range = range(max_y + 1)
            
        # Here we build the solver and we feed it with the constraints
        s = z3.Solver()
        
        # Here we prepare all the variables we may need:
        # in the process of minimizing the amount of variables
        # to be handled by the solver, what really matters are
        # only those variables that will be included in at least
        # one constraint!
        v = [[[z3.Bool(f'v{i}_[{n}, {m}]') for m in height_range] for n in width_range] for i in blocks_range]

        # Constraint #1: each block must have exactly one X coordinate and exactly one Y coordinate
        for i in blocks_range:
            allowed_positions_for_i = [v[i][n][m] for n in self.get_range_for_block(i, 'width') for m in self.get_range_for_block(i, 'height')]
            s.add(SAT_Model.exactly_one(allowed_positions_for_i))

        # Constraint #2: each pair of blocks cannot overlap
        for i, j in combinations(blocks_range, 2):
            width_range_for_j = self.get_range_for_block(j, 'width')
            height_range_for_j = self.get_range_for_block(j, 'height')

            for n, m in product(self.get_range_for_block(i, 'width'), self.get_range_for_block(i, 'height')):
                forbidden_width_range = range(n - self.block_widths[j] + 1, (n + self.block_widths[i] - 1) + 1)
                forbidden_height_range = range(m - self.block_heights[j] + 1, (m + self.block_heights[i] - 1) + 1)

                forbidden_P_values = SAT_Model.range_intersection(forbidden_width_range, width_range_for_j)
                forbidden_Q_values = SAT_Model.range_intersection(forbidden_height_range, height_range_for_j)

                s.add([z3.Implies(v[i][n][m], z3.Not(v[j][p][q])) for p in forbidden_P_values for q in forbidden_Q_values])

        # Symmetry-breaking constraints:
        for i, j in combinations(blocks_range, 2):
            width_range_for_j = self.get_range_for_block(j, 'width')
            height_range_for_j = self.get_range_for_block(j, 'height')

            for n, m in product(self.get_range_for_block(i, 'width'), self.get_range_for_block(i, 'height')):
                if self.block_widths[i] == self.block_widths[j]:  # The two blocks could be stacked vertically
                    if areas[i] >= areas[j]:
                        if (m - self.block_heights[j]) in height_range_for_j:
                            s.add(z3.Implies(v[i][n][m], z3.Not(v[j][n][m - self.block_heights[j]])))
                    else:
                        if (m + self.block_heights[i]) in height_range_for_j:
                            s.add(z3.Implies(v[i][n][m], z3.Not(v[j][n][m + self.block_heights[i]])))
                
                if self.block_heights[i] == self.block_heights[j]:  # The two blocks could be stacked horizontally
                    if areas[i] >= areas[j]:
                        if (n - self.block_widths[j]) in width_range_for_j:
                            s.add(z3.Implies(v[i][n][m], z3.Not(v[j][n - self.block_widths[j]][m])))
                    else:
                        if (n + self.block_widths[i]) in width_range_for_j:
                            s.add(z3.Implies(v[i][n][m], z3.Not(v[j][n + self.block_widths[i]][m])))

        # Constraint #3: the biggest block must be in position (0, 0)
        largest_block_index = np.argmax(areas)
        s.add(v[largest_block_index][0][0])

        constraints_production_time = time.time() - start
        print(f'Constraints production time: {round(constraints_production_time, 3)} seconds.')
        if constraints_production_time > 300.0:
            raise Exception('Timeout reached during constraint production.')

        num_threads = 8
        s.set("sat.threads", num_threads - 1)
        s.set("sat.local_search", True)
        s.set("sat.local_search_threads", 1)
        
        s.set("sat.lookahead_simplify", True)
        s.set("sat.lookahead.use_learned", True)
        
        s.set(timeout=int(5*60 - constraints_production_time)*1000)  # 5 minutes
        status = s.check()
        end = time.time()
        if status == z3.sat:
            model = s.model()  # Finds a model that satisfies the SAT formula
            self.solution = []
            for i in blocks_range:
                x, y = -1, -1
                possible_pos_i = [[n, m] for n in self.get_range_for_block(i, 'width') for m in self.get_range_for_block(i, 'height')]
                for [n, m] in possible_pos_i:
                    if model.evaluate(v[i][n][m]):
                        x, y = n, m
                        break
                
                if x == -1 or y == -1:
                    raise Exception('Formula was SATisfiable but at least a block was not positioned in the grid. Please check again the constraints!')
                else:
                    self.solution.append(SAT_Circuit(x, y))
            
            self.reached_height = max([self.solution[i].y + self.block_heights[i] for i in blocks_range])

            elapsed_time = end - start
            print(f'Total elapsed time: {round(elapsed_time, 3)} seconds.')
            self.save_solution()

            return elapsed_time
        elif status == z3.unsat:
            raise Exception('unSATisfiable formula.')
        elif status == z3.unknown:
            raise Exception('The Z3 solver faced the following problem: ' + s.reason_unknown())
