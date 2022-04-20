from sat_model import *

if __name__ == '__main__':
    for i in range(1, 40 + 1):
        print(f">>> Trying to solve instance #{i}...")
        sat_model = SAT_Model(i+5)
        sat_model.solve_SAT_instance()
