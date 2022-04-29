from sat_model_rotations import *
import matplotlib.pyplot as plt

if __name__ == '__main__':
    times = []
    for i in range(1, 20 + 1):
        print(f">>> Trying to solve instance #{i}...")
        sat_model = SAT_Model(i)
        try:
            time = sat_model.solve_SAT_instance()
        except Exception as e:
            print(e)
            time = 0
        times.append(time)
        print()

    plt.figure()
    plt.bar(range(1, 20 + 1), times)
    plt.show()
