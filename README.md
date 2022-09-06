# VLSI

This repository contains a project realized as part of the *Combinatorial Decision Making and Optimization course* exam of the [Master's degree in Artificial Intelligence, University of Bologna](https://corsi.unibo.it/2cycle/artificial-intelligence).

*VLSI* (Very Large Scale Integration) refers to the trend of integrating circuits into silicon chips.
The problem is to design the VLSI of the circuits defining your electrical device: given a
fixed-width plate and a list of rectangular circuits, decide how to place them
on the plate so that the length of the final device is minimized (improving its
portability).
Different solution in CP, SAT and SMT have been developed.

## Prerequisites

It is required to install [Minizinc](https://www.minizinc.org/) and add the executable to the environment variable PATH.

Moreover, Python 3 must be installed on the system and the following command must be issued from inside the project folder:

```bash
pip install -r ./requirements.txt
```

## CP

Use MiniZinc IDE!

## SAT

```bash
python ./SAT/src/main.py
```

```bash
python ./SAT/src/main_rotations.py
```

## SMT

```bash
python ./SAT/src/base_model.py
```

```bash
python ./SAT/src/rotation_model.py
```

## Plot results as images

```bash
python ./plot.py
```

## Group members

|  Reg No.  |  Name     |  Surname  |     Email                              |    Username      |
| :-------: | :-------: | :-------: | :------------------------------------: | :--------------: |
|  ???????  | Ludovico  | Granata   | `ludovico.granata@studio.unibo.it`     | [_LudovicoGranata_](https://github.com/LudovicoGranata) |
|  ???????  | Parsa     | Dahesh    | `parsa.dahesh@studio.unibo.it`         | [_ParsaD23_](https://github.com/ParsaD23) |
|  ???????  | Simone    | Persiani  | `simone.persiani2@studio.unibo.it`     | [_iosonopersia_](https://github.com/iosonopersia) |
