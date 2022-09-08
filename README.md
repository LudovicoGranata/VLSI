# VLSI

This repository contains a project realized as part of the _Combinatorial Decision Making and Optimization course_ exam of the [Master's degree in Artificial Intelligence, University of Bologna](https://corsi.unibo.it/2cycle/artificial-intelligence).

_VLSI_ (Very Large Scale Integration) refers to the trend of integrating
circuits into silicon chips. A typical example is the smartphone. The modern
trend of shrinking transistor sizes, allowing engineers to fit more and
more transistors into the same area of silicon, has pushed the integration
of more and more functions of cellphone circuitry into a single silicon die
(i.e. plate). This enabled the modern cellphone to mature into a powerful
tool that shrank from the size of a large brick-sized unit to a device small
enough to comfortably carry in a pocket or purse, with a video camera,
touchscreen, and other advanced features.

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
python ./SAT/src/main.py
```

```bash
python ./SAT/src/main_rotation.py
```

## Plot results as images

```bash
python ./plot.py
```

## Group members

|  Reg No.  |  Name     |  Surname  |     Email                              |    Username      |
| :-------: | :-------: | :-------: | :------------------------------------: | :--------------: |
|  1005278  | Ludovico  | Granata   | `ludovico.granata@studio.unibo.it`     | [_LudovicoGranata_](https://github.com/LudovicoGranata) |
|  973719  | Parsa     | Dahesh    | `parsa.dahesh@studio.unibo.it`         | [_ParsaD23_](https://github.com/ParsaD23) |
|  984854  | Simone    | Persiani  | `simone.persiani2@studio.unibo.it`     | [_iosonopersia_](https://github.com/iosonopersia) |
