include "globals.mzn";
include "gecode.mzn";
int: n_circuits;   % Number of circuits
set of int: CIRCUITS = 1..n_circuits;  

int: width;   % fixed width of the grid
set of int: WIDTH = 0..width; 
array[CIRCUITS, 1..2] of int: circuit_dimensions; %width and height of the circuits
array[CIRCUITS] of int: circuit_dimension_x = [circuit_dimensions[c,1]|c in CIRCUITS];%array of the width of every circuit
array[CIRCUITS] of int: circuit_dimension_y = [circuit_dimensions[c,2]|c in CIRCUITS];%array of the height of every circuit
int: max_height = sum ([circuit_dimensions[c, 2] | c in CIRCUITS]);%max possible height as the sum of all height
int: max_solution = width * max_height; 
array[CIRCUITS] of var 0..max_solution : solution; 
var int: height = max(c in CIRCUITS)(solution[c] div width + circuit_dimensions[c,2]); %the height - the objective to minimize


%second model 
array [WIDTH, 0..max_height] of var 0..n_circuits : solution_grid;

constraint forall (i in 0..width, j in 0..max_height, c in CIRCUITS)(solution_grid[i,j] == c <-> solution[c] = j* width+ i);

constraint symmetry_breaking_constraint ( lex_lesseq ( array1d(solution_grid), [solution_grid[i,j] | i in 0..width, j in reverse (0..max_height)] ));

constraint symmetry_breaking_constraint ( lex_lesseq ( array1d(solution_grid), [solution_grid[i,j] | i in reverse (0..width), j in 0..max_height] ));


%constraint to have the rectangles not to overlap
constraint diffn ([solution[c] mod width| c in CIRCUITS],[solution[c] div width| c in CIRCUITS],circuit_dimension_x, circuit_dimension_y)::domain; 
%constraints to have the rectangles inside the grid
constraint forall (c in CIRCUITS) (solution[c] mod width + circuit_dimension_x[c] <= width)::domain;
constraint forall (c in CIRCUITS)(solution[c] div width + circuit_dimension_y[c] <= height)::domain;


%cumulative constraints
constraint cumulative([solution[c] div width| c in CIRCUITS], circuit_dimension_y, circuit_dimension_x, width)::domain;
constraint cumulative([solution[c] mod width| c in CIRCUITS], circuit_dimension_x, circuit_dimension_y, height)::domain;

%symmetry breaking constraint

%constraint symmetry_breaking_constraint ( lex_lesseq ( solution, [solution[c] - 2*(solution[c] mod width)+ width -1 - circuit_dimension_x[c]| c in CIRCUITS] ) );
%constraint symmetry_breaking_constraint ( lex_lesseq ( solution_y, [height-solution_y[c]-circuit_dimension_y[c]| c in CIRCUITS] ) );







ann:search_ann;
%search_ann = int_search(solution, input_order, indomain_min);
%search_ann = int_search(solution, first_fail, indomain_min);
%search_ann = int_search(solution, dom_w_deg, indomain_min); 
%search_ann = int_search(solution, input_order, indomain_random);
%search_ann_x = int_search(solution_x, dom_w_deg, indomain_random); 
%search_ann_y = int_search(solution_y, dom_w_deg, indomain_random);
search_ann = int_search(solution, dom_w_deg, indomain_min);

ann : search_ann_plate;
search_ann_plate = int_search(array1d(solution_grid), dom_w_deg, indomain_random);

solve ::search_ann
      :: search_ann_plate
      :: restart_luby(150)
      :: relax_and_reconstruct(solution, 50) 
  minimize height;


output [ show(width) ++ " " ++ show(height) ++ " \n" ++ show(n_circuits)]
++[ "\n" ++ show(circuit_dimensions[c,1])++ " " ++ show(circuit_dimensions[c,2])++ " " ++ show(solution[c] mod width) ++ " "++ show(solution[c] div width)|
c in CIRCUITS ]
