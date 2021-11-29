include "globals.mzn";
include "gecode.mzn";
int: n_circuits;   % Number of circuits
set of int: CIRCUITS = 1..n_circuits;

int: width;   % fixed width of the grid
set of int: WIDTH = 0..width;
array[CIRCUITS, 1..2] of int: circuit_dimensions; %width and height of the circuits -- change the name to circuit_dimensions
array[CIRCUITS] of int: CIRCUITS_ORDERED = sort_by(CIRCUITS, [-circuit_dimensions[c,1]*circuit_dimensions[c,2] | c in CIRCUITS]);
array[CIRCUITS] of int: circuit_dimensions_ordered_x = [circuit_dimensions[CIRCUITS_ORDERED[c],1] | c in CIRCUITS];
array[CIRCUITS] of int: circuit_dimensions_ordered_y =[circuit_dimensions[CIRCUITS_ORDERED[c],2] | c in CIRCUITS];
int: max_height = sum ([circuit_dimensions_ordered_y[c] | c in CIRCUITS]);
int: min_height = (sum([circuit_dimensions_ordered_x[c] * circuit_dimensions_ordered_y[c] | c in CIRCUITS]) div width)+1;
int: max_solution = max(max_height, width);
array[CIRCUITS,1..2] of var 0..max_solution: solution;
%var int: height = max(c in CIRCUITS)(solution[c,2] + circuit_dimensions_ordered_y[c]);
var min_height..max_height: height = max(c in CIRCUITS)(solution[c,2] + circuit_dimensions_ordered_y[c]);


constraint diffn ([solution[c,1]|c in CIRCUITS],[solution[c,2]|c in CIRCUITS],[circuit_dimensions_ordered_x[c]|c in CIRCUITS],[circuit_dimensions_ordered_y[c]|c in CIRCUITS]);
constraint forall (c in CIRCUITS) (solution[c,1]+ circuit_dimensions_ordered_x[c] <= width)::domain;
constraint forall (c in CIRCUITS)(solution[c,2] + circuit_dimensions_ordered_y[c] <= height)::domain;
%constraint forall (c in CIRCUITS) (solution[c,1]< width);
%constraint forall (c in CIRCUITS)(solution[c,2] < height);

constraint cumulative([solution[c,2]| c in CIRCUITS], [circuit_dimensions_ordered_y[n]| n in CIRCUITS], [circuit_dimensions_ordered_x[n] | n in CIRCUITS] , width);
constraint cumulative([solution[c,1]| c in CIRCUITS], [circuit_dimensions_ordered_x[n]| n in CIRCUITS], [circuit_dimensions_ordered_y[n] | n in CIRCUITS] ,  height);


%symmetry constrain breaking



constraint symmetry_breaking_constraint ( lex_lesseq ( [solution[c,1]| c in CIRCUITS], [width-solution[c,1]-circuit_dimensions_ordered_x[c]| c in CIRCUITS] ) );
constraint symmetry_breaking_constraint ( lex_lesseq ( [solution[c,2]| c in CIRCUITS], [height-solution[c,2]-circuit_dimensions_ordered_y[c]| c in CIRCUITS] ) );

%the biggest block has to be in the bottom left corner
constraint symmetry_breaking_constraint(  solution[1,1] == 0 /\ solution[1,2] == 0);

%the second biggest block has to be to the right of the biggest block
%constraint symmetry_breaking_constraint ((lex_lesseq([solution[1,1],solution[1,2]],[solution[2,1],solution[2,2]] )));

%every block has to start "touching" another block.
%constraint forall (c in CIRCUITS where c!=1) (exists(o in CIRCUITS where o!=c)(solution[c,1]>= solution[o,1] /\ solution[c,1] <=solution[o,1] + circuit_dimensions_ordered_x[o] /\ solution[c,2]>= solution[o,2] /\ solution[c,2] <=solution[o,2] + circuit_dimensions_ordered_y[o]))::domain;

ann:search_ann;
%search_ann = int_search(solution, input_order, indomain_min);
%search_ann = int_search(solution, first_fail, indomain_min);
%search_ann = int_search(solution, dom_w_deg, indomain_min);
%search_ann = int_search(solution, input_order, indomain_random);
search_ann = int_search(solution, dom_w_deg, indomain_random);


solve ::search_ann
      :: restart_luby(150)
      ::relax_and_reconstruct(array1d(solution), 40)
  minimize height;


output [ show(width) ++ " " ++ show(height) ++ " \n" ++ show(n_circuits)]
++[ "\n" ++ show(circuit_dimensions_ordered_x[c])++ " " ++ show(circuit_dimensions_ordered_y[c])++ " " ++ show(solution[c,1]) ++ " "++ show(solution[c,2])|
c in CIRCUITS ]



%problem with 30,32,35,37,38,39,40





