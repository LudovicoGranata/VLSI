
include "globals.mzn";
include "gecode.mzn";

%==============Data==============================
int: n_circuits;   
set of int: CIRCUITS = 1..n_circuits;  
int: width; 
array[CIRCUITS, 1..2] of int: circuit_dimensions;
%================================================
%=============Ordering===========================
array[CIRCUITS] of int: CIRCUITS_ORDERED = sort_by(CIRCUITS, [-circuit_dimensions[c,1]*circuit_dimensions[c,2] | c in CIRCUITS]);
array[CIRCUITS, 1..2] of int: circuit_dimensions_ord = array2d(CIRCUITS,1..2,[circuit_dimensions[c, dim]|c in CIRCUITS_ORDERED, dim in 1..2]);
array[CIRCUITS] of int : hor_dim = [circuit_dimensions_ord[c,1] | c in CIRCUITS];
array[CIRCUITS] of int : ver_dim = [circuit_dimensions_ord[c,2] | c in CIRCUITS];

%================================================

%=============Rotation===========================
array[CIRCUITS] of var bool : rotated; % true if the circuit is rotated


%====Upper and Lower Bound for the height=======================
int: max_height = sum ([ max(circuit_dimensions_ord[c,1], circuit_dimensions_ord[c,2])| c in CIRCUITS]);
int: min_height = (sum([hor_dim[c] * ver_dim[c] | c in CIRCUITS]) div width);

%==============Solution=========================
array[CIRCUITS] of var 0..width-min(hor_dim): x_pos; %bottom left x
array[CIRCUITS] of var 0..max_height-min(ver_dim): y_pos; %bottom left y

%=================================================

%===========Objective to minimize=================
var min_height..max_height: height = max([ if not rotated[c] then (y_pos[c] + ver_dim[c]) else (y_pos[c] + hor_dim[c]) endif| c in CIRCUITS]);
%=================================================

%============Main Constraints=====================
array[CIRCUITS] of var int :new_hor_dim = [if not rotated[c] then hor_dim[c] else ver_dim[c] endif | c in CIRCUITS];
array[CIRCUITS] of var int :new_ver_dim = [if not rotated[c] then ver_dim[c] else hor_dim[c] endif| c in CIRCUITS];

constraint diffn ( x_pos, y_pos, new_hor_dim, new_ver_dim)::domain; 
constraint forall (c in CIRCUITS) (x_pos[c] + new_hor_dim[c] <= width)::domain;
constraint forall (c in CIRCUITS)(y_pos[c] + new_ver_dim[c] <= height)::domain;

%=================================================


%===========Implied Constraints====================

constraint cumulative(y_pos, new_ver_dim, new_hor_dim, width);
constraint cumulative(x_pos, new_hor_dim, new_ver_dim,  height);

%==================================================

%=============Symmetry breaking constraints========




%the largest block is positioned on the bottom left
constraint x_pos[1] = 0;
constraint y_pos[1] = 0;

%====two pieces symmetry
constraint symmetry_breaking_constraint(forall (c,k in CIRCUITS where c<k /\ new_hor_dim[c] == new_hor_dim[k])( x_pos[c] == x_pos[k] /\ new_ver_dim[c] + new_ver_dim[k] == max([y_pos[c] + new_ver_dim[c], y_pos[k] + new_ver_dim[k]]) - min([y_pos[c], y_pos[k]]) -> y_pos[c] < y_pos[k]));


%==================================================


%============Search annotation=====================

%ann:search_ann;
%search_ann = int_search(array1d(solution_bl), dom_w_deg, indomain_random);

ann:search_ann_x;
ann:search_ann_y;
search_ann_x = int_search( x_pos, input_order, indomain_random);
search_ann_y = int_search( y_pos, input_order, indomain_random);
%==================================================


%============Solve================================

solve :: search_ann_x
      :: search_ann_y
      :: restart_luby(100)
      ::relax_and_reconstruct(x_pos, 40) 
  minimize height;

%==================================================


%================Output============================
output [ show(width) ++ " " ++ show(height) ++ " \n" ++ show(n_circuits)]
++[ "\n" ++ show(new_hor_dim[c])++ " " ++ show(new_ver_dim[c])++ " " ++ show(x_pos[c]) ++ " "++ show(y_pos[c])|
c in CIRCUITS ];

%==================================================