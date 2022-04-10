
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
%================================================

%====Upper and Lower Bound=======================
int: max_height = sum (col (circuit_dimensions_ord, 2));
int: min_height = (sum([circuit_dimensions_ord[c,1] * circuit_dimensions_ord[c,2] | c in CIRCUITS]) div width);
%==============Solution=========================
array[CIRCUITS] of var 0..width-min(col(circuit_dimensions_ord,1)): solution_bl_x; %bottom left x
array[CIRCUITS] of var 0..max_height-min(col(circuit_dimensions_ord,2)): solution_bl_y; %bottom left y

array[CIRCUITS] of var min(col(circuit_dimensions_ord,1))..width: solution_ur_x; %upper right x
array[CIRCUITS] of var min(col(circuit_dimensions_ord,2))..max_height: solution_ur_y; %upper right y

constraint forall (c in CIRCUITS) (solution_ur_x[c]-solution_bl_x[c] = circuit_dimensions_ord[c,1] /\
                                   solution_ur_y[c]-solution_bl_y[c] = circuit_dimensions_ord[c,2]
);
%================================================

%===========Objective to minimize=================
var min_height..max_height: height = max(solution_ur_y);
%=================================================

%============Main Constraints=====================

constraint diffn ( solution_bl_x, solution_bl_y, col(circuit_dimensions_ord,1), col(circuit_dimensions_ord,2))::domain; 
constraint forall (c in CIRCUITS) (solution_bl_x[c]+ circuit_dimensions_ord[c,1] <= width)::domain;
constraint forall (c in CIRCUITS)(solution_bl_y[c] + circuit_dimensions_ord[c,2] <= height)::domain;

constraint forall (c in CIRCUITS) (solution_ur_x[c] >= circuit_dimensions_ord[c,1] )::domain;
constraint forall (c in CIRCUITS)(solution_ur_y[c]  >= circuit_dimensions_ord[c,2])::domain;

%=================================================


%===========Implied Constraints====================

constraint cumulative(solution_bl_y, col(circuit_dimensions_ord,2), col(circuit_dimensions_ord,1), width);
constraint cumulative(solution_bl_x, col(circuit_dimensions_ord,1), col(circuit_dimensions_ord,2),  height);

%==================================================

%=============Symmetry breaking constraints========

%horizzontal and vertical symmetry
% array[CIRCUITS] of var 0..width-min(col(circuit_dimensions_ord,1)): solution_bl_x_sym;
% array[CIRCUITS] of var 0..max_height-min(col(circuit_dimensions_ord,2)): solution_bl_y_sym;

% constraint forall (c in CIRCUITS) (
% 	(solution_bl_y_sym[c] == height - solution_bl_y[c] - circuit_dimensions_ord[c,2])
% /\	(solution_bl_x_sym[c] == width - solution_bl_x[c] - circuit_dimensions_ord[c,1])
% );

% constraint symmetry_breaking_constraint (
% 	lex_lesseq(solution_bl_x, solution_bl_x_sym)
% );
% constraint symmetry_breaking_constraint (
% 	lex_lesseq(solution_bl_y, solution_bl_y_sym)
% );


%====two pieces symmetry


% constraint symmetry_breaking_constraint(forall (c,k in CIRCUITS where c<k /\ circuit_dimensions_ord[c,2] == circuit_dimensions_ord[k,2])( solution_bl_y[c] == solution_bl_y[k] /\ circuit_dimensions_ord[c,1] + circuit_dimensions_ord[k,1] == max([solution_ur_x[c], solution_ur_x[k]]) - min([solution_bl_x[c], solution_bl_x[k]])  -> solution_bl_x[c] < solution_bl_x[k]  ));


constraint symmetry_breaking_constraint(forall (c,k in CIRCUITS where c<k /\ circuit_dimensions_ord[c,1] == circuit_dimensions_ord[k,1])( solution_bl_x[c] == solution_bl_x[k] /\ circuit_dimensions_ord[c,2] + circuit_dimensions_ord[k,2] == max([solution_ur_y[c], solution_ur_y[k]]) - min([solution_bl_y[c], solution_bl_y[k]]) -> solution_bl_y[c] < solution_bl_y[k]  ));

% constraint symmetry_breaking_constraint(forall (c,k in CIRCUITS where c!=k)( (solution_bl_y[c]==solution_bl_y[k] /\ solution_ur_y[c]==solution_ur_y[k] /\ solution_ur_x[c]==solution_bl_x[k]) -> c<k));

% constraint symmetry_breaking_constraint(forall (c,k in CIRCUITS where c!=k)( (solution_bl_x[c]==solution_bl_x[k] /\ solution_ur_x[c]==solution_ur_x[k] /\ solution_ur_y[c]==solution_bl_y[k]) -> c<k));

%the largest block is positioned on the bottom left
constraint solution_bl_x[1] = 0;
constraint solution_bl_y[1] = 0;

%==================================================


%============Search annotation=====================

%ann:search_ann;
%search_ann = int_search(array1d(solution_bl), dom_w_deg, indomain_random);

ann:search_ann_x;
ann:search_ann_y;
search_ann_x = int_search( solution_bl_x, input_order, indomain_random);
search_ann_y = int_search( solution_bl_y, dom_w_deg, indomain_random);
%==================================================


%============Solve================================

solve ::seq_search([ search_ann_x, search_ann_y])
      :: restart_luby(200)
      ::relax_and_reconstruct(solution_bl_x, 40) 
  minimize height;

%==================================================


%================Output============================
output [ show(width) ++ " " ++ show(height) ++ " \n" ++ show(n_circuits)]
++[ "\n" ++ show(circuit_dimensions_ord[c,1])++ " " ++ show(circuit_dimensions_ord[c,2])++ " " ++ show(solution_bl_x[c]) ++ " "++ show(solution_bl_y[c])|
c in CIRCUITS ];

%==================================================