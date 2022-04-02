% Here we consider the bottom-left and top-right borders
% Why are they ordered ???
% Symmetry on bottom left
% => Test the two piece symmetry

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
int: max_height = sum ([circuit_dimensions_ord[c,2] | c in CIRCUITS]);
int: max_solution_var = max(width,max_height);
int: min_height = (sum([circuit_dimensions_ord[c,1] * circuit_dimensions_ord[c,2] | c in CIRCUITS]) div width);
%==============Solution=========================
array[CIRCUITS,1..2] of var 0..max_solution_var : solution_bl;
array[CIRCUITS,1..2] of var 0..max_solution_var: solution_ur;
constraint forall(c in CIRCUITS)( ( (solution_ur[c,1] - solution_bl[c,1])= circuit_dimensions_ord[c,1]) /\ ((solution_ur[c,2] - solution_bl[c,2])= circuit_dimensions_ord[c,2]) );
%array[CIRCUITS,1..2] of var 0..max_solution_var: solution_br;
%constraint col(solution_br,1)=col(solution_ur,1);
%constraint col(solution_br,2)=col(solution_bl,2);
%array[CIRCUITS,1..2] of var 0..max_solution_var: solution_ul;
%constraint col(solution_ul,1)=col(solution_bl,1);
%constraint col(solution_ul,2)=col(solution_ur,2);
%================================================

%===========Objective to minimize=================
var min_height..max_height: height = max(c in CIRCUITS)(solution_ur[c,2]);
%=================================================

%============Main Constraints=====================

constraint diffn ( col(solution_bl,1), col(solution_bl,2), col(circuit_dimensions_ord,1), col(circuit_dimensions_ord,2))::domain; 
constraint forall (c in CIRCUITS) (solution_bl[c,1]+ circuit_dimensions_ord[c,1] <= width)::domain;
constraint forall (c in CIRCUITS)(solution_bl[c,2] + circuit_dimensions_ord[c,2] <= height)::domain;

%=================================================


%===========Implied Constraints====================

constraint cumulative(col(solution_bl,2), col(circuit_dimensions_ord,2), col(circuit_dimensions_ord,1), width);
constraint cumulative(col(solution_bl,1), col(circuit_dimensions_ord,1), col(circuit_dimensions_ord,2),  height);

%==================================================

%=============Symmetry breaking constraints========

%===horizontal symmetry, vertical symmetry and horizontal and vertical symmetry.
array[CIRCUITS,1..2] of var int: solution_bl_sym_x;
%array[CIRCUITS,1..2] of var int: solution_bl_sym_y;
%array[CIRCUITS,1..2] of var int: solution_bl_sym_xy;

constraint forall(c in CIRCUITS)(solution_bl_sym_x[c,1]=width-solution_ur[c,1] /\ solution_bl_sym_x[c,2]=solution_bl[c,2]);
%constraint forall(c in CIRCUITS)(solution_bl_sym_y[c,2]=height-solution_ul[c,2] /\ solution_bl_sym_y[c,1]=solution_bl[c,1]);
%constraint forall(c in CIRCUITS)(solution_bl_sym_xy[c,1]=width-solution_br[c,1] /\ solution_bl_sym_xy[c,2]=height-solution_bl[c,2]);

constraint symmetry_breaking_constraint ( lex_less ( array1d(solution_bl), array1d(solution_bl_sym_x)));

%constraint symmetry_breaking_constraint ( lex_less ( array1d(solution_bl), array1d(solution_bl_sym_y)));

%constraint symmetry_breaking_constraint ( lex_less ( array1d(solution_bl), array1d(solution_bl_sym_x)) /\ lex_less ( array1d(solution_bl), array1d(solution_bl_sym_y)) /\ lex_less ( array1d(solution_bl), array1d(solution_bl_sym_xy)));

%relative position of the two biggest pieces to break symmetries
%constraint (lex_lesseq(row(solution_bl,1), row(solution_bl,2)));
%constraint symmetry_breaking_constraint((solution_bl[1,1]<=solution_bl[2,1] /\ solution_bl[1,2]<=solution_bl[2,2]));


%====two pieces symmetry
constraint symmetry_breaking_constraint(forall (c,k in CIRCUITS where c!=k)( (solution_bl[c,1]==solution_bl[k,1] /\ solution_ur[c,1]==solution_ur[k,1] /\ solution_ur[c,2]==solution_bl[k,2]) -> c<k));

%constraint symmetry_breaking_constraint(forall (c,k in CIRCUITS where c!=k)( (solution_bl[c,2]==solution_bl[k,2] /\ solution_ul[c,2]==solution_ul[k,2] /\ solution_ur[c,1]==solution_bl[k,1]) -> c<k));



%==================================================

%==================Heuristics======================
%   We want to put the rectangles only in corners

%what's a corner? A corner is formed by two rectangles (c,k,with c!=k) and it's the point of one of the squares of the rectangles and one of the edge of the other rectangle.




%=================================================



%============Search annotation=====================

%ann:search_ann;
%search_ann = int_search(array1d(solution_bl), dom_w_deg, indomain_random);

ann:search_ann_x;
ann:search_ann_y;
search_ann_x = int_search( col(solution_bl,1), input_order, indomain_random);
search_ann_y = int_search( col(solution_bl,2), dom_w_deg, indomain_random);
%==================================================


%============Solve================================

solve ::seq_search([ search_ann_x, search_ann_y])
      :: restart_luby(150)
      ::relax_and_reconstruct(array1d(solution_bl), 40) 
  minimize height;

%==================================================


%================Output============================
output [ show(width) ++ " " ++ show(height) ++ " \n" ++ show(n_circuits)]
++[ "\n" ++ show(circuit_dimensions_ord[c,1])++ " " ++ show(circuit_dimensions_ord[c,2])++ " " ++ show(solution_bl[c,1]) ++ " "++ show(solution_bl[c,2])|
c in CIRCUITS ];

%==================================================

%problem with: 19,22,25,26,30,32,34,35,36,37,38,39,40