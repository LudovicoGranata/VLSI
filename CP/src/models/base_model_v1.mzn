include "globals.mzn";
include "gecode.mzn";

% ====================================================
% ================ PROBLEM PARAMETERS ================
% ====================================================

int: width;
int: n_circuits;

set of int: CIRCUITS = 1..n_circuits;
array[CIRCUITS, 1..2] of int: circuit_dimensions;

% ============= Conversion to my model ===============
array[CIRCUITS] of int: dim_1 = col(circuit_dimensions, 1); % Horizonal dimensions pre-ordering
array[CIRCUITS] of int: dim_2 = col(circuit_dimensions, 2); % Vertical dimensions pre-ordering

% ================= Ordered circuit ==================
array[CIRCUITS] of int: circuits_ordered = sort_by(CIRCUITS, % Circuits ordered by dimension
	[ -(dim_1[i]*dim_2[i]) | i in CIRCUITS] );
array[CIRCUITS] of int: hor_dim = [dim_1[circuits_ordered[i]] | i in CIRCUITS];
array[CIRCUITS] of int: ver_dim = [dim_2[circuits_ordered[i]] | i in CIRCUITS];


% ====================================================
% ================ DECISION VARIABLES ================
% ====================================================

int: max_height = sum (ver_dim);
int: min_height = sum([ hor_dim[i] * ver_dim[i] | i in CIRCUITS]) div width;
set of int: HEIGHT_DOM = min_height..max_height;

var HEIGHT_DOM: height;

set of int: CIRCUITX_DOM = 0..width - min(hor_dim);
set of int: CIRCUITY_DOM = 0..max_height - min(ver_dim);
array[CIRCUITS] of var CIRCUITX_DOM: X_pos;
array[CIRCUITS] of var CIRCUITY_DOM: Y_pos;


% ====================================================
% ================ MODEL CONSTRAINTS =================
% ====================================================

height = max([Y_pos[i]+ver_dim[i] | i in CIRCUITS]);

constraint diffn(X_pos, Y_pos, hor_dim, ver_dim)::domain;
constraint forall(i in CIRCUITS) (
	( (X_pos[i] + hor_dim[i]) <= width )
/\	( (Y_pos[i] + ver_dim[i]) <= height)
);

% ================ Implied constraints ===============
constraint cumulative(X_pos, hor_dim, ver_dim, height)::domain;
constraint cumulative(Y_pos, ver_dim, hor_dim, width)::domain;


% ====================================================
% ========== SYMMETRY BREAKING CONSTRAINTS ===========
% ====================================================

% ============= Largest circuit on (0,0) =============
% constraint X_pos[1] == 0 /\ Y_pos[1] == 0;

% ============== S.B. on x and y axis ================
array[CIRCUITS] of var CIRCUITX_DOM: X_pos_sym;
array[CIRCUITS] of var CIRCUITY_DOM: Y_pos_sym;

constraint forall (i in CIRCUITS) (
	(Y_pos_sym[i] == height - Y_pos[i] - ver_dim[i])
/\	(X_pos_sym[i] == width - X_pos[i] - hor_dim[i])
);

constraint symmetry_breaking_constraint (
	lex_lesseq(X_pos, X_pos_sym)
);
constraint symmetry_breaking_constraint (
	lex_lesseq(Y_pos, Y_pos_sym)
);

% ========== S.B. on 2-3 stacking circuits ===========
predicate two_stack_ver(int: i, int: j) = (
	X_pos[i] == X_pos[j] /\ hor_dim[i] == hor_dim[j] /\ ver_dim[i] + ver_dim[j] == max([Y_pos[i]+ver_dim[i],Y_pos[j]+ver_dim[j]]) - min([Y_pos[i],Y_pos[j]])
);

predicate two_stack_hor(int: i, int: j) = (
	Y_pos[i] == Y_pos[j] /\ ver_dim[i] == ver_dim[j] /\ hor_dim[i] + hor_dim[j] == max([X_pos[i]+hor_dim[i],X_pos[j]+hor_dim[j]]) - min([X_pos[i],X_pos[j]])
);

% % => un-comment those 3 line to acivate 3 stacking symmetry (for final model remove the if)
constraint symmetry_breaking_constraint (
		forall ( i,j in CIRCUITS where i<j /\ two_stack_ver(i,j)) (
			Y_pos[i] <= Y_pos[j]
		/\	forall( k in CIRCUITS where i!=k /\ j!=k /\ ver_dim[k] == ver_dim[i] + ver_dim[j] /\ hor_dim[k] + hor_dim[i] == max([X_pos[k]+hor_dim[k],X_pos[i]+hor_dim[i]]) - min([X_pos[k],X_pos[i]]) ) (
					X_pos[k] < X_pos[i] /\ X_pos[k] < X_pos[j]
			)
		)
	);
constraint symmetry_breaking_constraint (
		forall ( i,j in CIRCUITS where i<j /\ two_stack_hor(i,j)) (
			 Y_pos[i] <= Y_pos[j]
		/\	forall( k in CIRCUITS where i!=k /\ j!=k /\ hor_dim[k] == hor_dim[i] + hor_dim[j] /\ ver_dim[k] + ver_dim[i] == max([Y_pos[k]+ver_dim[k],Y_pos[i]+ver_dim[i]]) - min([Y_pos[k],Y_pos[i]])) (
				Y_pos[k] < Y_pos[i] /\ Y_pos[k] < Y_pos[j]
			)
		)
	);


% ====================================================
% ===================== SEARCH =======================
% ====================================================

solve
	:: int_search(Y_pos, dom_w_deg, indomain_random)
	:: int_search(X_pos, dom_w_deg, indomain_random)
	:: restart_luby(100)
	:: relax_and_reconstruct(X_pos, 40)
	minimize height;

output [ 
	show(width) ++ " " ++ show(height) ++ " \n" ++ 
	show(n_circuits) ] ++[ "\n" ++ 
	show(hor_dim[c])++ " " ++ show(ver_dim[c])++ " " ++ 
	show(X_pos[c]) ++ " "++ show(Y_pos[c])
	| c in CIRCUITS ]