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
array[CIRCUITS] of int: d_1 = col(circuit_dimensions, 1); % Horizonal dimensions pre-ordering
array[CIRCUITS] of int: d_2 = col(circuit_dimensions, 2); % Vertical dimensions pre-ordering

% ================= Ordered circuit ==================
array[CIRCUITS] of int: circuits_ordered = sort_by(CIRCUITS, % Circuits ordered by dimension
	[ -(d_1[i]*d_2[i]) | i in CIRCUITS] );
array[CIRCUITS] of int: hor_dim = [d_1[circuits_ordered[i]] | i in CIRCUITS];
array[CIRCUITS] of int: ver_dim = [d_2[circuits_ordered[i]] | i in CIRCUITS];


% ====================================================
% ================ DECISION VARIABLES ================
% ====================================================

int: max_height = sum( [ max([ver_dim[i], hor_dim[i]]) | i in CIRCUITS] );
int: min_height = sum([ hor_dim[i] * ver_dim[i] | i in CIRCUITS]) div width;
set of int: HEIGHT_DOM = min_height..max_height;

var HEIGHT_DOM: height;

set of int: X_POS_DOM = 0..width - min( [ min([hor_dim[i], ver_dim[i]]) | i in CIRCUITS ]);
set of int: Y_POS_DOM = 0..max_height - min( [ min([hor_dim[i], ver_dim[i]]) | i in CIRCUITS ]);
array[CIRCUITS] of var X_POS_DOM: X_pos;
array[CIRCUITS] of var Y_POS_DOM: Y_pos;

% ================= Rotation variables ===============
int: max_dim = max(hor_dim ++ ver_dim);
int: min_dim = min(hor_dim ++ ver_dim);

set of int: DIM_1_DOM = min_dim..min([max_dim, width]);
set of int: DIM_2_DOM = min_dim..max_dim;

array[CIRCUITS] of var DIM_1_DOM: dim_1; % horizontal dimension
array[CIRCUITS] of var DIM_2_DOM: dim_2; % vertical dimension
array[CIRCUITS] of var bool: rotated;

constraint forall(i in CIRCUITS) ( 
	( rotated[i] -> (dim_1[i] == ver_dim[i] /\ dim_2[i] == hor_dim[i]) )
/\	( (not rotated[i]) -> (dim_1[i] == hor_dim[i] /\ dim_2[i] == ver_dim[i]) )
);

% ====================================================
% ================ MODEL CONSTRAINTS =================
% ====================================================

height = max([Y_pos[i]+dim_2[i] | i in CIRCUITS]);

constraint diffn(X_pos, Y_pos, dim_1, dim_2)::domain;
constraint forall(i in CIRCUITS) (
	( (X_pos[i] + dim_1[i]) <= width )
/\	( (Y_pos[i] + dim_2[i]) <= height)
);

% ================ Implied constraints ===============
constraint cumulative(X_pos, dim_1, dim_2, height)::domain;
constraint cumulative(Y_pos, dim_2, dim_1, width)::domain;


% ====================================================
% ========== SYMMETRY BREAKING CONSTRAINTS ===========
% ====================================================

% ============= Largest circuit on (0,0) ============= => slower than xy S.B.
% constraint X_pos[1] == 0 /\ Y_pos[1] == 0;

% ============== S.B. on x and y axis ================
array[CIRCUITS] of var X_POS_DOM: X_pos_sym;
array[CIRCUITS] of var Y_POS_DOM: Y_pos_sym;

constraint forall (i in CIRCUITS) (
	(Y_pos_sym[i] == height - Y_pos[i] - dim_2[i])
/\	(X_pos_sym[i] == width - X_pos[i] - dim_1[i])
);

constraint symmetry_breaking_constraint (
	lex_lesseq(X_pos, X_pos_sym)
);
constraint symmetry_breaking_constraint (
	lex_lesseq(Y_pos, Y_pos_sym)
);

% ========== S.B. on 2-3 stacking circuits ===========
predicate two_stack_ver(int: i, int: j) = (
	X_pos[i] == X_pos[j] /\ dim_1[i] == dim_1[j] /\ dim_2[i] + dim_2[j] == max([Y_pos[i]+dim_2[i],Y_pos[j]+dim_2[j]]) - min([Y_pos[i],Y_pos[j]])
);

predicate two_stack_hor(int: i, int: j) = (
	Y_pos[i] == Y_pos[j] /\ dim_2[i] == dim_2[j] /\ dim_1[i] + dim_1[j] == max([X_pos[i]+dim_1[i],X_pos[j]+dim_1[j]]) - min([X_pos[i],X_pos[j]])
);

% => set true to acivate stacking symmetry (for final model remove the if)
% => un-comment those 3 line to acivate 3 stacking symmetry (for final model remove the if)
constraint if false then (
	symmetry_breaking_constraint (
		forall ( i,j in CIRCUITS where i<j /\ two_stack_ver(i,j) ) (
			Y_pos[i] < Y_pos[j]
		/\	forall( k in CIRCUITS where i!=k /\ j!=k /\ dim_2[k] == dim_2[i] + dim_2[j] /\ dim_1[k] + dim_1[i] == max([X_pos[k]+dim_1[k],X_pos[i]+dim_1[i]]) - min([X_pos[k],X_pos[i]]) ) (
					X_pos[k] < X_pos[i] /\ X_pos[k] < X_pos[j]
			)
		)
	)
/\
	symmetry_breaking_constraint (
		forall ( i,j in CIRCUITS where i<j /\ two_stack_hor(i,j)) (
			Y_pos[i] < Y_pos[j]
		/\	forall( k in CIRCUITS where i!=k /\ j!=k /\ dim_1[k] == dim_1[i] + dim_1[j] /\ dim_2[k] + dim_2[i] == max([Y_pos[k]+dim_2[k],Y_pos[i]+dim_2[i]]) - min([Y_pos[k],Y_pos[i]])) (
				Y_pos[k] < Y_pos[i] /\ Y_pos[k] < Y_pos[j]
			)
		)
	)
) endif;


% ====================================================
% ===================== SEARCH =======================
% ====================================================

solve
	:: int_search(Y_pos, dom_w_deg, indomain_random)
	:: int_search(X_pos, dom_w_deg, indomain_random)
	:: bool_search(rotated, dom_w_deg, indomain_random)
	:: restart_luby(100)
	:: relax_and_reconstruct(X_pos, 40)
	minimize height;

output [ 
	show(width) ++ " " ++ show(height) ++ "\n" ++ 
	show(n_circuits) ] ++[ "\n" ++ 
	show(hor_dim[c])++ " " ++ show(ver_dim[c])++ " " ++ 
	show(X_pos[c]) ++ " "++ show(Y_pos[c]) ++
	if fix(rotated[c]) then " R" else "" endif | c in CIRCUITS ] ++ [ "\n"
]