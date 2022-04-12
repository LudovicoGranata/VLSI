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
array[CIRCUITS] of int: hor_dim = [circuit_dimensions[i,1] | i in CIRCUITS];
array[CIRCUITS] of int: ver_dim = [circuit_dimensions[i,2] | i in CIRCUITS];


% ====================================================
% ================ DECISION VARIABLES ================
% ====================================================

int: max_height = sum( [ max([ver_dim[i], hor_dim[i]]) | i in CIRCUITS] );
int: min_height = sum([ hor_dim[i] * ver_dim[i] | i in CIRCUITS]) div width;
set of int: HEIGHT_DOM = min_height..max_height;

var HEIGHT_DOM: height;

set of int: CIRCUITX_DOM = 0..width - min( [ min([hor_dim[i], ver_dim[i]]) | i in CIRCUITS ]);
set of int: CIRCUITY_DOM = 0..max_height - min( [ min([hor_dim[i], ver_dim[i]]) | i in CIRCUITS ]);
array[CIRCUITS] of var CIRCUITX_DOM: circuitx;
array[CIRCUITS] of var CIRCUITY_DOM: circuity;

% ================= Rotation variables ===============
int: max_dim = max(hor_dim ++ ver_dim);
int: min_dim = min(hor_dim ++ ver_dim);

set of int: DIM_1_DOM = min_dim..min([max_dim, width]);
set of int: DIM_2_DOM = min_dim..max_dim;

array[CIRCUITS] of var DIM_1_DOM: dim_1; % horizontal dimension
array[CIRCUITS] of var DIM_2_DOM: dim_2; % vertical dimension
array[CIRCUITS] of var bool: rotated;

array[CIRCUITS] of int: circuits_ordered = sort_by(CIRCUITS,
	[- hor_dim[i]*ver_dim[i] | i in CIRCUITS] );
array[CIRCUITS] of int: hor_dim_ord = [hor_dim[circuits_ordered[i]] | i in CIRCUITS];
array[CIRCUITS] of int: ver_dim_ord = [ver_dim[circuits_ordered[i]] | i in CIRCUITS];

constraint forall(i in CIRCUITS) ( 
	( rotated[i] -> (dim_1[i] == ver_dim_ord[i] /\ dim_2[i] == hor_dim_ord[i]) )
/\	( (not rotated[i]) -> (dim_1[i] == hor_dim_ord[i] /\ dim_2[i] == ver_dim_ord[i]) )
);

% ====================================================
% ================ MODEL CONSTRAINTS =================
% ====================================================

height = max([circuity[i]+dim_2[i] | i in CIRCUITS]);

constraint diffn(circuitx, circuity, dim_1, dim_2)::domain;
constraint forall(i in CIRCUITS) (
	( (circuitx[i] + dim_1[i]) <= width )
/\	( (circuity[i] + dim_2[i]) <= height)
);

% ================ Implied constraints ===============
constraint cumulative(circuitx, dim_1, dim_2, height)::domain;
constraint cumulative(circuity, dim_2, dim_1, width)::domain;


% ====================================================
% ========== SYMMETRY BREAKING CONSTRAINTS ===========
% ====================================================

% ============= Largest circuit on (0,0) ============= => slower than xy S.B.
% constraint circuitx[1] == 0 /\ circuity[1] == 0;

% ============== S.B. on x and y axis ================
array[CIRCUITS] of var CIRCUITX_DOM: circuitx_sym;
array[CIRCUITS] of var CIRCUITY_DOM: circuity_sym;

constraint forall (i in CIRCUITS) (
	(circuity_sym[i] == height - circuity[i] - dim_2[i])
/\	(circuitx_sym[i] == width - circuitx[i] - dim_1[i])
);

constraint symmetry_breaking_constraint (
	lex_lesseq(circuitx, circuitx_sym)
);
constraint symmetry_breaking_constraint (
	lex_lesseq(circuity, circuity_sym)
);

% ========== S.B. on 2-3 stacking circuits ===========
predicate two_stack_ver(int: i, int: j) = (
	circuitx[i] == circuitx[j] /\ dim_1[i] == dim_1[j] /\ dim_2[i] + dim_2[j] == max([circuity[i]+dim_2[i],circuity[j]+dim_2[j]]) - min([circuity[i],circuity[j]])
);

predicate two_stack_hor(int: i, int: j) = (
	circuity[i] == circuity[j] /\ dim_2[i] == dim_2[j] /\ dim_1[i] + dim_1[j] == max([circuitx[i]+dim_1[i],circuitx[j]+dim_1[j]]) - min([circuitx[i],circuitx[j]])
);

% => set true to acivate stacking symmetry (for final model remove the if)
% => un-comment those 3 line to acivate 3 stacking symmetry (for final model remove the if)
constraint if false then (
	symmetry_breaking_constraint (
		forall ( i,j in CIRCUITS where i<j /\ two_stack_ver(i,j) ) (
			circuity[i] < circuity[j]
	% 	/\	forall( k in CIRCUITS where i!=k /\ j!=k /\ dim_2[k] == dim_2[i] + dim_2[j] /\ dim_1[k] + dim_1[i] == max([circuitx[k]+dim_1[k],circuitx[i]+dim_1[i]]) - min([circuitx[k],circuitx[i]]) ) (
	% 				circuitx[k] < circuitx[i] /\ circuitx[k] < circuitx[j]
	% 		)
		)
	)
/\
	symmetry_breaking_constraint (
		forall ( i,j in CIRCUITS where i<j /\ two_stack_hor(i,j)) (
			circuity[i] < circuity[j]
	% 	/\	forall( k in CIRCUITS where i!=k /\ j!=k /\ dim_1[k] == dim_1[i] + dim_1[j] /\ dim_2[k] + dim_2[i] == max([circuity[k]+dim_2[k],circuity[i]+dim_2[i]]) - min([circuity[k],circuity[i]])) (
	% 			circuity[k] < circuity[i] /\ circuity[k] < circuity[j]
	% 		)
		)
	)
) endif;


% ====================================================
% ===================== SEARCH =======================
% ====================================================

solve
	:: int_search(circuity, input_order, indomain_min)
	:: bool_search(rotated, dom_w_deg, indomain_random)
	:: int_search(circuitx, input_order, indomain_random)
	:: restart_luby(150)
	:: relax_and_reconstruct(circuitx, 40)
	minimize height;

output [ 
	show(width) ++ " " ++ show(height) ++ " \n" ++ 
	show(n_circuits) ] ++[ "\n" ++ 
	show(dim_1[c])++ " " ++ show(dim_2[c])++ " " ++ 
	show(circuitx[c]) ++ " "++ show(circuity[c])
	| c in CIRCUITS ] ++ [ "\n" ++
	show(rotated) ]