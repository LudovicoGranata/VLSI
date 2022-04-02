include "globals.mzn";

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

int: max_height = round((sum(i in CIRCUITS)( max([hor_dim[i], ver_dim[i]]) ) )/2);
int: min_height = min(i in CIRCUITS)(max([hor_dim[i], ver_dim[i]]));
set of int: HEIGHT_DOM = min_height..max_height;
var HEIGHT_DOM: height;

set of int: CIRCUITX_DOM = 0..width-min(i in CIRCUITS)(min([hor_dim[i], ver_dim[i]]));
set of int: CIRCUITY_DOM = 0..max_height-min(i in CIRCUITS)(min([hor_dim[i], ver_dim[i]]));
array[CIRCUITS] of var CIRCUITX_DOM: circuitx;
array[CIRCUITS] of var CIRCUITY_DOM: circuity;

int: max_dim = max(hor_dim ++ ver_dim);
int: min_dim = min(hor_dim ++ ver_dim);

set of int: HOR_DIM_R_DOM = min_dim..min([max_dim, width]);
set of int: VER_DIM_R_DOM = min_dim..max_dim;

array[CIRCUITS] of var HOR_DIM_R_DOM: hor_dim_r;
array[CIRCUITS] of var VER_DIM_R_DOM: ver_dim_r;
array[CIRCUITS] of var bool: rotated;


% ====================================================
% ================ MODEL CONSTRAINTS =================
% ====================================================

constraint diffn(circuitx, circuity, hor_dim_r, ver_dim_r)::domain;
constraint forall(i in CIRCUITS) (
	( (circuitx[i] + hor_dim_r[i]) <= width )
/\	( (circuity[i] + ver_dim_r[i]) <= height)
);

constraint exists(i in CIRCUITS) ( circuitx[i] == 0 /\ circuity[i] == 0 );

constraint cumulative(circuitx, hor_dim_r, ver_dim_r, height)::domain;
constraint cumulative(circuity, ver_dim_r, hor_dim_r, width)::domain;

constraint forall(i in CIRCUITS) ( 
	(rotated[i] -> (hor_dim_r[i] == ver_dim[i] /\ ver_dim_r[i] == hor_dim[i])) /\ (not (rotated[i]) -> (ver_dim_r[i] == ver_dim[i] /\ hor_dim_r[i] == hor_dim[i]))
);


% ====================================================
% ==================== DUAL MODEL ====================
% ====================================================

% => this model is slow !!!

set of int: MATRIX_WIDTH = 0..width-1;
set of int: MATRIX_HEIGHT = 0..max_height-1;
array[MATRIX_HEIGHT, MATRIX_WIDTH] of var 0..n_circuits: matrix;

% ============= Channeling Constraints ===============
constraint forall(i in MATRIX_WIDTH, k in CIRCUITS, j in MATRIX_HEIGHT)
	((circuitx[k]<=i /\ circuitx[k]+hor_dim_r[k]>i /\ circuity[k]<=j /\ circuity[k]+ver_dim_r[k]>j) <-> (matrix[j,i] == k));


% ====================================================
% ========== SYMMETRY BREAKING CONSTRAINTS ===========
% ====================================================

array[CIRCUITS] of var CIRCUITX_DOM: circuitx_sym;
array[CIRCUITS] of var CIRCUITY_DOM: circuity_sym;

constraint forall (i in CIRCUITS) (
	(circuity_sym[i] == height - circuity[i] - ver_dim_r[i])
/\	(circuitx_sym[i] == width - circuitx[i] - hor_dim_r[i])
);

array[MATRIX_HEIGHT, MATRIX_WIDTH] of var 0..n_circuits: matrix_X_symmetry;
array[MATRIX_HEIGHT, MATRIX_WIDTH] of var 0..n_circuits: matrix_Y_symmetry;
array[MATRIX_HEIGHT, MATRIX_WIDTH] of var 0..n_circuits: matrix_XY_symmetry;

constraint forall(i in MATRIX_WIDTH, k in CIRCUITS, j in MATRIX_HEIGHT)
	((circuitx_sym[k]<=i /\ circuitx_sym[k]+hor_dim_r[k]>i /\ circuity[k]<=j /\ circuity[k]+ver_dim_r[k]>j) <-> (matrix_X_symmetry[j,i] == k));
	
constraint forall(i in MATRIX_WIDTH, k in CIRCUITS, j in MATRIX_HEIGHT)
	((circuitx[k]<=i /\ circuitx[k]+hor_dim_r[k]>i /\ circuity_sym[k]<=j /\ circuity_sym[k]+ver_dim_r[k]>j) <-> (matrix_Y_symmetry[j,i] == k));
	
constraint forall(i in MATRIX_WIDTH, k in CIRCUITS, j in MATRIX_HEIGHT)
	((circuitx_sym[k]<=i /\ circuitx_sym[k]+hor_dim_r[k]>i /\ circuity_sym[k]<=j /\ circuity_sym[k]+ver_dim_r[k]>j) <-> (matrix_XY_symmetry[j,i] == k));

constraint lex_greatereq(array1d(matrix), array1d(matrix_X_symmetry));
constraint lex_greatereq(array1d(matrix), array1d(matrix_Y_symmetry));
constraint lex_greatereq(array1d(matrix), array1d(matrix_XY_symmetry));

constraint lex_greatereq(circuitx, circuitx_sym);
% constraint lex_greatereq(circuity, circuity_sym); removes solutions?


% ====================================================
% ===================== SEARCH =======================
% ====================================================

solve :: seq_search([
		int_search(circuity, dom_w_deg, indomain_min),
		bool_search(rotated, dom_w_deg, indomain_random),
		int_search(circuitx, dom_w_deg, indomain_random) ])
	minimize height;

output ["height=\(height)\n",
		"circuitx=\(circuitx)\n",
		"circuity=\(circuity)\n",
		"hor_dim=\(hor_dim_r)\n",
		"ver_dim=\(ver_dim_r)\n"]