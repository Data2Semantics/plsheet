:- module(ods_formula,
	  [ sheet_ds_formulas/2,	% :Sheet, -DSFormulas
	    sheet_formula_groups/3,	% :Sheet, -Groups, -Singles
	    ds_formulas/2,		% +Formulas, -DSFormulas
	    group_formula/2,		% +Group, -Grounded
	    generalize_formula/8,	% +S0, +X0, +Y0, +F0, -S, -X, -Y, -F
	    sheet_dependency_graph/2,	% :Sheet, -AggregatedGraph
	    sheet_dependency_graph/3,	% :Sheet, unTransposedGraph,-TransposedGraph
	    orig_dependency_graph/2,    % :Sheet, -Graph
	    orig_no_copy_graph/2,       % :Sheet, -Graph,
	    cell_dependency_graph/5,	% :Sheet, +X, +Y, +Direction, -Graph
	    cell_dependency/3,          % :Sheet, ?Cell, -Inputs
	    group_dependency/4,         % :Sheet, +Groups,  ?Group, -Inputs
	    intermed_result/2           % +Graph, -Sink
	  ]).

:- use_module(library(record)).
:- use_module(library(clpfd), except([transpose/2])).
:- use_module(library(ugraphs)).
:- use_module(library(debug)).
:- use_module(library(apply)).
:- use_module(library(pairs)).
:- use_module(library(lists)).
:- use_module(library(ordsets)).
:- use_module(library(thread)).
:- use_module(library(trace/pprint)).
:- use_module(ods_table).
:- use_module(datasource).

:- record
	map(sheet,x,y).

:- meta_predicate
	sheet_ds_formulas(:, -),
	sheet_formula_groups(:, -,-),
	sheet_dependency_graph(:, -),
	sheet_dependency_graph(:, -, -),
	orig_dependency_graph(:, -),
	orig_no_copy_graph(:, -),
	cell_dependency_graph(:,+,+,+,-),
	cell_dependency(:,+,?),
	group_dependency(:,+,?,-),
	intermed_result(+,-).

/** <module> Reason about formulas


*/

%%	sheet_ds_formulas(:Sheet, -Formulas) is det.
%
%	Formulas is a list of generalised formulas in Sheet

sheet_ds_formulas(Sheet, DSFormulas) :-
	sheet_formula_groups(Sheet, Groups, Singles),
	append(Groups, Grouped),
	append(Singles, Grouped, AllFormulas),
	ds_formulas(AllFormulas, DSFormulas0),
	sort(DSFormulas0, DSFormulas).

%%	sheet_formula_groups(:Sheet, -Groups, -Singles) is det.
%
%	Group formulas that have the same   structure.  Each group is of
%	this form:
%
%	    forall(What, In, f(Sheet,X,Y,Formula))
%
%	The What/In pairs describe the spatial   relation  of the group.
%	Provided pairs are:
%
%	  - col, X in Xs
%	  Repeat a formula over multiple columns
%	  - row, Y in Ys
%	  Repeat a formula over multiple rows
%	  - sheet, S in Sheets
%	  Repeat a formula over multiple sheets
%	  - area, [ X in Xs, Y in Ys ]
%	  Repeat a formula over a rectangular area
%	  - workbook, [ S in Sheets, X in Xs, Y in Ys ]
%	  Repeat a formula over multiple sheets over an area
%
%	In the above, `Sheets` is a list   of sheet names and `Xs`, `Ys`
%	is a list of integers or pairs `Low-High`, e.g., [1, 5-10] means
%	the X/Y values `1,5,6,7,8,9,10`.
%
%	In general, the terms contain   clpfd  _constraints_ between the
%	X/Y variables and cells or cell-ranges appearing in the formula.
%	The  corresponding  formula  with  concrete  cell  addresses  is
%	obtained by binding  the  X  and   Y  values,  which  cause  the
%	constraints to be propagated to materialize the cell addresses.

sheet_formula_groups(QSheet, Groups, Singles) :-
	QSheet = _:Sheet,
	findall(f(Sheet,X,Y,Simple),
		(   cell_formula(Sheet, X, Y, F),
		    simplify_lookup(F,Simple)),
		Formulas),
%	findall(f(Sheet,X,Y,F),
%		cell_formula(Sheet, X, Y, F),
%		Formulas),
	length(Formulas, Count),
	debug(formula, '~q: Found ~D formulas', [Sheet, Count]),
	map_list_to_pairs(skolem_formula, Formulas, Keyed),
	keysort(Keyed, Sorted),
	group_pairs_by_key(Sorted, ByKey),
	pairs_values(ByKey, CandidateGroups),
	length(CandidateGroups, CCount),
	debug(formula, '~D candidate groups', [CCount]),
	concurrent_maplist(make_groups,
			   CandidateGroups, NestedGroups, NestedSingles),
	append(NestedGroups, Groups),
	append(NestedSingles, Singles).

make_groups([], [], []).
make_groups([F0|FT], Groups, Singles) :-
	generalize_formula(F0, P),
	partition(match_formula(P), FT, Matching, Rest),
	length(Matching, Matches),
	length(Rest, Left),
	debug(formula, '~p: ~D matches; ~D left', [P, Matches, Left]),
	(   Matching \== []
	->  make_group(P, [F0|Matching], G0),
	    Groups = [G0|GT],
	    RS = Singles
	;   Groups = GT,
	    Singles = [F0|RS]
	),
	make_groups(Rest, GT, RS).

match_formula(P, F) :-
	\+ \+ P = F.

%%	make_group(+Pattern, +Matches, -Group)
%
%	Turn a set of matches into a group.  Groups is a term
%	forall(Var in Values, Formula).
%
%	@param Pattern is a term f(S,X,Y,F), where S,X,Y are variables.
%	@param Matches is a list of ground terms f(S,X,Y,F).

make_group(P, Matches, Groups) :-
	P = f(S,X,Y,_),
	findall(b(S,X,Y), member(P,Matches), Bindings),
	maplist(arg(1), Bindings, AllSheets), sort(AllSheets, Sheets),
	maplist(arg(2), Bindings, AllXs),     sort(AllXs, Xs),
	maplist(arg(3), Bindings, AllYs),     sort(AllYs, Ys),
	(   group(Sheets, Xs, Ys, P, Matches, Groups0)
	->  true
	;   gtrace, group(Sheets, Xs, Ys, P, Matches, Groups0)
	),
	flatten(Groups0, Groups).

group([S], [X], [Y], P, _, Result) :- !,
	P = f(S,X,Y,F),
	assertion(ground(P)),
	Result = (cell(S,X,Y) = F).
group([S], [X],  Ys, f(S,X,Y,F), _, forall(row,   Y in Set, f(S,X,Y,F))) :- !,
	compress(Ys, Set).
group([S], Xs,  [Y], f(S,X,Y,F), _, forall(col,   X in Set, f(S,X,Y,F))) :- !,
	compress(Xs, Set).
group(Ss,  [X], [Y], f(S,X,Y,F), _, forall(sheet, S in Ss,  f(S,X,Y,F))) :- !.
group([S], Xs, Ys, f(S,X,Y,F), Matches,
      [forall(area, [X in SetX, Y in SetY], f(S,X,Y,F))]) :-
	forall(( member(X,Xs),
		 member(Y,Ys)
	       ),
	       memberchk(f(S,X,Y,_), Matches)), !,
	compress(Xs, SetX),
	compress(Ys, SetY).
group(Ss, Xs, Ys, f(S,X,Y,F), Matches,
      [forall(workbook, [S in Ss, X in SetX, Y in SetY], f(S,X,Y,F))]) :-
	Ss = [_,_|_],
	forall(( member(S, Ss),
		 member(X,Xs),
		 member(Y,Ys)
	       ),
	       memberchk(f(S,X,Y,_), Matches)), !,
	compress(Xs, SetX),
	compress(Ys, SetY).
group([S], Xs, Ys, P, Matches, Groups) :- !,
	P = f(S,X,Y,_),
	length(Xs, Xc),
	length(Ys, Yc),
	(   Xc < Yc
	->  findall(G, (member(X,Xs), make_group(P, Matches, G)), NGroups)
	;   findall(G, (member(Y,Ys), make_group(P, Matches, G)), NGroups)
	),
	append(NGroups, Groups).
group(Ss, _Xs, _Ys, P, Matches, Groups) :-
	P = f(S,_,_,_),
	findall(G, (member(S,Ss), make_group(P, Matches, G)), NGroups),
	append(NGroups, Groups).

%%	compress(+List, -Description)
%
%	Create a short description of the elements in list using ranges.
%	Ranges are expressed as Low-High.

compress(List, Description) :-
	sort(List, Sorted),
	create_ranges(Sorted, Description).

create_ranges([], []).
create_ranges([Low|T0], [Low-High|T]) :-
	range(Low, T0, High, T1),
	High > Low, !,
	create_ranges(T1, T).
create_ranges([H|T0], [H|T]) :-
	create_ranges(T0, T).

range(Low, [Next|T0], High, T) :-
	integer(Low), integer(Next),
	succ(Low, Next), !,
	range(Next, T0, High, T).
range(High, T, High, T) :-
	integer(High).


%%	ds_formulas(+Formulas:list, -DSFormulas:list) is det.

ds_formulas(FL0, FL) :-
	ds_formulas(FL0, FL1, []),
	maplist(simplify_formula, FL1, FL).

ds_formulas([], FL, FL).
ds_formulas([H|T], FL0, FL) :-
	(   ds_formula(H, FL0, FL1)
	->  true
	;   gtrace,
	    print_term(H, []),
	    ds_formula(H, FL0, FL1)
	),
	ds_formulas(T, FL1, FL).

%%	ds_formula(+Group, -DSFormula, ?Tail) is det.
%
%	Translate a formula using the  forall()   notation  above into a
%	formula between data-sources. Some examples:
%
%	    * D1-D20 = A1-A20 + B1-B20

ds_formula(f(S,X,Y,F), [cell(S,X,Y) = F|FL], FL) :- !.
ds_formula(forall(_, _ in [], _), FL, FL) :- !.
					% rows
ds_formula(forall(row, Y in [Ya-Yz|T], P),
	   [cell_range(S,X,Ya,X,Yz) = FDS|More], FL) :-
	P = f(S,X,Y,F),
	range_formula(y(Y,Ya,Yz), F, FDS), !,
	assertion(ground(FDS)),
	ds_formula(forall(row, Y in T, P), More, FL).
ds_formula(forall(row, Y in [Ya-Yz|T], P), FL0, FL) :- !,
	numlist(Ya, Yz, YL),
	append(YL, T, Ys),
	ds_formula(forall(row, Y in Ys, P), FL0, FL).
ds_formula(forall(row, Y in [Y0|Ys], P),
	   [cell(S,X,Y0) = FDS|More], FL) :- !,
	P = f(S,X,Y,F),
	range_formula(y(Y,Y0,Y0), F, FDS),
	assertion(ground(FDS)),
	ds_formula(forall(row, Y in Ys, P), More, FL).
					% columns
ds_formula(forall(col, X in [Xa-Xz|T], P),
	   [cell_range(S,Xa,Y,Xz,Y) = FDS|More], FL) :-
	P = f(S,X,Y,F),
	range_formula(x(X,Xa,Xz), F, FDS), !,
	assertion(ground(FDS)),
	ds_formula(forall(col, X in T, P), More, FL).
ds_formula(forall(col, X in [Xa-Xz|T], P), FL0, FL) :- !,
	numlist(Xa, Xz, XL),
	append(XL, T, Xs),
	ds_formula(forall(col, X in Xs, P), FL0, FL).
ds_formula(forall(col, X in [X0|Xs], P),
	   [cell(S,X0,Y) = FDS|More], FL) :- !,
	P = f(S,X,Y,F),
	range_formula(x(X,X0,X0), F, FDS),
	assertion(ground(FDS)),
	ds_formula(forall(col, X in Xs, P), More, FL).
					% areas
ds_formula(forall(area, [_ in [],_], _), FL, FL) :- !.
ds_formula(forall(area, [_,_ in []], _), FL, FL) :- !.
ds_formula(forall(area, [X in [Xa-Xz|TX], Y in [Ya-Yz|TY]], P),
	   [ cell_range(S,Xa,Ya,Xz,Yz) = FDS | More ], FL) :- !,
	P = f(S,X,Y,F),
	range_formula(xy(X,Xa,Xz,Y,Ya,Yz), F, FDS),
	assertion(ground(FDS)),
	ds_formula(forall(area, [X in TX, Y in [Ya-Yz|TY]], P),
		   More, FL0),
	ds_formula(forall(area, [X in [Xa-Xz|TX], Y in TY], P),
		   FL0, FL).
ds_formula(forall(area, [X in [X0|TX], Y in [Ya-Yz|TY]], P),
	   [ cell_range(S,X0,Ya,X0,Yz) = FDS | More ], FL) :- !,
	P = f(S,X,Y,F),
	range_formula(xy(X,X0,X0,Y,Ya,Yz), F, FDS),
	assertion(ground(FDS)),
	ds_formula(forall(area, [X in TX, Y in [Ya-Yz|TY]], P),
		   More, FL0),
	ds_formula(forall(area, [X in [X0|TX], Y in TY], P),
		   FL0, FL).
ds_formula(forall(area, [X in [Xa-Xz|TX], Y in [Y0|TY]], P),
	   [ cell_range(S,Xa,Y0,Xz,Y0) = FDS | More ], FL) :- !,
	P = f(S,X,Y,F),
	range_formula(xy(X,Xa,Xz,Y,Y0,Y0), F, FDS),
	assertion(ground(FDS)),
	ds_formula(forall(area, [X in TX, Y in [Y0|TY]], P),
		   More, FL0),
	ds_formula(forall(area, [X in [Xa-Xz|TX], Y in TY], P),
		   FL0, FL).
ds_formula(forall(area, [X in [X0|TX], Y in [Y0|TY]], P),
	   [ cell(S,X0,Y0) = FDS | More ], FL) :- !,
	P = f(S,X,Y,F),
	range_formula(xy(X,X0,X0,Y,Y0,Y0), F, FDS),
	assertion(ground(FDS)),
	ds_formula(forall(area, [X in TX, Y in [Y0|TY]], P),
		   More, FL0),
	ds_formula(forall(area, [X in [X0|TX], Y in TY], P),
		   FL0, FL).

ds_formula(Formula, [Formula|FL], FL).		% TBD


%%	range_formula(+Spec, +F, -FDS) is semidet.

range_formula(_Spec, F, FDS) :-
	ground(F), !,
	FDS = F.
						% y...
range_formula(y(Y,Ya,Ya), cell(S,X,YF), cell(S,X,Ys)) :-
	findall(YF, Y=Ya, [Ys]), !.
range_formula(y(Y,Ya,Ya), cell_range(S,Xs,YFs,Xe,YFe),
	                  cell_range(S,Xs,Ys,Xe,Ye)) :-
	findall(YFs-YFe, Y=Ya, [Ys-Ye]), !.
range_formula(y(Y,Ya,Yz), cell(S,X,YF), cell_range(S,X,Ys,X,Ye)) :-
	findall(YF, (Y=Ya; Y=Yz), [Ys,Ye]), !.
					% x...
range_formula(x(X,Xa,Xa), cell(S,XF,Y), cell(S,Xs,Y)) :-
	findall(XF, X=Xa, [Xs]), !.
range_formula(x(X,Xa,Xa), cell_range(S,XFs,Ys,XFe,Ye),
	                  cell_range(S,Xs,Ys,Xe,Ye)) :-
	findall(XFs-XFe, X=Xa, [Xs-Xe]), !.
range_formula(x(X,Xa,Xz), cell(S,XF,Y), cell_range(S,Xs,Y,Xe,Y)) :-
	findall(XF, (X=Xa; X=Xz), [Xs,Xe]), !.
					% xy...
range_formula(xy(X,Xa,Xa,Y,Ya,Ya),
	      cell_range(S,XFs,YFs,XFe,YFe),
	      cell_range(S,Xs,Ys,Xe,Ye)) :-
	findall(XFs-XFe, X=Xa, [Xs-Xe]),
	findall(YFs-YFe, Y=Ya, [Ys-Ye]), !.
range_formula(xy(X,Xa,Xz,Y,Ya,Ya),
	      cell_range(S,XF,YFs,XF,YFe),
	      cell_range(S,Xs,Ys,Xe,Ye)) :-
	findall(XF, (X=Xa; X=Xz), [Xs,Xe]),
	findall(YFs-YFe, Y=Ya, [Ys-Ye]), !.
range_formula(xy(X,Xa,Xz,Y,Ya,Yz),
	      cell(S,XF,YF),
	      cell_range(S,Xs,Ys,Xe,Ye)) :-
	findall(XF, (X=Xa; X=Xz), [Xs,Xe]),
	findall(YF, (Y=Ya; Y=Yz), [Ys,Ye]), !.
					% Cannot do these
range_formula(_, cell(_,_,_), _) :- !, fail.
range_formula(_, cell_range(_,_,_,_,_), _) :- !, fail.
					% General recursion
range_formula(Y, From, To) :-
	compound(From), !,
	From =.. [Name|Args0],
	maplist(range_formula(Y), Args0, Args),
	To =.. [Name|Args].
range_formula(_, Formula, Formula).



%%	generalize_formula(F0, F) is det.
%%	generalize_formula(+S0, +X0, +Y0, +F0, -S, -X, -Y, -F) is det.
%
%	F is F0, after replacing coordinates by the variables X and Y or
%	constraints thereof. The idea is  that   F  now unifies to other
%	formulas that have the same  structure   with  the same relative
%	cell positions.

generalize_formula(f(S0,X0,Y0,F0), f(S,X,Y,F)) :-
	generalize_formula(S0, X0, Y0, F0, S, X, Y, F).

generalize_formula(S0, X0, Y0, F0, S, X, Y, F) :-
	Map = map(S0-S, X0-X, Y0-Y),
	generalize_formula(Map, F0, F).

skolem_formula(f(S0,X0,Y0,F0), F) :-
	generalize_formula(S0, X0, Y0, F0, 'S', 'X', 'Y', F).



generalize_formula(Map, cell(S0,X0,Y0), cell(S,X,Y)) :- !,
	generalize_sheet(S0, Map, S),
	generalize_x(X0, Map, X),
	generalize_y(Y0, Map, Y).
generalize_formula(Map,
		   cell_range(S0,SX0,SY0,EX0,EY0),
		   cell_range(S, SX, SY, EX, EY)) :- !,
	generalize_sheet(S0, Map, S),
	generalize_x(SX0, Map, SX),
	generalize_y(SY0, Map, SY),
	generalize_x(EX0, Map, EX),
	generalize_y(EY0, Map, EY).
generalize_formula(Map, From, To) :-
	compound(From), !,
	From =.. [Name|Args0],
	maplist(generalize_formula(Map), Args0, Args),
	To =.. [Name|Args].
generalize_formula(_, Formula, Formula).


generalize_sheet($(S), _, $(S)) :- !.
generalize_sheet(S0, Map, S) :-
	map_sheet(Map, F-T),
	(   S0 == F
	->  S = T
	;   S = S0
	).
generalize_x($(X), _, $(X)) :- !.
generalize_x(X0, Map, X) :-
	map_x(Map, F-T),
	generalize_cordinate(X0, F-T, X).
generalize_y($(Y), _, $(Y)) :- !.
generalize_y(Y0, Map, Y) :-
	map_y(Map, F-T),
	generalize_cordinate(Y0, F-T, Y).

generalize_cordinate(X0, F-T, X) :-
	(   X0 == F
	->  X = T
	;   atom(T)
	->  X = T
	;   integer(X0)
	->  Dif is X0-F,
	    (	Dif > 0
	    ->	X #= T+Dif
	    ;	MinDif is -Dif,
		X #= T-MinDif
	    )
	;   X = X0
	).

%%	simplify_formula(+FormulaIn, -FormulaOut) is det.
%
%	Replace single-cell ranges with a cell.

simplify_formula(Var, Var) :-
	var(Var), !.
simplify_formula(cell_range(S,X,Y,X,Y), cell(S,X,Y)) :- !.
simplify_formula(F0, F) :-
	compound(F0), !,
	F0 =.. [Name|Args0],
	maplist(simplify_formula, Args0, Args),
	F =.. [Name|Args].
simplify_formula(F, F).

%%	group_formula(+Group, -Formula)
%
%	Materialize  a  group,  describing  the   formula  similarly  as
%	sheet_ds_formulas/2, but using a node representation that is not
%	limited to rectangular areas.  The node representation is one of
%
%	  - cell(Sheet,Xs,Y)
%	  - cell(Sheet,X,Ys)
%	  - cell(Sheets,X,Y)
%	  - cell_range(Sheets,SX,EX,SY,EY)

group_formula(f(S,X,Y,F), cell(S,X,Y) = F).
group_formula(forall(What, In, f(S,X,Y,F)),
	      Target = Formula) :- !,
	ground_formula(What, In, f(S,X,Y,cell(S,X,Y)), Target),
	ground_formula(What, In, f(S,X,Y,F), Formula).
group_formula(F, F).

ground_formula(What, In, f(S,X,Y,F0), Formula) :-
	target(F0), !,
	(   ground_target(F0, What, In, f(S,X,Y,F0), Formula)
	->  true
	;   gtrace,
	    ground_target(F0, What, In, f(S,X,Y,F0), Formula)
	).
ground_formula(What, In, f(S,X,Y,F0), F) :-
	compound(F0), !,
	F0 =.. [Name|Args0],
	ground_formulas(Args0, What, In, f(S,X,Y), Args),
	F  =.. [Name|Args].
ground_formula(_, _, f(_,_,_,F), F).

target(cell(_,_,_)).
target(cell_range(_,_,_,_,_)).

ground_formulas([], _, _, _, []).
ground_formulas([H0|T0], What, In, f(S,X,Y), [H|T]) :-
	ground_formula(What, In, f(S,X,Y,H0), H),
	ground_formulas(T0, What, In, f(S,X,Y), T).

ground_target(cell(S,Xc,Y), col, X in Xs, f(_,X,_,_), cell(S,Xcs,Y)) :- !,
	materialize(Xs, X, Xc, Xcs).
ground_target(cell(S,X,Yc), row, Y in Ys, f(_,_,Y,_), cell(S,X,Ycs)) :- !,
	materialize(Ys, Y, Yc, Ycs).
ground_target(cell(Sc,X,Y), sheet, S in Ss, f(S,_,_,_), cell(Scs,X,Y)) :- !,
	materialize(Ss, S, Sc, Scs).
ground_target(cell(S,Xc,Yc), area, [X in Xs, Y in Ys], f(_,X,Y,_),
	      cell(S,Xcs,Ycs)) :- !,
	materialize(Xs, X, Xc, Xcs),
	materialize(Ys, Y, Yc, Ycs).
ground_target(cell(Sc,Xc,Yc), workbook, [S in Ss, X in Xs, Y in Ys], f(S,X,Y,_),
	      cell(Scs,Xcs,Ycs)) :- !,
	materialize(Ss, S, Sc, Scs),
	materialize(Xs, X, Xc, Xcs),
	materialize(Ys, Y, Yc, Ycs).
ground_target(cell_range(S,Xac,Ya,Xzc,Yz), col, X in Xs, f(_,X,_,_),
	      cell_range(S,Xas,Ya,Xzs,Yz)) :- !,
	materialize(Xs, X, Xac, Xas),
	materialize(Xs, X, Xzc, Xzs).
ground_target(cell_range(S,Xa,Yac,Xz,Yzc), row, Y in Ys, f(_,_,Y,_),
	      cell_range(S,Xa,Yas,Xz,Yzs)) :- !,
	materialize(Ys, Y, Yac, Yas),
	materialize(Ys, Y, Yzc, Yzs).
ground_target(cell_range(Sc,Xa,Ya,Xz,Yz), sheet, S in Ss, f(S,_,_,_),
	      cell_range(Scs,Xa,Ya,Xz,Yz)) :- !,
	materialize(Ss, S, Sc, Scs).
ground_target(cell_range(S,Xac,Yac,Xzc,Yzc), area, [X in Xs, Y in Ys], f(_,X,Y,_),
	      cell_range(S,Xas,Yas,Xzs,Yzs)) :- !,
	materialize(Xs, X, Xac, Xas),
	materialize(Xs, X, Xzc, Xzs),
	materialize(Ys, Y, Yac, Yas),
	materialize(Ys, Y, Yzc, Yzs).
ground_target(cell_range(Sc,Xac,Yac,Xzc,Yzc),
	      workbook, [S in Ss, X in Xs, Y in Ys], f(S,X,Y,_),
	      cell_range(Scs,Xas,Yas,Xzs,Yzs)) :- !,
	materialize(Ss, S, Sc, Scs),
	materialize(Xs, X, Xac, Xas),
	materialize(Xs, X, Xzc, Xzs),
	materialize(Ys, Y, Yac, Yas),
	materialize(Ys, Y, Yzc, Yzs).

materialize(Domain, Var, Values, Materialized) :-
	materialize2(Domain, Var, Values, Materialized0),
	simplify_domain(Materialized0, Materialized).

materialize2([], _, _, []).
materialize2([H0|T0], V, Vc, [H|T]) :-
	(   H0 = (S-E)
	->  H = (Sh-Eh),
	    findall(Vc, (V=S;V=E), [Sh,Eh])
	;   findall(Vc, V=H0, [H])
	),
	materialize2(T0, V, Vc, T).

simplify_domain(Domain0, Domain) :-
	phrase(expand(Domain0), Domain1),
	compress(Domain1, Domain2),
	(   Domain2 = [One]
	->  Domain = One
	;   Domain = Domain2
	).

expand([])    --> !, [].
expand([H|T]) --> !, expand(H), expand(T).
expand(F-T)   --> !, numlist(F,T).
expand(One)   --> [One].

numlist(T,T) --> !, [T].
numlist(F,T) --> [F], {F2 is F+1}, numlist(F2,T).




%%	sheet_dependency_graph(:Sheet, -UGraph) is det.
%
%	Create a UGraph that represents  the dependencies between cells.
%	Nodes in the cells are terms cell(S,X,Y).

sheet_dependency_graph(Sheet, Graph) :-
	sheet_formula_groups(Sheet, Groups, Singles0),
	append(Groups, Plain0),
	strip_dollar(Plain0, Plain),
	maplist(group_formula, Plain, PlainGroups),
	strip_dollar(Singles0, Singles),
	append(Singles,PlainGroups,Results),
	findall(Node-Inputs,
		group_dependency(Sheet,Results,Node,Inputs),
		Graph0),
	sort(Graph0, Graph1),
	findall(Node-Original,
		find_copy_node(Results,Node,Original),
		Replacements),
	maplist(replace_copy(Replacements),Graph1,Graph2),
	pairs_keys_values(Graph2, Left, RightSets),
	append(RightSets, Right0),
	sort(Right0, Right),
	                                   % Add missing (source) nodes
	ord_subtract(Right, Left, Sources),
	maplist(pair_nil, Sources, SourceTerms),
	ord_union(Graph2, SourceTerms, Graph3),
	transpose(Graph3, Graph4),
	sort(Graph4,Graph).

sheet_dependency_graph(Sheet, Graph1, Graph) :-
	sheet_formula_groups(Sheet, Groups, Singles0),
	append(Groups, Plain0),
	strip_dollar(Plain0, Plain),
	maplist(group_formula, Plain, PlainGroups),
	strip_dollar(Singles0, Singles),
	append(Singles,PlainGroups,Results),
	findall(Node-Inputs,
		group_dependency(Sheet,Results,Node,Inputs),
		Graph0),
%	findall(Cell-Dep,
%		cell_dependency(Sheet,Cell,Dep),
%		Graph0),
%	maplist(strip_dollar,Graph0,Graph1),
	transform_sheets(Graph0, Graph01),
	transform_ranges(Graph01, Graph02),
%	trace,
	sort(Graph02, Graph1),
	pairs_keys_values(Graph1, Left, RightSets),
	append(RightSets, Right0),
	sort(Right0, Right),
	                                   % Add missing (source) nodes
%	filter_overlap(Left, Left1),
%	filter_overlap(Right1, Right),
	new_subtract(Right, Left, Sources),
	maplist(pair_nil, Sources, SourceTerms),
	ord_union(Graph1, SourceTerms, Graph2),
	transpose(Graph2, Graph).

new_subtract(Right, Left, Sources):-
	select_widest_cell_range(Right, Left, S1),
	sort(S1, Sources).

select_widest_cell_range([], _L, []):-!.
select_widest_cell_range([C1|Rest], L, Rest1):-
	member(C2, L),
	range_included(C1, C2),!,
	select_widest_cell_range(Rest, L, Rest1).
select_widest_cell_range([C|Rest], L, [C|Rest1]):-
	select_widest_cell_range(Rest, L, Rest1),!.

range_included(C1, C2):-
	C1 = cell(S, X1, Y1),
	C2 = cell(S, X2, Y2),
	inside(X1, X2),
	inside(Y1, Y2),!.

inside(_X, []):- fail,!.   %TBD even more complex comparisons, e.g. R1 and R2
inside(X,X):-!.
inside([],_X):-!.
inside([F|T],  R):-!,
	inside(F, R),
	inside(T, R),!.
inside(X, _Range):-
	var(X),!.
inside(X, X0-X1):-
	X >= X0,
	X =< X1,!.
inside(A-B, X0-X1):-
	A >= X0,
	B =< X1,!.
inside(A-B, [X0-X1|_Rest]):-
	A >= X0,
	B =< X1,!.
inside(X, [X0-X1|_Rest]):-
	X >= X0,
	X =< X1,!.
inside(X, [XL|_Rest]):-
	member(X, XL) ,!.
inside(X, [_|Rest]):-
	inside(X, Rest).


transform_ranges([], []):-!.
transform_ranges([cell_range(S, X1, Y1, X1, Y2)|Rest],
		 [cell(S, X1, Y1-Y2)|TRest]):-
	transform_ranges(Rest, TRest),!.
transform_ranges([cell_range(S, X1, Y1, X1, Y2)-D|Rest],
		 [cell(S, X1, Y1-Y2)-D1|TRest]):-
	transform_ranges(D, D1),
	transform_ranges(Rest, TRest),!.
transform_ranges([cell_range(S, X1, Y1, X2, Y2)-D|Rest],
		 [cell(S, X1-X2, Y1-Y2)-D1|TRest]):-
	transform_ranges(D, D1),
	transform_ranges(Rest, TRest),!.
transform_ranges([X-D|Rest], [X1-D1|TRest]):-
	transform_ranges([X], [X1]),
	transform_ranges(D, D1),
	transform_ranges(Rest, TRest),!.
transform_ranges([X|Rest], [X|TRest]):-
	transform_ranges(Rest, TRest),!.

transform_sheets([], []):-!.
transform_sheets([C-D|Rest], SRest):-
	C = cell(Sheet, _, _),
	is_list(Sheet),!,
	transform_sheets(Rest, Rest1),
	findall(C1-D1, (member(S, Sheet),
		        select_sheet(Sheet, S, C-D, C1-D1)), CL),
	append(CL, Rest1, SRest),!.
transform_sheets([C-D|Rest], [C-D|Rest1]):-
	transform_sheets(Rest, Rest1),!.

select_sheet(SList, Sheet, cell(SList, X, Y)-D, cell(Sheet, X, Y)-D1):-
	maplist(select_sheet1(SList, Sheet), D, D1).
select_sheet1(SList, Sheet, cell(SList, X, Y), cell(Sheet, X, Y)):-!.
select_sheet1(SList, Sheet, cell_range(SList, X1, Y1, X2, Y2), cell(Sheet, X1-X2, Y1-Y2)):-!.

orig_dependency_graph(Sheet, Graph) :-
	findall(Cell-Dep,
		cell_dependency(Sheet,Cell,Dep),
		Graph0),
	maplist(strip_dollar,Graph0,Graph1),
	sort(Graph1, Graph2),
	pairs_keys_values(Graph2, Left, RightSets),
	append(RightSets, Right0),
	sort(Right0, Right),
	                                   % Add missing (source) nodes
	ord_subtract(Right, Left, Sources),
	maplist(pair_nil, Sources, SourceTerms),
	ord_union(Graph2, SourceTerms, Graph3),
	transpose(Graph3, Graph).

orig_no_copy_graph(Sheet, Graph) :-
	findall(Cell-Dep,
		cell_dependency(Sheet,Cell,Dep),
		Graph0),
	maplist(strip_dollar,Graph0,Graph1),
	sort(Graph1, Graph2),
	findall(Cell-Original,
		find_copy_cell(Cell,Original),
		Replacements0),
	maplist(strip_dollar,Replacements0,Replacements),
	maplist(replace_copy(Replacements),Graph2,Graph3),
	pairs_keys_values(Graph3, Left, RightSets),
	append(RightSets, Right0),
	sort(Right0, Right),
	                                   % Add missing (source) nodes
	ord_subtract(Right, Left, Sources),
	maplist(pair_nil, Sources, SourceTerms),
	ord_union(Graph3, SourceTerms, Graph4),
	transpose(Graph4, Graph).




pair_nil(X,X-[]).

ds_dependency(Sheet,Groups,Node,Inputs):-
	Sheet = M:_,
	member(Node = GenFormula,Groups),
	formula_cells(GenFormula,M, Inputs0, []),
	sort(Inputs0, Inputs).

group_dependency(Sheet1,Results,Node,Inputs):-
	(   Sheet1 = _U:Sheet ->true    %added BJW
	;   Sheet = Sheet1),
	member(Result, Results),
	(   Result = (Node = GenFormula)
	->  group_inputs(GenFormula,Inputs0, [])
	;   Result = f(Sheet,X,Y,Formula)
	->  Node = cell(Sheet,X,Y),
	    group_inputs(Formula,Inputs0, [])
	),
	sort(Inputs0, Inputs).


% find_copy_node(+Results,-Node,-Original) is det
%
% Find nodes that are created by a copy action, i.e. these nodes have
% one single cell (original) as input.Input variable 'Results' is the
% appended list of Groups(group_formula format) and Singles resulting
% from sheet_formula_groups.
%
%
% replace_copy(+Replacements,+In,-Out)
%
% Detects copy nodes in a pair of node-[inputs]; if there are copy nodes
% present in [inputs], then these are replaced by the original nodes. If
% the node in node-[inputs] is the copy node, than it is replaced
% by the original and the corresponding [inputs] are an empty list.
% Input variable 'Replacements' is a list of copy nodes and
% corresponding originals. The actual copy node is

find_copy_cell(Cell,Original):-
	M = user,
	cell_formula(S0,X0,Y0,cell(S,X,Y)),
	Cell = cell(M:S0,X0,Y0),
	Original = cell(M:S,X,Y).


find_copy_node(Results,Node,Original):-
	member(Result, Results),
	(   Result = (Node = cell(S,X,Y))
	->  Original = cell(S,X,Y)
	;   Result = f(Sheet0,X0,Y0,cell(S,X,Y))
	->  Node = cell(Sheet0,X0,Y0),
	    Original = cell(S,X,Y)
	).

replace_copy(Replacements,In,Out):-
	In =Node0-Inputs0,
	replace_copy2(Replacements,Node0,Node),
	maplist(replace_copy2(Replacements),Inputs0,Inputs),
	(   Inputs == [Node]
	->  Out = Node-[]
	;   Out =Node-Inputs
	)	.

replace_copy2(Replacements,Node,Original):-
	member(Node-Original,Replacements),!.
replace_copy2(_,Node,Node).


% intermed_result(:Sheet,+Graph,-Sink) is det

% Finds intermediate results in sheet_dependency_graph.
%
% An intermediate result is a sink cell (no dependents) of which the
% inputs have more dependents than that sink cell. An intermediate
% result cell is a dead end in the dependency graph, but the
% calculation workflow continues through its inputs

intermed_result(Graph,Sink):-
	member(Sink-[],Graph),
	member(_Node-Deps,Graph),
	member(Sink,Deps),
	length(Deps,L),L>1.

correct_overlap(GraphIn,GraphOut):-
	sheet_dependency_graph(_, GraphIn),
	maplist(replace_overlap(GraphIn),GraphIn,GraphOut).



replace_overlap(Graph,In,Out):-
	In= cell(S,X,Y)-[],
	member(Out-_,Graph),
	Out= cell_range(S,SX,SY,EX,EY),
	ds_inside(cell_range(S,SX,SY,EX,EY),X,Y),!.
replace_overlap(_,C,C).


% Copied from formula_cells but added but using a node representation that is not
% limited to rectangular areas. See group_formula

group_inputs(cell(S,X,Y),[cell(S,X,Y)|T], T) :- !.
group_inputs(cell([S0|S],X,Y), [cell([S0|S],X,Y)|T], T) :- !.
group_inputs(cell([S0|S],[X0-X],Y), [cell([S0|S],[X0-X],Y)|T], T) :- !.
group_inputs(cell([S0|S],X,[Y0-Y]),[cell([S0|S],X,[Y0-Y])|T], T) :- !.
group_inputs(cell([S0|S],[X0-X],[Y0-Y]), [cell([S0|S],[X0-X],[Y0-Y])|T], T) :- !.
group_inputs(cell(S,[X0-X],Y), [cell(S,[X0-X],Y)|T], T) :- !.
group_inputs(cell(S,X,[Y0-Y]), [cell(S,X,[Y0-Y])|T], T) :- !.
group_inputs(cell(S,[X0-X],[Y0-Y]), [cell(S,[X0-X],[Y0-Y])|T], T) :- !.

group_inputs(DataSource, Cells, Rest) :-
	DataSource = cell_range(S,SX,SY,EX,EY), !,
	Cells = [cell_range(S,SX,SY,EX,EY)|Rest].
group_inputs(ext(URL, DS), Cells, Cells) :- !,
	debug(dep, 'External ref: ~p ~p', [URL, DS]).
group_inputs(Compound, Cells, Rest) :-
	compound(Compound), !,
	Compound =.. [_|Args],
	list_inputs(Args, Cells, Rest).
group_inputs(_, Cells, Cells).

list_inputs([], Cells, Cells).
list_inputs([H|T], Cells, Rest) :-
	group_inputs(H, Cells, Rest0),
	list_inputs(T, Rest0, Rest).


get_op(F, F0):-
	F0 =eval(_),!,
	F0 =.. [Name|Args0],
	maplist(get_op, Args0, Args),
	F =.. [Name|Args].
get_op2(F, Op):-
	F =cell(_,_,_),!,
	Op = 'Cell'.
get_op2(_, Op):-
	Op = 'Math'.





cell_dependency(Sheet, cell(Sheet,X,Y), Inputs) :-
	Sheet = M:_,
	cell_formula(Sheet, X, Y, Formula),
%	formula_cells(Formula, M, Inputs0, []),
	simplify_lookup(Formula,Simple),
	formula_cells(Simple, M, Inputs0, []),
	sort(Inputs0, Inputs).


formula_cells(cell(S,X,Y), M, [cell(M:S,X,Y)|T], T) :- !.
formula_cells(DataSource, M,  Cells, Rest) :-
	DataSource = cell_range(S,SX,SY,EX,EY), !,
	Cells = [cell_range(M:S,SX,SY,EX,EY)|Rest].
formula_cells(ext(URL, DS), _M, Cells, Cells) :- !,
	debug(dep, 'External ref: ~p ~p', [URL, DS]).
formula_cells(Compound, M, Cells, Rest) :-
	compound(Compound), !,
	Compound =.. [_|Args],
	list_formula_cells(Args, M, Cells, Rest).
formula_cells(_, _, Cells, Cells).

list_formula_cells([], _, Cells, Cells).
list_formula_cells([H|T], M, Cells, Rest) :-
	formula_cells(H, M, Cells, Rest0),
	list_formula_cells(T, M, Rest0, Rest).

%%	cell_dependency_graph(:Sheet, +X, +Y, +Direction, -Graph) is det.
%
%	True when Graph is an  Ugraph   expressing  the  dependencies of
%	StartCell. Direction is one of =inputs=, =outputs= or =both=.
%
%	@tbd	Implement =outputs= and =both=. Probably need to
%		materialize the dependecies for that.  We could do
%		that while loading the spreadsheet?

cell_dependency_graph(Sheet, X, Y, inputs, Graph) :- !,
	input_graph(Sheet, X, Y, Graph).
cell_dependency_graph(_,_,_,Dir,_) :-
	must_be(oneof([inputs]), Dir).

input_graph(Sheet, Col, Y, Graph) :-
	column_x(Col, X),
	Cell0 = cell(Sheet,X,Y),
	empty_assoc(V0),
	put_assoc(Cell0, V0, true, V1),
	traverse_input_graph([Cell0], V1, Edges, []),
	vertices_edges_to_ugraph([Cell0], Edges, Graph).

traverse_input_graph([], _, Edges, Edges).
traverse_input_graph([Cell0|CellT], Visited0, Edges, ETail) :-
	inputs(Cell0, Inputs),
	edges(Inputs, Cell0, Edges, Tail0),
	update_visited(Inputs, Visited0, Visited1, NewInputs, CellT),
	traverse_input_graph(NewInputs, Visited1, Tail0, ETail).

inputs(cell(Sheet,X,Y), Inputs) :-
	cell_formula(Sheet, X, Y, Formula0), !,
	strip_dollar(Formula0, Formula),
	Sheet = M:_,
	formula_cells(Formula, M, Inputs, []).
inputs(_, []).

edges([], _, Edges, Edges).
edges([H|T], V0, [H-V0|Edges], ET) :-
	edges(T, V0, Edges, ET).

update_visited([], Visited, Visited, Inputs, Inputs).
update_visited([H|T], Visited0, Visited, Inputs0, Inputs) :-
	get_assoc(H, Visited0, _), !,
	update_visited(T, Visited0, Visited, Inputs0, Inputs).
update_visited([H|T], Visited0, Visited, [H|Inputs1], Inputs) :-
	put_assoc(H, Visited0, true, Visited1),
	update_visited(T, Visited1, Visited, Inputs1, Inputs).


column_x(Col, X) :-
	atom(Col), !,
	upcase_atom(Col, COL),
	column_name(X, COL).
column_x(Col, X) :-
	integer(Col), !,
	X = Col.
column_x(Col, _) :-
	type_error(column, Col).
