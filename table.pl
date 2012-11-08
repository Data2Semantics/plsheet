:- module(table,
	  [ assert_tables/2,		% ?Sheet, ?Type
	    tables/3,			% ?Sheet, +Type, -Tables
	    table/2,			% +Data, -Support
	    cell_property/4,		% :Sheet, ?X, ?Y, ?Property
	    cells_outside_tables/3	% +Sheet, +Table, -Cells
	  ]).
:- use_module(recognise).
:- use_module(datasource).
:- use_module(ods_table).
:- use_module(library(lists)).

:- meta_predicate
	tables(:, ?, -),
	assert_tables(:, ?),
	cell_property(:,?,?,?).

%%	assert_tables(:Sheet, ?Type) is det.
%
%	Infer and assert identified tables. Creates the following facts:
%
%	  * table(TableID, Type, MainDS, HeaderDSList, UnionDS)
%	  * cell_property(Sheet CellId, table(TableID))

assert_tables(Sheet, Type) :-
	Sheet = M:_,
	tables(Sheet, Type, Tables),
	forall(member(T, Tables),
	       assert_table(M:T)).

assert_table(M:T) :-
	assertz(M:T),
	T = table(TabId, _Type, _MainDS, _HdrDS, Union),
	ds_sheet(Union, Sheet),
	forall(ds_inside(Union, X, Y),
	       ( cell_id(X,Y,CellId),
		 assertz(M:cell_property(Sheet,CellId,table(TabId)))
	       )).

%%	cell_property(:Sheet, ?X, ?Y, ?Property)
%
%	Query (inferred) properties of the cell Sheet.XY.

cell_property(M:Sheet, X, Y, Property) :-
	(   nonvar(X), nonvar(Y)
	->  cell_id(X,Y,Id),
	    M:cell_property(Sheet,Id,Property)
	;   M:cell_property(Sheet,Id,Property),
	    cell_id(X,Y,Id)
	).


%%	tables(?Sheet, +Type, -Tables) is det.
%
%	Make an initial guess  at  all  tables.   Table  is  a  list  of
%	table(Data, Headers,Union).

tables(Sheet, Type, Tables) :-
	findall(SheetTables,
		( setof(Table,
			Type^table_in_sheet(Sheet, Type, Table),
			SheetTables0),
		  remove_inside(SheetTables0, SheetTables)
		),
		NestedTables),
	append(NestedTables, Tables).

table_in_sheet(M:Sheet, Type, table(Id,Type,DS,Headers,Union)) :-
	ds_sheet(DS, Sheet),
	cell_class(Type),
	anchor(DS, Type),
	once((block(M:DS, Type),
	      table(M:DS, Headers))),
	ds_union([DS|Headers], Union),
	ds_id(DS, Id).

%%	remove_inside(+Tables0, -Tables) is det.
%
%	Remove all tables that are entirely enclosed into other tables.

remove_inside(Tables0, Tables) :-
	remove_inside(Tables0, Tables0, Tables).

remove_inside([], _, []).
remove_inside([H|T0], All, T) :-
	H = table(_,_,Union),
	member(T2, All),
	T2 \== H,
	T2 = table(_,_,U2),
	ds_intersection(Union, U2, Union), !,
	remove_inside(T0, All, T).
remove_inside([H|T0], All, [H|T]) :-
	remove_inside(T0, All, T).


%%	cells_outside_tables(+Sheet, +Table, -Cells) is det.
%
%	True when Cells is a list of cell(Sheet,X,Y) that is outside any
%	table.

cells_outside_tables(Sheet, Tables, Cells) :-
	findall(cell(Sheet,X,Y),
		( sheet_bb(Sheet, SheetDS),
		  ds_inside(SheetDS, X, Y),
		  cell_value(Sheet, X, Y, _),
		  \+ ( member(table(_,_,DS), Tables),
		       ds_inside(DS,X,Y)
		     )
		),
		Cells).


%%	table(:DataDS, ?SupportDS) is nondet.
%
%	True when there is a table  with   DataDS  and a list of support
%	datasources.

table(QDataDS, TitleDS) :-
	QDataDS = _:DataDS,
	ds_size(DataDS, Cols, Rows),
	top_rows(QDataDS, -1, TitleDS, Left),
	left_columns(QDataDS, -1, Left, Right),
	right_columns(QDataDS, Cols, Right, Bottom),
	bottom_rows(QDataDS, Rows, Bottom, []).

%%	top_rows(:DS, +StartIndex, -Rows, ?Tail) is nondet.
%%	bottom_rows(:DS, +StartIndex, -Rows, ?Tail) is nondet.
%%	left_columns(:DS, +StartIndex, -Rows, ?Tail) is nondet.
%%	right_columns(:DS, +StartIndex, -Rows, ?Tail) is nondet.

top_rows(QDataDS, Index, [Row|Rows], Tail) :-
	QDataDS = M:DataDS,
	ds_unbounded_row_slice(DataDS, Index, Row),
	row(M:Row, string),
	Up is Index - 1,
	top_rows(QDataDS, Up, Rows, Tail).
top_rows(_, _, Tail, Tail).


bottom_rows(QDataDS, Index, [Row|Rows], Tail) :-
	QDataDS = M:DataDS,
	ds_unbounded_row_slice(DataDS, Index, Row),
	row(M:Row, string),
	Down is Index + 1,
	bottom_rows(QDataDS, Down, Rows, Tail).
bottom_rows(_, _, Tail, Tail).


left_columns(QDataDS, Index, [Col|Cols], Tail) :-
	QDataDS = M:DataDS,
	ds_unbounded_column_slice(DataDS, Index, Col),
	col(M:Col, string),
	Up is Index - 1,
	left_columns(QDataDS, Up, Cols, Tail).
left_columns(_, _, Tail, Tail).

right_columns(QDataDS, Index, [Col|Cols], Tail) :-
	QDataDS = M:DataDS,
	ds_unbounded_column_slice(DataDS, Index, Col),
	col(M:Col, string),
	Right is Index + 1,
	right_columns(QDataDS, Right, Cols, Tail).
right_columns(_, _, Tail, Tail).

