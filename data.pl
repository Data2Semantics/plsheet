:- module(ods_data,
	  [ assert_table/1,		% +Table

	    sheet_table/2,		% ?Sheet, ?Table
	    table_union/2,		% ?Table, ?Union
	    table_id/2,			% ?Table, ?Id

	    assert_table_property/2,	% :TabId, +Property

	    assert_cell_property/4,	% :Sheet, +X, +Y, ?Property
	    cell_property/4,		% :Sheet, ?X, ?Y, ?Property

	    clean_data/0
	  ]).
:- use_module(datasource).

:- meta_predicate
	assert_table(:),
	sheet_table(:, ?),
	assert_table_property(:, +),
	assert_cell_property(:, +, +, +),
	cell_property(:,?,?,?).

:- module_transparent
	clean_data/0.


/** <module> Data store module

Defined relations:

  * table(TabId, Type, DataDS, HeaderDSList, UnionDS)
  * table_property(TabId, Property)
  * cell_property(Sheet, X, Y, Property)
*/

data(table_property/2).
data(cell_property/3).
data(table/5).

clean_data :-
	context_module(M),
	forall(ods_data:data(Name/Arity),
	       ( functor(Head, Name, Arity),
		 retractall(M:Head)
	       )).


		 /*******************************
		 *	       TABLES		*
		 *******************************/

%%	assert_table(:Table) is det.
%
%	@param Table is table(TabId, _Type, _MainDS, _HdrDS, Union)

assert_table(M:T) :-
	assertz(M:T),
	T = table(TabId, _Type, _MainDS, _HdrDS, Union),
	ds_sheet(Union, Sheet),
	forall(ds_inside(Union, X, Y),
	       assert_cell_property(M:Sheet, X, Y, table(TabId))).

%%	sheet_table(:Sheet, ?Table)
%
%	True when Sheet contains Table.  Table is a struct
%
%	  ==
%	  table(TabId, Type, DataDS, HeaderDSList, UnionDS)
%	  ==

sheet_table(M:Sheet, table(TabId, Type, DataDS, HdrDS, Union)) :-
	ds_sheet(DataDS, Sheet),
	M:table(TabId, Type, DataDS, HdrDS, Union).


%%	table_union(+Table, -Union) is det.
%
%	True uf Union is the UnionDS of Table.

table_union(table(_TabId, _Type, _DataDS, _HdrDS, Union), Union).

%%	table_id(+Table, -Id) is det.

table_id(table(TabId, _Type, _DataDS, _HdrDS, _Union), TabId).


%%	assert_table_property(:TabId, +Property)

assert_table_property(M:TabId, Property) :-
	assertz(M:table_property(TabId, Property)).


		 /*******************************
		 *	       CELLS		*
		 *******************************/

%%	assert_cell_property(:Sheet, +X, +Y, +Property) is det.
%
%	Add a property to a  cell.  Does   nothing  if  the  property is
%	already defined.


assert_cell_property(M:Sheet, X, Y, Property) :-
	cell_id(X,Y,CellId),
	assertz(M:cell_property(Sheet,CellId,Property)).


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

