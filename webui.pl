:- module(webui,
	  [ server/1,			% ?Port
	    show/1,			% +Data
	    show/2,			% +Data, +Options
	    clear/0
	  ]).
:- use_module(library(http/thread_httpd)).
:- use_module(dialog/http_dialog).
:- use_module(library(http/http_dispatch)).
:- use_module(library(http/html_head)).
:- use_module(library(http/html_write)).

:- http_handler(root(.), home, []).
:- http_handler(root('webui.css'), http_reply_file('webui.css', []), []).

server(Port) :-
	http_server(http_dispatch, [port(Port)]).


home(_Request) :-
	reply_html_page(title('Test'),
			[ \html_requires(root('webui.css')),
			  \log_area([id(log)]),
			  \form_area([id(form)])
			]).

show(Data) :-
	show(Data, []).

show(Data, Options) :-
	log_html(log, \webshow(Data), Options).

clear :-
	log_html(log, '', [clear(true)]).

webshow(Data) -->
	html(h4('Showing ~p'-[Data])),
	web_portray(Data).

web_portray(cell_range(Sheet, SX,SY, EX,EY)) -->
	{ integer(SX), integer(SY), integer(EX), integer(EY) }, !,
	html(table(class(spreadsheet),
		   \table_rows(Sheet, SX,SY, EX,EY))), !.
web_portray(cell(Sheet,X,Y)) -->
	web_portray(cell_range(Sheet, X,Y, X,Y)).
web_portray(table(_,_,Union)) -->
	web_portray(Union).
web_portray(List) -->
	{ is_list(List), !,
	  length(List, Len)
	},
	html(h2('List of ~D objects'-[Len])),
	web_portray_list(List).
web_portray(_) -->
	html(p('No rules to portray')).

web_portray_list([]) --> "".
web_portray_list([H|T]) -->
	webshow(H),
	web_portray_list(T).

%%	table_rows(+Sheet, +SX,+SY, +EX,+EY)// is det.

table_rows(Sheet, SX,SY, EX,EY) -->
	{ SY =< EY, !,
	  Y2 is SY+1
	},
	html(tr(\table_row(Sheet, SY, SX, EX))),
	table_rows(Sheet, SX,Y2, EX,EY).
table_rows(_, _,_, _,_) --> [].

table_row(Sheet, Y, SX,EX) -->
	{ SX =< EX, !,
	  X2 is SX+1
	},
	table_cell(Sheet, SX,Y),
	table_row(Sheet, Y, X2,EX).
table_row(_, _, _,_) --> [].

table_cell(Sheet, SX, SY) -->
	{ cell_type(Sheet, SX,SY,percentage),
	  cell_value(Sheet, SX,SY, Value),
	  Val is Value*100
	}, !,
	html(td([Val,'%'])).
table_cell(Sheet, SX, SY) -->
	{ cell_value(Sheet, SX,SY, Value)
	}, !,
	html(td('~q'-[Value])).
table_cell(_, _, _) -->
	html(td(class(empty), [])).

