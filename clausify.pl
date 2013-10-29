%%%%   clausify.pl   %%%%
%%%%   Valutazione: 25/30   %%%%

variabile(X) :- var(X).

costante(X) :- atomic(X).

termine(X) :- variabile(X).
termine(X) :- costante(X).

predicato(X) :-
	costante(X), !.

predicato(X) :-
	compound(X),
	X =.. [L | Ls],
	costante(L),
	valid_fbf_private(Ls).

/*
  Questi predicati servono
  per controllare le varie fbf
*/
fbf(predicato).
fbf(not).
fbf(and).
fbf(or).
fbf(implies).
fbf(every).
fbf(exist).
fbf(X) :- compound(X).
/* -------------------------- */

/*
  Questi predicati invece
  servono per contare le
  arità dei diversi op logici
*/
arity(not, 1).
arity(and, N) :- N > 1.
arity(or, N) :- N > 1.
arity(implies, 2).
arity(every, 2).
arity(exist, 2).

arity_counter([], 0).
arity_counter([_ | T], C) :-
	arity_counter(T, C1),
	C is C1 + 1.
/* ------------------------------ */

pari(P) :-
	M is P mod 2,
	M = 0.

/*
  Questi predicati servono ad
  estrarre i letterali nel caso
  di not(_) oppure not(not(_))
*/
estrai_letterale([X | []], N) :-
	N = X, !.

estrai_letterale([X | []], N) :-
	X =.. [_ | T],
	T \= [],
	estrai_letterale(T, N).

estrai_letterale([X | []], N) :-
	X =.. [_ | Ls],
	estrai_letterale(Ls, N).

estrai_letterale([X | []], N) :-
	compound(X),
	X =.. [_ | Ls],
	estrai_letterale(Ls, N).

estrai_letterale([_ | Xs], N) :-
	estrai_letterale(Xs, N).
/* --------------------------------- */

/*
  Questi predicati not(X) se i not
  sono un numero pari allora verrà
  semplicemente ritornato X,
  altrimenti verrà ritornato not(X).
*/
not_counter(not(X), M) :-
	predicato(X),
	valid_fbf(X),
	not_counter_private(not(X), M1 ,C1),
	C is C1 - 1,
	pari(C),
	M = M1, !.

not_counter(not(X), M) :-
	predicato(X),
	valid_fbf(X),
	not_counter_private(not(X), M1 ,C1),
	C is C1 - 1, 
	not(pari(C)),
	M = not(M1), !.

not_counter_private(not(X), M, C) :-
	predicato(X),	
	not_counter_private(X, M, C1),
	C is C1 +1.

not_counter_private(not(X), M, 0) :-
	not(variabile(X)),
	X =.. [H | _],
	H \= not,
	fbf2cnf(X, CNF),
	M = CNF.

not_counter_private(not(X), M, C) :-
	not(variabile(X)),
	X =.. [H | T],
	H = not,
	valid_fbf(T),
	not_counter_private(X, M, C1),
	C is C1 +1.

not_counter_private(not(X), M, C) :-
	not(variabile(X)),
	X =.. [H, A | T],
	H = and,
	and_not(A, T, FBF),
	append([or], FBF, NFBF),
	NFBF1 =.. NFBF,
	fbf2cnf(NFBF1, NCNF),
	C is 0 +1,
	M = NCNF.

not_counter_private(not(X), M, C) :-
	not(variabile(X)),
	X =.. [H | _],
	H = implies,
	fbf2cnf_private([X], X1),
	fbf2cnf(not(X1), X2),
	C = 1 ,
	M = X2.

not_counter_private(not(X), M, C) :-
	not(variabile(X)),
	X =.. [H, A | T],
	H = or,
	or_not(A, T, FBF),
	append([and], FBF, NFBF),
	NFBF1 =.. NFBF,
	fbf2cnf(NFBF1, NCNF),
	C is 0 +1,
	M = NCNF.

not_counter_private(not(X), M, C) :-
	not(variabile(X)),
	X =.. [H , A| T],
	H = every,
	append([not], T, NT),
	L =.. NT,
	append([A], [L], T2),
	append([exist], T2, NFBF),
	NFBF1 =.. NFBF,
	fbf2cnf(NFBF1, NCNF),
	C is 0 +1,
	M = NCNF.

not_counter_private(not(X), M, C) :-
	not(variabile(X)),
	X =.. [H , A| T],
	H = exist,
	append([not], T, NT),
	L =.. NT,
	append([A], [L], T2),
	append([every], T2, NFBF),
	NFBF1 =.. NFBF,
	fbf2cnf(NFBF1, NCNF),
	C is 0 +1,
	M = NCNF.
/* ------------------------------------- */

/*
  Questi predicati servono per
  riscrivere la regola numero 2
*/
and_not(A, [], CNF) :-
	append([not(A)], [], CNF).

and_not(A, [H | FBF], CNF) :-
	fbf2cnf(H, CNF3),
	and_not(CNF3, FBF, CNF2),
	append([not(A)], CNF2, CNF1),
	CNF = CNF1, !.
/* ------------------------------------------- */

/*
  Questi predicati servono per
  riscrivere la regola numero 3
*/
or_not(A, [], CNF) :-
	append([not(A)], [], CNF).

or_not(A, [H | FBF], CNF) :-
	fbf2cnf(H, CNF3),
	or_not(CNF3, FBF, CNF2),
	append([not(A)], CNF2, CNF1),
	CNF = CNF1, !.
/* ------------------------------------------ */
   
/*
  Questi predicati effettuano i vari
  controlli sui vari operatori logici
*/
valid_fbf(X) :- 
	X =.. [L | Ls],
	termine(L),
	fbf(L),
	arity_counter(Ls, C),
	arity(L, C),
	valid_fbf_private(Ls), !.

valid_fbf(X) :- 
	X =.. [L | []],
	termine(L), !.

valid_fbf(X) :- 
	X =.. [L | _],
	termine(L),
	not(fbf(L)),
	predicato(X).

valid_fbf_private([X | []]) :-
	termine(X), !.

valid_fbf_private([X | []]) :-
	compound(X),
	valid_fbf(X), !.

valid_fbf_private([X | Xs]) :-
	termine(X),
	valid_fbf_private(Xs), !.

valid_fbf_private([X | Xs]) :-
	compound(X),
	valid_fbf(X),
	valid_fbf_private(Xs).
/* --------------------------------*/

/*
  Il predicato fbf2cnf
  trasforna una FBF in una CNF
*/
fbf2cnf(FBF, CNFFBF) :-
	termine(FBF),
	CNFFBF = FBF, !.

fbf2cnf(FBF, CNFFBF) :-
	predicato(FBF),
	FBF =.. [H | T],
	H \= not,
	H \= and,
	H \= or,
	H \= implies,
	H \= exist,
	H \= every,
	T \=[],
	valid_fbf(FBF),
	CNFFBF = FBF ,!.

fbf2cnf(FBF, CNFFBF) :-
	compound(FBF),
	FBF =.. [H | _],
	H \= exist,
	valid_fbf(FBF),
	fbf2cnf_private([FBF], N),
	CNFFBF = N, !.

fbf2cnf(FBF, CNFFBF) :-
	compound(FBF),
	FBF =.. [H | T],
	H = exist,
	T = [V | T2],
	NFBF =.. T2,
	fbf2cnf(NFBF, FBF2),
	FBF2 =.. L,
	skolem_function([], SK),
	exist_private(V, SK, L, [], F),
	V = SK,
	Final =.. F,
	fbf2cnf(Final, CNF),
	CNFFBF = CNF, !.

/*
  Questi lavorano essenzialmente
  sul quantificatore universale
*/
fbf2cnf(FBF, CNFFBF) :-
	compound(FBF),
	FBF =.. [H | T],
	H = every,
	T = [V | T2],
	T2 = [H2 | _ ],
	H2 =.. [Op | T3],
	T3 = [H3 | T4],
	Op = exist,
	skolem_function([V], SF),
	exist_private(H3, SF, T4, [], NL),
	H3 = SF,
	NFBF =.. NL,
	fbf2cnf(NFBF, NL2),
	CNFFBF = NL2, !.

fbf2cnf(FBF, CNFFBF) :-
	compound(FBF),
	FBF =.. [H | T],
	H = every,
	T = [_ | T2],
	T2 = [H2 | _ ],
	H2 =.. [Op | _],
	Op \= exist,
	fbf2cnf(H2, CNF),
	CNFFBF = CNF, !.
/*----------------------------------------- */

fbf2cnf_private([H | _], CNFFBF) :-
	termine(H),
	CNFFBF = H, !.

fbf2cnf_private([H | _], CNF) :-
	H =.. [H1 | T],
	H1 = exist,
	T \= [],
	T = [_ | T2],
	FBF =.. T2,
	exist(V, FBF),
	CNF = V.

fbf2cnf_private(L, CNF) :-
	L = [H | _],
	H =.. [H1 | Ls],
	H1 = and,
	valid_fbf(H),
	and(H1, Ls, CNF1),
	CNF2 =.. CNF1,
	flatten_and(CNF2, NL),
	append([and], NL, Temp),
	Final =.. Temp,
	CNF = Final, !.

fbf2cnf_private(L, CNF) :-
	L = [H | _],
	H =.. [H1 | Ls],
	H1 = or,
	valid_fbf(H),
	or(H1, Ls, CNF1),
	CNF2 =.. CNF1,
	flatten_or(CNF2, NL),
	append([or], NL, Temp),
	Final =.. Temp,
	CNF = Final, !.

fbf2cnf_private([H | _], CNF) :-
	H =.. [H1 | _],
	H1 = not,
	not_counter(H, M),
	CNF = M.

fbf2cnf_private([H | _], CNF) :-
	H =.. [H1 | T],
	H1 = implies,
	implies(T, M),
	fbf2cnf(M, M1),
	CNF = M1, !.
 /* ---------------------------------- */

/*
  Questo predicato prende una FBF
  la converte in CNF e controlla se
  e' una clausola di horn valida.
*/
horn(FBF) :-
	termine(FBF), !.

horn(FBF) :-
	compound(FBF),
	valid_fbf(FBF),
	fbf2cnf_private([FBF], CNF),
	CNF =.. NCNF,
	horn_private(NCNF, C),
	C < 2, !.

horn_private([H | T], C) :-
	H = or,
	horn_private(T, C1),
	C is C1 + 0, !.

horn_private([H | T], C) :-
	H = and,
	horn_private(T, C1),
	C is C1 + 0, !.

horn_private([H | T], C) :-
	H \= and,
	H \= or,
	H \= not(_),
	horn_private(T, C1),
	C is C1 + 1.

horn_private([H | T], C) :-
	H \= and,
	H \= or,
	H = not(_),
	horn_private(T, C1),
	C is C1 + 0.

horn_private([H | []], C) :-
	H \= and,
	H \= or,
	H = not(_),
	C = 0.

horn_private([H | []], C) :-
	H \= and,
	H \= or,
	H \= not(_),
	C = 1.
/* --------------------------- */

/*
  Questo predicato costruisce
  la disgiunzione logica
*/
or(A, [], CNF) :-
	append([A], [], CNF).

or(A, [H | FBF], CNF) :-
	predicato(H),
	fbf2cnf(H, CNF3),
	or(CNF3, FBF, CNF2),
	append([A], CNF2, CNF1),
	CNF = CNF1, !.
/* ---------------------------------- */

/*
  Questo predicato costruisce
  la congiunzione logica
*/
and(A, [], CNF) :-
	append([A], [], CNF).

and(A, [H | FBF], CNF) :-
	predicato(H),
	fbf2cnf(H, CNF3),
	and(CNF3, FBF, CNF2),
	append([A], CNF2, CNF1),
	CNF = CNF1, !.
/* ----------------------------------- */

/*
  Questi predicati servono
  ad appiattire congiunzioni e
  disgiunzioni. Funzionano
  nello stesso identico modo.
*/
flatten_or(FBF, NL) :-
	FBF =.. [H | T],
	H = or,
	flatten_or_private(T, L),
	NL = L, !.

flatten_or(FBF, NL) :-
	FBF =.. [H | _],
	H \= or,
	append([FBF], [], NL2),
	NL = NL2, !.

flatten_or_private([H | T] , NL) :-
	T \= [],
	compound(H),
	flatten_or(H, L2),
	flatten_or_private(T, L),
	append(L2, L, Final),
	NL = Final, !.

flatten_or_private([H | []] , NL) :-
	compound(H),
	flatten_or(H, L2),
	append(L2, [], Final),
	NL = Final, !.

flatten_or_private([H | T] , NL) :-
	T \= [],
	termine(H),
	flatten_or_private(T, L),
	append([H], L, Final),
	NL = Final, !.

flatten_or_private([H | []], NL) :-
	termine(H),
	append([H], [], L),
	NL = L, !.

flatten_and(FBF, NL) :-
	FBF =.. [H | T],
	H = and,
	flatten_and_private(T, L),
	NL = L, !.

flatten_and(FBF, NL) :-
	FBF =.. [H | _],
	H \= and,
	append([FBF], [], NL2),
	NL = NL2, !.

flatten_and_private([H | T] , NL) :-
	T \= [],
	compound(H),
	flatten_and(H, L2),
	flatten_and_private(T, L),
	append(L2, L, Final),
	NL = Final, !.

flatten_and_private([H | []] , NL) :-
	compound(H),
	flatten_and(H, L2),
	append(L2, [], Final),
	NL = Final, !.

flatten_and_private([H | T] , NL) :-
	T \= [],
	termine(H),
	flatten_and_private(T, L),
	append([H], L, Final),
	NL = Final, !.

flatten_and_private([H | []], NL) :-
	termine(H),
	append([H], [], L),
	NL = L, !.
/* -------------------------------------- */

/*
  Predicato che tratta
  l'implicazione logica
*/
implies([A, B | []], CNF) :-
	H \= not,
	H \= and,
	H \= or,
	H \= implies,
	H \= exist,
	H \= every,
	fbf2cnf(A, A1),
	fbf2cnf(B, B1),
	CNF = or(not(A1), B1),!.

implies([A, B | []], CNF) :-
	fbf2cnf(not(A), A1),
	fbf2cnf(B, B1),
	CNF = or(A1, B1),!.
/* -------------------------------- */

/*
  Predicato che tratta
  il quantificatore esistenziale
*/
exist(V, FBF) :-
	compound(FBF),
	skolem_function([], SK),
	exist_private(V, SK, [FBF], [], _),
	V = SK.

exist_private(V, SK, [H | []], NL, Final) :-
	variabile(H),
	H == V,
	append([SK], NL, NL2),
	Final = NL2, !.

exist_private(V, SK, [H | T], NL, Final) :-
	variabile(H),
	H == V,
	exist_private(V, SK, T, NL, F2),
	append([SK], F2, NL2),
	Final = NL2, !.

exist_private(_, _, [H | []], NL, Final) :-
	termine(H),
	append([H], NL, NL2),
	Final = NL2, !.

exist_private(_, _, [H | T], NL, Final) :-
	termine(H),
	exist_private(_, _, T, NL, F2),
	append([H], F2, NL2),
	Final = NL2, !.

exist_private(V, SK, [H | []], _, Final) :-
	compound(H),
	H =.. [H1 | L],
	exist_private(V, SK, L, [], F2),
	append([H1], F2, NH),
	FH =.. NH,
	append([FH], [], NL2),
	Final = NL2, !.

exist_private(V, SK, [H | T], NL, Final) :-
	compound(H),
	H =.. [H1 | L],
	exist_private(V, SK, L, [], F2),
	append([H1], F2, NH),
	FH =.. NH,
	exist_private(V, SK, T, NL, F3),
	append([FH], F3, NL2),
	Final = NL2, !.
/* --------------------------------------------- */

skolem_variable(V, SK) :- var(V), gensym(skv, SK).
skolem_function([], SF) :- skolem_variable(_, SF).
skolem_function([A | ARGS], SF) :-
	gensym(skf, SF_op),
	SF =.. [SF_op, A | ARGS].

%%%%   EOF   %%%%

%%%%   This is free software   %%%%
