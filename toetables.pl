:- use_module(library(clpfd)).
:- use_module(library(lists)).
:- use_module(library(between)).
:- use_module(library(sets)).
:- use_module(library(ordsets)).

% ['toes.pl'].

% feasible_excess_full( 10, 3, 9 ).
% feasible_excess_full( 11, 3, 10 ).
% feasible_excess_full( 12, 3, 11 ).
% feasible_excess_full( 13, 3, 19 ).
% feasible_excess_full( 14, 3, 24 ).
% feasible_excess_full( 15, 3, 26 ).

feasible_excess_full( S, D, Excess ) :-
    partitions_trim(S,1,5,D,Parts),
    maplist(feasible_excess_full( D, Excess), Parts ).

feasible_excess_full( D, Excess, ToePartition ) :-
    sum( ToePartition, #=, S ),
    MaxNumWebbings #= 1 + (( Excess + S - 3 )//4),
    numlist( MaxNumWebbings, Inds ),
    maplist( feasible_excess( D, ToePartition, Excess), Inds, _ ).

feasible_excess( D, ToePartition, Excess, NumWebbings, PossiblePartitions ) :-
    findall( Partitions, ( feasible_webbing_partitions( D, ToePartition, Excess, NumWebbings, Vs, Partitions, _, _ ), labeling([], Vs) ), PartitionsList),
    writeln('Checking Feasible Excess for:'),
    writeln([ToePartition, NumWebbings]),
    writeln('Number of Webbing Partitions to check is:'),
    length(PartitionsList, KLK),
    writeln(KLK),
    include( attempt_to_fill_webbing_partition(ToePartition), PartitionsList, PossiblePartitions ).

attempt_to_fill_webbing_partition( ToePartition, WebbingPartitions ) :-
    length( WebbingPartitions, NumWebbings ),
    length( WebMat, NumWebbings ),
    sum( ToePartition, #=, S ),
    maplist( length_(S), WebMat ),
    append( WebMat, Vs ),
    domain( Vs, 0, 1 ),
    maplist( table_webbing(ToePartition), WebMat, WebbingPartitions ),
    transpose(WebMat,TWebMat),
    maplist(sum_geq(2), TWebMat), 
    same_length(Parts,ToePartition),
    maplist(length,Parts,ToePartition),
    append(Parts,TWebMat),
    bagof([Part1,Part2],I^J^(nth1(I,Parts,Part1),nth1(J,Parts,Part2),I<J),PartParts),
    maplist(part_constrainer,PartParts),
    lex_chain(WebMat,[op(#<)]),
    maplist(lex_chain,Parts),
    labeling([], Vs),
    writeln('FOUND A COUNTEREXAMPLE'). % This prints if the supplied excess can in fact be met.

part_constrainer([Part1,Part2]):-
    bagof([PartRow1,PartRow2],I^J^(nth1(I,Part1,PartRow1),nth1(J,Part2,PartRow2)),PartRows),
    maplist(part_constrainer0,PartRows).

part_constrainer0([PartRow1,PartRow2]):-
    same_length(AndRow,PartRow1),
    domain(AndRow,0,1),
    maplist(and_re,PartRow1,PartRow2,AndRow),
    bool_or(AndRow,1).

and_re(A,B,C):-(A#/\ B) #= C.

table_webbing( ToePartition, Webbing, WebbingPartition) :-
    get_permuted_partitions( WebbingPartition, PermutedPartitions),
    maplist( webbings_based_on_perm(ToePartition), PermutedPartitions, PossibleWebbingsList ),
    append( PossibleWebbingsList, WebbingTable ),
    table( [Webbing], WebbingTable ).

webbings_based_on_perm( [A,B,C], [D,E,F], PossibleWebbings ) :-
    sum( [A,B,C], #=, S ),
    findall( Ws, ( length(Ws, S), domain( Ws, 0, 1 ), length(W1, A), length(W2, B), length(W3, C), append([W1,W2,W3], Ws), sum(W1, #=, D), sum(W2, #=, E), sum(W3, #=, F), labeling([], Ws) ), PossibleWebbings ).

get_permuted_partitions( [A,B,C], Ps ) :-
    A #< B,
    B #< C,
    Ps = [ [A,B,C], [A,C,B], [B,A,C], [B,C,A], [C,A,B], [C,B,A] ].
get_permuted_partitions( [A,B,C], Ps ) :-
    A #< B,
    B #= C,
    Ps = [ [A,B,C], [B,A,C], [B,C,A] ].
get_permuted_partitions( [A,B,C], Ps ) :-
    A #= B,
    B #< C,
    Ps = [ [A,B,C], [A,C,B], [C,A,B] ].
get_permuted_partitions( [A,B,C], Ps ) :-
    A #= B,
    B #= C,
    Ps = [ [A,B,C] ].

feasible_webbing_partitions( D, ToePartition, Excess, NumWebbings, Vs, Partitions, Costs, Scores ) :-
    length(Partitions, NumWebbings),
    maplist( length_(3), Partitions ),
    append( Partitions, Vs ),
    domain( Vs, 0, 5 ),
    table_partitions( Partitions ),
    maplist( get_triple_score, Partitions, Scores ),
    maplist( get_sum, Partitions, Costs ),
    get_triple_score( ToePartition, TargetScore), 
    sum( ToePartition, #=, S ),
    ModifiedExcess #= Excess + S,
    sum( Costs, #=<, ModifiedExcess ),
    sum( Scores, #>=, TargetScore ),
    bagof( [C1, C2], I^J^( nth1(I,Costs,C1), nth1(J,Costs,C2), I #< J ), CostPairs),
    maplist( sum_geq(7), CostPairs),
    maplist( basesixify, Partitions, BasedPartitions ),
    numlist( NumWebbings, L ),
    sorting( BasedPartitions, L, BasedPartitions ).

basesixify( [A,B,C], D ) :- D #= 36*A + 6*B + C.

get_sum(L,S) :- sum(L, #=, S).

table_partitions( Partitions ) :- 
    table( Partitions,  [ [0,1,1], [0,1,2], [1,1,1], [0,1,3], [0,2,2], [1,1,2], [0,1,4], [0,2,3], [1,1,3], [1,2,2], [0,1,5], [0,2,4], [0,3,3], [1,1,4], [1,2,3], [2,2,2] ] ).

get_triple_score( [A,B,C], TS) :- TS #= A*B + A*C + B*C.

length_(S,L) :- length(L,S).

sum_leq(Val,List):-
    sum(List,#=<,Val).

sum_geq(Val,List):-
    sum(List,#>=,Val).

partitions_trim(N,MinSize,MaxSize,D,Parts):-is_partition(N,MinSize,MaxSize,Partit),
        setof(TrimPart,P^Partit^(labeling([],Partit),delete(Partit,0,TrimPart),length(TrimPart,P),P=<D),Parts).

is_partition(N,MinSize,MaxSize,RevPart):- 
    MinSize>0, R is N//MinSize, length(Part,R), increasing(Part), domain(Part,0,MaxSize), reverse(Part,RevPart),                 
    ( foreach(X,Part), param(MinSize,MaxSize) do (X#=0 #\/ X#>=MinSize) ),
    sum(Part,#=,N).

increasing([]).
increasing([_]).
increasing(List):-List=[A|Tail1],Tail1=[B|_],A#=<B,increasing(Tail1).

maplist(Pred, Ws, Xs, Ys, Zs) :-
        ( foreach(W,Ws),
            foreach(X,Xs),
            foreach(Y,Ys),
            foreach(Z,Zs),
            param(Pred)
        do call(Pred, W, X, Y, Z)
        ).

maplist(Pred, Us, Ws, Xs, Ys, Zs) :-
        ( foreach(U,Us),
        foreach(W,Ws),
            foreach(X,Xs),
            foreach(Y,Ys),
            foreach(Z,Zs),
            param(Pred)
        do call(Pred, U, W, X, Y, Z)
        ).

writeln( Stream ) :-
    write( Stream ),
    write('\n').