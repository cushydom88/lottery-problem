:-use_module(library(clpfd) ).
:-use_module(library(lists)).
:-use_module(library(ordsets)).
:-use_module(library(ugraphs)).
:-use_module(library(between)).

% Note this code runs on SICSTUS Prolog

% Example commands to build code and compute lottery numbers:
% ['lotteryPaperNew.pl'].
% lottery_numbers_in_range(30,70).

% Example from paper:
% lottery_numbers_in_range( 69, 71).

% Command to produce the exceptions for showing L(71,6,6,2) = 38
% possible_lottery_number( 71, 35, 38 ).

%%% COMPUTE LOTTERY NUMBERS IN A RANGE %%%
% Given Nmin and Nmax try to compute L(n,6,6,2) for Nmin <= n <= Nmax.
% The value of L(n,6,6,2) is passed in to the computation of L(n+1,6,6,2)
lottery_numbers_in_range( Nmin, Nmax ) :-
    PrevLottoNum #= 1,
    lottery_numbers_in_range2( PrevLottoNum, Nmin, Nmax ).
lottery_numbers_in_range2( PrevLottoNum, N, Nmax ) :-
    ( N = Nmax -> possible_lottery_number( N, PrevLottoNum, _ );
                  possible_lottery_number( N, PrevLottoNum, NewLottoNum ),
                  NewN #= N + 1,
                  lottery_numbers_in_range2( NewLottoNum, NewN, Nmax )
    ).
%%%%%%

%%% POSSIBLE LOTTERY NUMBER %%%
possible_lottery_number( N, PrevLottoNum, UB ) :-
    % first calculate the upper bound
    upper_bound( N, PrevLottoNum, UB ),
    ( PrevLottoNum = UB -> print_message(informational, format(' L(~w,6,6,2) = ~w ',[N,UB]) );
                           PrevLottoNum #\= UB,
                           % Calculate an upper bound on d1
                           bound_isolated_blocks_and_num_shans( N, UB, RSPairs ),
                           get_min_num_Iblocks( N, MinNumIBlocks ),
                           % get Delta(I) exceptions
                           maplist( get_deltaI_exceptions(N, UB, MinNumIBlocks), RSPairs, DeltaExceptionsList ),
                           append( DeltaExceptionsList, DeltaExceptions),
                           % get bad RS Tuples
                           get_bad_RS_tuples(N, UB, RSPairs, BadRSTuples1 ),
                           exclude( partially_fill_bad_r_s_tuple(N, UB), BadRSTuples1, BadRSTuples ),
                           % Output to temrinal
                           write_lotto_result( BadRSTuples, DeltaExceptions, N, UB )
    ).
%%%%%%

%%% NUM ISOLATED BLOCKS AND SHANONS BOUND %%%
bound_isolated_blocks_and_num_shans( N, UB, RSPairs ) :-
    T #= 2*N - 6*(UB - 1),
    ( T =< 0 -> RMin #= 0; RMin #= T ),
    findall( [R,S], ( domain( [R,S], 0, 5 ), R #>= RMin, R + S #=< 5, labeling([], [R,S]) ),  PossRSPairs ),
    include( num_isolated_blocks_and_shans_helper(N, UB), PossRSPairs, RSPairs ).
num_isolated_blocks_and_shans_helper(N, UB, [R,S] ) :-
    M #= N - 6*R - 9*S,
    P #= 6 - R - S,
    LB #= UB - R - 3*S - 1,
    furedi_lower_bound( Vs, M, 6, P, LB ),
    labeling([], Vs).
%%%%%%


%%% COVERING DESIGN UPPER BOUND %%%
% Start with a guess for the upper bound and increase the guess until a solution is found
upper_bound( N, Guess, UB ) :-
    findall( Vs, ( test_upper_bound( Vs, N, Guess ), labeling([], Vs)),  Sols ),
    length(Sols, KK),
    (KK = 0 ->  Guess2 #= Guess + 1,
                upper_bound( N, Guess2, UB ) ; 
                UB #= Guess
    ).
test_upper_bound( Vs, N, UB ) :- 
    length( Vs, 5 ),
    domain( Vs, 6, 70 ),
    sum( Vs, #=, N ),
    get_covering_design_nums( Vs, Scores ),
    sum( Scores, #=<, UB ),
    sorting(Vs,[1,2,3,4,5],Vs).
get_covering_design_nums( Vs, Scores ) :-
    Vals = [0,0,0,0,0,1,3,3,3,4,
            6,6,7,7,10,10,12,12,15,16,
            17,19,21,22,23,24,27,28,30,31,
            31,38,39,40,42,47,50,51,54,55,
            59,63,65,67,70,73,79,80,82,87,
            90,96,98,99,105,110,114,117,119,128,
            132,135,140,142,143,143,157,160,163,172],
    maplist( get_covering_design_num(Vals), Vs, Scores ).
get_covering_design_num(Vals, I, Score ) :-
    nth1( I, Vals, Score ).
%%%%%%

%%% FUREDI LOWER BOUND %%%
furedi_lower_bound(Vs, N, K, P, LB ) :-
    LLB is K * LB,
    NP is P - 1,
    length( Vs, NP ),
    domain( Vs, 1, N ),
    sum( Vs, #=, N ),
    maplist( furedi_lower_bound_helper(K), Vs, Ws ),
    sum( Ws, #=<, LLB  ).
furedi_lower_bound_helper( K, X, Y ) :- 
    ((X -1 ) mod (K - 1 )  ) #= 0,
    Y #= X * ( (X-1) / (K - 1 ) ).
furedi_lower_bound_helper( K, X, Y ) :- 
    ((X -1 ) mod (K - 1 )  ) #\= 0,
    Y #= X * ( 1 + ( (X-1) / ( K - 1 ) ) ).
%%%%%%

%%% BAD RS TUPLES %%%
get_bad_RS_tuples(N, UB, RSPairs, BadRSTuples ) :-
    maplist( check_RS_tuple(N, UB), RSPairs, BadRSTuples0 ),
    include( non_empty, BadRSTuples0, BadRSTuples).
check_RS_tuple(N, UB, [R, S], BadRSTuple ):-
    get_delta_two( N, UB, R, S, D2 ),
    Num2s #= D2 + S,
    MaxNum2s #= 4 - R,
    ( Num2s >= MaxNum2s ->  BadRSTuple = []; 
        SpacesLeft #= 5 - R - Num2s,
        row_of_n_ms( Num2s, 2, FirstDelta ),
        DeltaLength #= 5 - R,
        extend_deltas_to_fixed_length( DeltaLength, N, UB, R, S, [FirstDelta], Deltas ),
        length( Deltas, NumDeltas ),
        TargetNumDeltas #= SpacesLeft + 1,
        ( NumDeltas = TargetNumDeltas -> BadRSTuple = [];
                                        D2Upper #= 9*S + 8*(MaxNum2s - S ),
                                        D2Lower0 #= (3*N - 12 * R - 6 * (UB - 1) ),
                                        ( D2Lower0 < 9*S -> D2Lower #= 9*S; D2Lower #= D2Lower0 ),
                                        BadRSTuple = [R,S,D2Lower,D2Upper]
        )
    ).

extend_deltas_to_fixed_length( DeltaLength, N, UB, R, S, Deltas, ExtendedDeltas ) :-
    nth1( 1, Deltas, FirstDelta ),
    length( FirstDelta, CurrentDeltaLength),
    ( CurrentDeltaLength = DeltaLength -> ExtendedDeltas = Deltas;
      include( can_extend_delta(N, UB, R, S), Deltas, Deltas2 ),
      ( Deltas2 = [] -> ExtendedDeltas = [];
      extend_deltas( Deltas2, Deltas3),
      extend_deltas_to_fixed_length( DeltaLength, N, UB, R, S, Deltas3, ExtendedDeltas ) 
      )
     ).

can_extend_delta( N, UB, R, S, Delta ) :-
    delete( Delta, 3, Residue),
    length( Residue, NumTwos ),
    length( Delta, DeltaLength ),
    NumThrees #= DeltaLength - NumTwos, 
    NumNonShanTwos #= NumTwos - S,
    D2Upper #= 9*S + 8*NumNonShanTwos,
    Used #= 6*R + 2*D2Upper + 3*( N - 6*R - D2Upper ),
    Left #= 6*(UB - 1) - Used,
    Min2sAnd3s #= N - 6*R - Left,
    NumSpaces #= 9*S + 11*NumNonShanTwos + 16*NumThrees,
    Min2sAnd3s #>= NumSpaces.

extend_deltas( Deltas, Deltas2) :-
    maplist( extend_delta, Deltas, DeltasList ),
    append(DeltasList, Deltas2).

extend_delta( Delta, DeltasList ) :-
    length( Delta, DeltaLength),
    ( DeltaLength = 0 -> DeltasList = [[2], [3]];
    nth1( DeltaLength, Delta, Last ),
    ( Last = 2 -> append([Delta, [2]], NewDelta1 ),
                  append([Delta, [3]], NewDelta2 ),
                  DeltasList = [NewDelta1, NewDelta2];
                  append([Delta, [3]], NewDelta ),
                  DeltasList = [NewDelta]
    )
    ).


partially_fill_bad_r_s_tuple( N, UB, [R,S,_,_] ) :-
    % These D2 estimates do not include the ones inside Shanon graphs
    PossD2Lower #= (3*N - 12 * R - 6 * (UB - 1) - 9*S  ),
    make_non_negative(PossD2Lower, D2Lower),
    D2Upper #= 8*( 4 - R - S ),
    numlist( D2Lower, D2Upper, D2s),
    maplist( partially_fill_bad_r_s_tuple2( N, UB, R, S), D2s ).


partially_fill_bad_r_s_tuple2( N, UB, R, S, D2 ) :-
    Y #= (D2 mod 8),
    (Y = 0 ->  PossExtraI2s #= D2 / 8 ; PossExtraI2s #= 1 + (D2 / 8)),
    make_non_negative(PossExtraI2s, ExtraI2s),
    I2s #= ExtraI2s + S,
    row_of_n_ms( I2s, 2, FirstDelta ),
    DeltaLength #= 4 - R ,
    extend_deltas_to_fixed_length( DeltaLength, N, UB, R, S, [FirstDelta], Deltas ), %these deltas contain the shannons
    maplist( partially_fill_bad_r_s_tuple3( N, UB, R, S, D2), Deltas).

partially_fill_bad_r_s_tuple3( N, UB, R, S, D2, Delta) :-
    delete( Delta, 3, Residue),
    length( Residue, I2s ),
    ( D2 < (I2s - S) -> true;
    length( Delta, DeltaLength ),
    I3s #= DeltaLength - I2s,
    Used #= 6*R + 2*(D2 + 9*S) + 3*( N - 6*R - D2 - 9*S ),
    Left #= 6*(UB-1) - Used,
    PossD3Upper #= 10*(I2s - S) + 16*I3s - D2,
    make_non_negative(PossD3Upper, D3Upper),
    PossD3Lower #= N - 6*R - D2 - 9*S - Left,
    make_non_negative(PossD3Lower, D3Lower),
    (   D3Lower #=< D3Upper -> numlist( D3Lower, D3Upper, D3s),
        maplist( partially_fill_bad_r_s_tuple4( N, UB, R, S, Delta, D2), D3s)
        ; true )
    ).


partially_fill_bad_r_s_tuple4( N, UB, R, S, DeltaWithShans, D2, D3) :-
    ( ( 6*(UB-1) - 6*R - 2*(D2 + 9*S ) - 3*D3 ) < 4*( N - 6*R - D2 - 9*S - D3 ) -> true;
    row_of_n_ms( S, 2, DeltaShans ),
    append( [DeltaShans, Delta], DeltaWithShans ),
    delete( Delta, 3, Residue),
    length( Residue, I2s ),
    length( Delta, DeltaLength ),
    I3s #= DeltaLength - I2s,
    ( D3 < I3s -> true;
    NumSpaces #= 10*I2s + 15*I3s,
    Toes #= 2*( D2 + D3 - I2s - I3s ) - NumSpaces,
    Toes #>= 0,
    Excess #= D3 - I3s,
    findall( Vs, (populate_toes_in_Iblocks( Delta, Toes, Excess, Vs ), labeling([], Vs) ), Sols ),
    length( Sols, KK ),
    ( KK = 0 -> true;
        exclude(toe_sol_is_tight( N, UB, D2, D3, R, S, Delta, I2s, I3s, Toes ), Sols, NonTightSols),
        (
            length(NonTightSols, NumNonTightSols),
            NumNonTightSols = 0 ->  D4 #= N - 6*R - 9*S - D2 - D3, 
            (D4 > 21 -> true; false);
            false
        )
    )
    )
    ).

toe_sol_is_tight( N, UB, D2, D3, R, S, Delta, I2s, I3s, Toes, Sol ) :- % For now only consider Deltas consisting of all 2s
    I3s #= 0, 
    %maplist( at_least_six, Sol ),
    ( 6*(UB-1) - 6*R - 2*(D2 + 9*S ) - 3*D3 ) #= 4*( N - 6*R - D2 - 9*S - D3 ),
    sum(Sol, #=, Toes),
    maplist( get_ex, Sol, Delta, Excesses ),
    sum(Excesses, #=, Excess),
    ExtraExcess #= D3 - Excess, 
    numlist( 0, ExtraExcess, Es),
    maplist( toe_sol_is_tight2(D2, D3, I2s, Toes, Excess), Es).

toe_sol_is_tight2( D2, D3, I2s, Toes, Excess, E ) :-
    MaxNumD2Toes #= Toes - Excess - E,
    RemainingD2s #= D2 - I2s - MaxNumD2Toes,
    RemainingSpaces #= 10*I2s - Toes - 2*RemainingD2s,
    ( RemainingSpaces =< 0 -> true;
        (
            D3sLeftToPlace #= D3 - Excess - E,
            D3Spill #= 2*D3sLeftToPlace - RemainingSpaces,
            (
                D3Spill < 0 -> false;
                true
            )
        )
    ).

at_least_six(X) :- X #>= 6.

make_non_negative(X, Y) :-
    X #< 0,
    Y #= 0.
make_non_negative(X, Y) :-
    X #>= 0,
    Y #= X.
%%%%%%

%%% DELTA(I) EXCEPTIONS %%%
% Lower bound the number of blocks in B_I
get_min_num_Iblocks( N, Min) :-
    M #= ( ( N - 5 ) mod 5 ),
    ( M = 0 -> Min #= (N - 5)/5; Min #= 1 + ((N - 5)/5) ).


% Find the values of Delta(I) we cannot immediately rule out
get_deltaI_exceptions( N, UB, MinNumIBlocks, [R, S], DeltaExceptions ) :-
    % Lower bound how many 2s are assumed to be in Delta(I)
    get_delta_two( N, UB, R, S, Delta2 ),
    K2 #= 5 - R - S - Delta2, % have a look at K2 not strictly positive
    row_of_n_ms( Delta2, 2, L2 ),
    findall( Xs, ( length(Xs, 2), domain(Xs, 0, K2), sum(Xs, #=, K2), labeling([], Xs) ), VSizes ),
    maplist( make_delta_end, VSizes, DeltaEnds ),
    maplist( append(L2), DeltaEnds, Deltas1 ),
    % Remove out Delta(I) where |B_I| is too small 
    include( at_least_m_blocks(MinNumIBlocks, R, S), Deltas1, Deltas2 ),
    % Upper bound the excess of the whole design
    % For each possible Delta(I) consider the constraint problem of populating toes in the IBlocks 
    convlist( can_populate_toes_in_Iblocks(N, UB, R, S), Deltas2, DeltasAndBounds ),
    maplist( fill_delta(R, S), DeltasAndBounds, DeltaExceptions ).

can_populate_toes_in_Iblocks(N, UB, R, S, DeltaTail, [DeltaTail, D2L, D2U]) :-
    get_excess( N, R, UB, Excess ),
    sum(DeltaTail, #=, B),
    MinToes #= 2*N - 10 - 5*(B + 2*S + 2*R) - 6*S,
    delete( DeltaTail, 3, Residue),
    length( Residue, NumTwos ),
    NumThrees #= 5 - NumTwos - S - R,
    FootExcess #= Excess - NumThrees,
    findall( Vs, (populate_toes_in_Iblocks( DeltaTail, MinToes, FootExcess, Vs ), labeling([], Vs)), Sols1),
    OverD3Excess #= 6*(UB-1) - 3*N + 9*S + 8* NumTwos + 12*R,
    include( d3_excess_check(OverD3Excess), Sols1, Sols2 ),
    convlist( twos_lie_with_twos(  N, UB, R, S, DeltaTail, FootExcess ), Sols2, SolsAndBounds0 ),
    include( changing_socks( N, UB, R, MinToes ), SolsAndBounds0, SolsAndBounds ),
    length(SolsAndBounds, LL),
    LL #> 0,
    maplist(grab_second_and_third, SolsAndBounds, D2Ls, D2Us ),
    list_to_ord_set( D2Ls, D2LsUniques ),
    list_to_ord_set( D2Us, D2UsUniques ),
    length(D2UsUniques, KK),
    nth1( 1, D2LsUniques, D2L),
    nth1( KK, D2UsUniques, D2U).

changing_socks( N, UB, R, MinToes, [Sol, _, D2U] ) :-
    OverD3Excess #= 6*(UB-1) - 6*R - 2*D2U - 3*( N - 6*R - D2U ),
    delete( Sol, 12, Residue),
    length( Residue, NumNonTwelves ),
    length( Sol, LengthSol ),
    NumTwelves #= LengthSol - NumNonTwelves,
    sum( Sol, #=, SumSol ),
    ExcessToes #= SumSol - MinToes, 
    SocksToChanges #= ExcessToes + 1,
    CanChange #= OverD3Excess/3,
    SocksToChanges #> NumTwelves - CanChange.



d3_excess_check( OverD3Excess, Vs ) :-
    maplist( d3_excess_score, Vs, Scores ),
    sum( Scores, #=<, OverD3Excess ).
d3_excess_score(V,S) :- element( V, [0,0,0,0,0,0,0,0,0,0,0,0,7,11,12], S ).

grab_second_and_third( [_, Y, Z], Y, Z ).

populate_toes_in_Iblocks( DeltaNoOnes, MinToes, Excess, Vs ) :-
    same_length( Vs, DeltaNoOnes, N ),
    domain( Vs, 1, 15 ),
    maplist( adjust_domain, DeltaNoOnes, Vs ), 
    maplist( get_ex, Vs, DeltaNoOnes, Excesses ),
    sum(Excesses, #=<, Excess ),
    sum(Vs, #>=, MinToes ),
    numlist(N,L),
    sorting(Vs,L,Vs).
adjust_domain( D, V ) :- ( D = 2 -> V #=< 10; D #= 3 ).
get_ex( V, D, Ex ) :-
    ( D = 2 -> element( V, [0,0,0,0,0,0,2,3,7,10], Ex ); element( V, [1,2,3,4,5,6,7,8,9,10,11,12,20,25,27], Ex )).
non_empty(L) :- length(L,K), K#>0.

fill_delta(R, S, [Delta, D2L, D2U], [R, S, D2L, D2U, PaddedDelta] ) :-
    row_of_n_ms( R, 1, X1 ),
    row_of_n_ms( S, 2, X2 ),
    append( [X1, X2, Delta], PaddedDelta).

% gives how many elements of delta(I) can be assumed to be 2, in addition to 2s from Shannon hypergraphs
get_delta_two( N, UB, R, S, Delta2 ) :-
    %get_delta_two2( N, UB, R, S, PossDelta2 ),
    X #= (3*N - 12 * R - 6 * (UB - 1) - 9*S  ),
    Y #= (X mod 8),
    (Y = 0 ->  PossDelta2 #= X / 8 ; PossDelta2 #= 1 + (X / 8)),
    make_non_negative(PossDelta2, Delta2).

row_of_n_ms( N, M, Row ) :-
    length( Row, N ),
    maplist( #=(M), Row ).
make_delta_end( [A,B], DeltaEnd ) :-
    row_of_n_ms( A, 2, X1 ),
    row_of_n_ms( B, 3, X2 ),
    append(X1, X2, DeltaEnd).

at_least_m_blocks(MinNumIBlocks, R, S, PossDelta ) :-
    sum(PossDelta, #=, Tot),
    Tot + R + 2*S #>= MinNumIBlocks.

at_least_m_blocks( MinNumIBlocks, PossDelta ) :-
    sum(PossDelta, #>=, MinNumIBlocks).

get_excess( N, R, UB, Excess ) :-
    Excess #= 6*(UB-1) + 6*R - 2*N. 


twos_lie_with_twos(  N, UB, R, S, Delta, FootExcess, Sol, [Sol, D2L, D2U] ) :-
    maplist( get_ex, Sol, Delta, SolExcesses ),
    sum(SolExcesses, #=, SolExcess ),
    ExtraExcess #= FootExcess - SolExcess,
    delete( Delta, 3, Residue),
    length( Residue, I2s ),
    I3s #= 5 - R - S - I2s,
    PossD2Lower #= (3*N - 12 * R - 6 * (UB - 1) - 9*S  ),
    make_non_negative( PossD2Lower, D2Lower),
    D2Upper #= 8*I2s,
    ( I2s = 0 -> D2L #=  D2Upper + 9*S, D2U #=  D2Lower + 9*S ; (I3s = 0 -> D2L #=  D2Upper + 9*S, D2U #=  D2Lower + 9*S ; 
    length( Sol2, I2s ),
    append( [Sol2, Sol3], Sol ),
    list_to_ord_set( Sol2, Sol2Uniques ),
    list_to_ord_set( Sol3, Sol3Uniques ),
    findall( [X,Y], (domain([X,Y], 0, 15 ), member(X, Sol2Uniques ), member(Y, Sol3Uniques ), X #\= 10, labeling([], [X,Y]) ), TwoThreePairs ),
    ( TwoThreePairs = [] ->  ( D2Lower > I2s -> false;  D2L #=  D2Upper + 9*S, D2U #=  D2Lower + 9*S  );
    maplist( min_excess_for_two_three_split, TwoThreePairs, TwoThreeSplitExcesses ),
    list_to_ord_set( TwoThreeSplitExcesses, TwoThreeSplitExcessesUniques ),
    nth1(1,TwoThreeSplitExcessesUniques,MinExcessForSplit),
    sum( Sol2, #=, Sol2Sum ),
    maplist( get_ex, Sol2, Residue, Excesses ),
    sum(Excesses, #=, Excess ),
    Max2Toes #= Sol2Sum - Excess,
    numlist( 0, ExtraExcess, Es ),
    numlist( D2Lower, D2Upper, D2s ),
    ( ExtraExcess > D2Upper -> M #= ExtraExcess; M #= D2Upper ),
    findall( [X,Y], (domain([X,Y], 0, M ), member(X, D2s ), member(Y, Es ), labeling([], [X,Y]) ), D2andExtraExcessPairs ),
    EmptySpaces #= 10*I2s - Sol2Sum,
    include( check_d2_and_extra_excess_pair( I2s, EmptySpaces, Max2Toes, MinExcessForSplit ), D2andExtraExcessPairs, D2andExtraExcessPairs1 ),
    ( D2andExtraExcessPairs1 = [] -> false;
     maplist( grab_first, D2andExtraExcessPairs1, RemainingD2s),
    list_to_ord_set( RemainingD2s, RemainingD2sUniques ),
    length(RemainingD2sUniques, KK),
    nth1( 1, RemainingD2sUniques, D2L),
    nth1( KK, RemainingD2sUniques, D2U)
     )
    )
        ) ).

grab_first( [X | _], X ).
at_least_five(X) :- X #>= 5.

check_d2_and_extra_excess_pair( I2s, EmptySpaces, Max2Toes, MinExcessForSplit, [D2, E] ) :-
    D2Left #= D2 - I2s - ( Max2Toes - E ),
    D2Left #>= 0,
    D2Left #=< EmptySpaces, 
    PossMinSplitD2s #= 2*D2Left - EmptySpaces, 
    make_non_negative( PossMinSplitD2s, MinSplitD2s),
    ( MinSplitD2s > 0 -> E #>= MinExcessForSplit; true ).

min_excess_for_two_three_split( [5,11], 2 ).
min_excess_for_two_three_split( [5,12], 2 ).
min_excess_for_two_three_split( [5,13], 2 ).
min_excess_for_two_three_split( [5,14], 2 ).
min_excess_for_two_three_split( [6,9], 2 ).
min_excess_for_two_three_split( [6,10], 2 ).
min_excess_for_two_three_split( [6,11], 3 ).
min_excess_for_two_three_split( [6,12], 4 ).
min_excess_for_two_three_split( [6,13], 4 ).
min_excess_for_two_three_split( [6,14], 4 ).
min_excess_for_two_three_split( [6,15], 6 ).
min_excess_for_two_three_split( [7,9], 1 ).
min_excess_for_two_three_split( [7,10], 1 ).
min_excess_for_two_three_split( [7,11], 2 ).
min_excess_for_two_three_split( [7,12], 3 ).
min_excess_for_two_three_split( [7,13], 4 ).
min_excess_for_two_three_split( [7,14], 4 ).
min_excess_for_two_three_split( [8,8], 1 ).
min_excess_for_two_three_split( [8,9], 1 ).
min_excess_for_two_three_split( [8,10], 1 ).
min_excess_for_two_three_split( [8,11], 2 ).
min_excess_for_two_three_split( [8,12], 5 ).
min_excess_for_two_three_split( [8,13], 5 ).
min_excess_for_two_three_split( [8,14], 5 ).
min_excess_for_two_three_split( [9,9], 0 ).
min_excess_for_two_three_split( [9,10], 0 ).
min_excess_for_two_three_split( [9,11], 5 ).
min_excess_for_two_three_split( [9,12], 5 ).
min_excess_for_two_three_split( [9,13], 5 ).
min_excess_for_two_three_split( [9,14], 5 ).
min_excess_for_two_three_split( [9,15], 5 ).

%%%%%%

%%% RESULT OUTPUT %%%
write_lotto_result( [], [], N, UB ) :-
    print_message(informational, format(' L(~w,6,6,2) = ~w ',[N,UB]) ).
write_lotto_result( BadRSTuples, DeltaExceptions, N, UB ) :-
    append( BadRSTuples, DeltaExceptions, TotalExceptions ),
    length(TotalExceptions, Ex),
    ( Ex = 0 -> print_message(informational, format(' L(~w,6,6,2) = ~w ',[N,UB]) );
                print_message(informational, format('Conjecture that  L(~w,6,6,2) = ~w.',[N,UB]) ),
                write_bad_r_s_tuples( BadRSTuples ),
                write_delta_exceptions( DeltaExceptions )
    ).

write_bad_r_s_tuples(BadRSTuples) :-
    ( BadRSTuples = [] -> true;
    print_message(informational, format('BadRSTuples [R,S,A,B]:',[]) ),
    maplist( write_bad_r_s_tuple, BadRSTuples )
    ).
write_bad_r_s_tuple( [R, S, A, B] ) :-
    print_message(informational, format('[~w,~w,~w,~w]',[R, S, A, B]) ).

write_delta_exceptions(DeltaExceptions) :-
    ( DeltaExceptions = [] -> true;
    print_message(informational, format('Delta(I) exceptions [R,S,D2U,D2L,Delta]:',[]) ),
    maplist( write_delta_exception, DeltaExceptions )
    ).
write_delta_exception( [R, S, D2U, D2L, Delta] ) :-
    print_message(informational, format('[~w,~w,~w,~w,~w]',[R, S, D2U, D2L, Delta]) ).
    



writeln( Stream ) :-
        write( Stream ),
        write('\n').
%%%%%%
