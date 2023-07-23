:-use_module(library(clpfd) ).
:-use_module(library(lists)).
:-use_module(library(ordsets)).
:-use_module(library(ugraphs)).
:-use_module(library(between)).

% ['lottery.pl'].

% compute_lottery_numbers_in_range(30,61).

%%% COMPUTE LOTTERY NUMBERS IN A RANGE %%%
% Given Nmin and Nmax try to compute L(n,6,6,2) for Nmin <= n <= Nmax.
% The value of L(n,6,6,2) is passed in to the computation of L(n+1,6,6,2)
compute_lottery_numbers_in_range( Nmin, Nmax ) :-
    PrevLottoNum #= 1,
    compute_lottery_numbers_in_range2( PrevLottoNum, Nmin, Nmax ).
compute_lottery_numbers_in_range2( PrevLottoNum, N, Nmax ) :-
    N #= Nmax,
    possible_lottery_number( N, PrevLottoNum, _ ).
compute_lottery_numbers_in_range2( PrevLottoNum, N, Nmax ) :-
    N #\= Nmax,
    possible_lottery_number( N, PrevLottoNum, NewLottoNum ),
    NewN #= N + 1,
    compute_lottery_numbers_in_range2( NewLottoNum, NewN, Nmax ).
%%%%%%

%%% POSSIBLE LOTTERY NUMBER %%%
possible_lottery_number( N, PrevLottoNum, UB ) :-
    % first calculate the upper bound
    upper_bound( N, PrevLottoNum, UB ),
    possible_lottery_number2( N, PrevLottoNum, UB ).
possible_lottery_number2( N, PrevLottoNum, UB ) :-
    PrevLottoNum #= UB,
    print_message(informational, format(' L(~w,6,6,2) = ~w ',[N,UB]) ).
possible_lottery_number2( N, PrevLottoNum, UB ) :-
    PrevLottoNum #\= UB,
    % Calculate an upper bound on d1
    bound_isolated_blocks( N, UB, Rs ),
    get_min_num_Iblocks( N, MinNumIBlocks ),
    % get any exceptions for constructing a slim I
    maplist( get_slim_I_exceptions(N, UB), Rs, PossSlimIExceptions ),
    include( interval_check, PossSlimIExceptions, SlimIExceptions1 ),
    % get Delta(I) exceptions
    maplist( get_deltaI_exceptions(N, UB, MinNumIBlocks), Rs, DeltaExceptionsList ),
    append( DeltaExceptionsList, DeltaExceptions),
    write_lotto_result( SlimIExceptions1, DeltaExceptions, N, UB ).
%%%%%%

%%% D1 UPPER BOUND %%%
bound_isolated_blocks( N, UB, PossD1s ) :-
    get_r_min( N, UB, D1Min ),
    include( bound_isolated_blocks_helper(N, UB, D1Min), [0,1,2,3,4], PossD1s ).
bound_isolated_blocks_helper(_, _, D1Min, 0) :-
    D1Min #< 1.
bound_isolated_blocks_helper(N, UB, D1Min, R) :-
    R #> 0,
    D1Min #=< 6*R,
    P #= 6 - R,
    LB #= UB - R,
    M #= N - 6 * R,
    furedi_lower_bound( Vs, M, 6, P, LB ),
    labeling([], Vs).
get_r_min( N, UB, D1Min ) :-
    T #= 2*N - 6*(UB - 1),
    T #=< 0,
    D1Min #= 0.
get_r_min( N, UB, D1Min ) :-
    T #= 2*N - 6*(UB - 1),
    T #> 0,
    D1Min #= T.
%%%%%%

%%% COVERING DESIGN UPPER BOUND %%%
% Start with a guess for the upper bound and increase the guess until a solution is found
upper_bound( N, Guess, UB ) :-
    findall( Vs, ( test_upper_bound( Vs, N, Guess ), labeling([], Vs)),  Sols ),
    upper_bound2( N, Guess, Sols, UB ).
upper_bound2( N, Guess, [], UB ) :-
    Guess2 #= Guess + 1,
    upper_bound( N, Guess2, UB ).
upper_bound2( _, Guess, Sols, UB ) :-
    length(Sols, KK),
    KK #>= 1, 
    UB #= Guess.

test_upper_bound( Vs, N, UB ) :- 
    length( Vs, 5 ),
    domain( Vs, 1, 65 ),
    M is N - 25,
    sum( Vs, #=, M ),
    get_covering_design_nums( Vs, Scores ),
    sum( Scores, #=<, UB ),
    sorting(Vs,[1,2,3,4,5],Vs).

get_covering_design_nums( Vs, Scores ) :-
    Vals = [1,3,3,3,4,
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
furedi_lower_bound_helper( K,  X, Y ) :- 
    ((X -1 ) mod (K - 1 )  ) #= 0,
    Y #= X * ( (X-1) / (K - 1 ) ).
furedi_lower_bound_helper( K, X, Y ) :- 
    ((X -1 ) mod (K - 1 )  ) #\= 0,
    Y #= X * ( 1 + ( (X-1) / ( K - 1 ) ) ).
%%%%%%

%%% SLIM I EXCEPTIONS
get_slim_I_exceptions( N, UB, R, [R, [D2Lower, D2Upper] ] ) :-
    D2Upper #= 9 * (4 - R),
    D2Lower0 #= ( 9*( 4*N - 6*(UB-1) - 18*R - 16*(4-R) )) / 4,
    make_non_negative(D2Lower0,D2Lower).
interval_check([_, [A,B] ]) :- A #=< B.
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
    ( ( N - 5 ) mod 5 ) #= 0,
    Min #= (N - 5)/5.
get_min_num_Iblocks( N, Min ) :-
    ( ( N - 5 ) mod 5 ) #\= 0,
    Min #= 1 + ((N - 5)/5).

% Find the values of Delta(I) we cannot immediately rule out
get_deltaI_exceptions( N, UB, MinNumIBlocks, R, Deltas ) :-
    % Lower bound how many 2s are assumed to be in Delta(I)
    get_delta_two( N, UB, R, Delta2 ),
    % Fill Delta(I) with as many 1s and 2s that can be assumed
    % Then generate all ways to complete Delta(I) by adding 2s and 3s
    row_of_n_ms( R, 1, L1 ),
    row_of_n_ms( Delta2, 2, L2 ),
    append( L1, L2, L3 ),
    length( L3, K1),
    K2 #= 5 - K1,
    findall( Xs, ( length(Xs, 2), domain(Xs, 0, K2), sum(Xs, #=, K2), labeling([], Xs) ), VSizes ),
    maplist( make_delta_end, VSizes, DeltaEnds ),
    maplist( append(L3), DeltaEnds, Deltas1 ),
    % Remove out Delta(I) where |B_I| is too small 
    include( at_least_m_blocks(MinNumIBlocks), Deltas1, Deltas2 ),
    % Upper bound the excess of the whole design
    get_base_excess( N, R, UB, BaseExcess ),
    % For each possible Delta(I) consider the constraint problem of populating toes in the IBlocks 
    include( can_populate_toes_in_Iblocks(N, R, BaseExcess), Deltas2, Deltas ).

get_delta_two( N, UB, R, Delta2 ) :-
    get_delta_two2( N, UB, R, PossDelta2 ),
    make_non_negative(PossDelta2, Delta2).
get_delta_two2( N, UB, R, Delta2 ) :-
    X #= (3*N - 12 * R - 6 * (UB - 1) ),
    (X mod 9) #= 0,
    Delta2 #= X / 9.
get_delta_two2( N, UB, R, Delta2 ) :-
    X #= (3*N - 12 * R - 6 * (UB - 1) ),
    (X mod 9) #\= 0,
    Delta2 #= 1 + (X / 9).
row_of_n_ms( N, M, Row ) :-
    length( Row, N ),
    maplist( #=(M), Row ).
make_delta_end( [A,B], DeltaEnd ) :-
    row_of_n_ms( A, 2, X1 ),
    row_of_n_ms( B, 3, X2 ),
    append(X1, X2, DeltaEnd).

at_least_m_blocks( MinNumIBlocks, PossDelta ) :-
    sum(PossDelta, #>=, MinNumIBlocks).

get_base_excess( N, R, UB, BaseExcess ) :-
    BaseExcess #= 6*(UB-1) + 6*R - 2*N. 

can_populate_toes_in_Iblocks(N, R, BaseExcess, Delta) :-
    sum(Delta, #=, B),
    MinToes #= 2*N - 10 - 5*(B+R),
    delete( Delta, 3, Residue),
    length( Residue, NumOnesAndTwos ),
    NumThrees #= 5 - NumOnesAndTwos,
    Excess #= BaseExcess - NumThrees,
    delete( Delta, 1, DeltaNoOnes),
    populate_toes_in_Iblocks( DeltaNoOnes, MinToes, Excess, Vs ), 
    labeling([], Vs).

populate_toes_in_Iblocks( DeltaNoOnes, MinToes, Excess, Vs ) :-
    same_length( Vs, DeltaNoOnes, N ),
    domain( Vs, 1, 15 ),
    maplist( adjust_domain, DeltaNoOnes, Vs ), 
    maplist( get_ex, Vs, DeltaNoOnes, Excesses ),
    sum(Excesses, #=<, Excess ),
    sum(Vs, #>=, MinToes ),
    numlist(N,L),
    sorting(Vs,L,Vs).
adjust_domain( 2, V ) :- V #=< 10.
adjust_domain( 3, _).
get_ex( V, 2, Ex ) :-
    element( V, [0,0,0,0,0,0,2,3,7,10], Ex ).
get_ex( V, 3, Ex ) :-
    element( V, [1,2,3,4,5,6,7,8,9,10,11,12,20,25,27], Ex ).
%%%%%%

%%% RESULT OUTPUT %%%
write_lotto_result( [], [], N, UB ) :-
    print_message(informational, format(' L(~w,6,6,2) = ~w ',[N,UB]) ).
write_lotto_result( SlimIExceptions, DeltaExceptions, N, UB ) :-
    append( SlimIExceptions, DeltaExceptions, TotalExceptions ),
    length(TotalExceptions, Ex),
    Ex #> 0,
    print_message(informational, format('We conjecture that  L(~w,6,6,2) = ~w and must rule out the following cases',[N,UB]) ),
    write_slimI_exceptions( SlimIExceptions ),
    write_delta_exceptions( DeltaExceptions ).

write_slimI_exceptions( Exceptions ) :-
    maplist( write_slimI_exception, Exceptions ).
write_slimI_exception( [R, [D2, D2] ] ) :-
    D1 #= 6*R,
    print_message(informational, format(' d_1 = ~w and d_2 = ~w ',[D1,D2]) ).
write_slimI_exception([R, [D2L, D2U] ] ) :-
    D1 #= 6*R,
    D2L #\= D2U,
    print_message(informational, format(' d_1 = ~w and d2 in the range [~w,~w] ',[D1,D2L, D2U]) ).

write_delta_exceptions( Exceptions ) :-
    maplist( write_delta_exception, Exceptions ).
write_delta_exception( Delta ) :-
    delete( Delta, 2, Residue),
    length( Residue, NumNoneTwos ),
    NumTwos #= 5 - NumNoneTwos,
    D2 #= NumTwos * 9,
    print_message(informational, format(' d_2 <= ~w and \\delta(I) = ~w ',[D2, Delta]) ).

writeln( Stream ) :-
        write( Stream ),
        write('\n').
%%%%%%