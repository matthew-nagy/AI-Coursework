% This is a helper predicate and should find all the links for a particular actor
% find_links_by_actor(+A,-L)
find_links_by_actor(A,L) :-
    wp(A, WikiDocument),
    findall(Link, wt_link(WikiDocument, Link), L).

%Base case, unify with accumulator
filter_actors([], _, Ans, Ans).
%Recursive case, either add the head to the accumulator or don't based on if they have the link
filter_actors([AH | AT], Link, Acc, Ans):-
    find_links_by_actor(AH, Links),
    (contains(Links, Link) ->
        NewAcc = [AH | Acc]
    ;
        NewAcc = Acc
    ),
    filter_actors(AT, Link, NewAcc, Ans).

%Use case, Given a list of actors and a link, filtered list will be the actors in actor list which have that link
filter_actors(ActorList, Link, FilteredList) :- filter_actors(ActorList, Link, [], FilteredList).

%Find a single adjacent charger
get_single_adjacent_charger(Pos, ChargerNum) :- map_adjacent(Pos, _, c(ChargerNum)).

%Follow the given path to a charger and recharge
path_to_charger(A, Path, OutEnergy):-
    agent_do_moves(A, Path),
    get_agent_position(A, CurrentPos),
    get_single_adjacent_charger(CurrentPos, X),
    agent_topup_energy(A, c(X)),
    ailp_grid_size(GS),
    OutEnergy is (GS * GS) / 4.


%Follow the given path to the given oracle. Then ask for its links, and "return" the new list of links and the energy there
path_to_oracle(A, Path, OracleNum, OutLink, OutEnergy):-
    agent_do_moves(A, Path),
    agent_ask_oracle(A, o(OracleNum), link, OutLink),
    get_agent_energy(A, OutEnergy).

%Find a new, nearby oracle which we have not quearied yet
find_queariable_oracle(CurrentEnergy, EAsk, AskedOracles, CurrentPos, OracleNum, PathResult):-
    Allowed_Energy is CurrentEnergy - EAsk, %The "Start energy" for this search should be the amount of energy the agent can actually spend moving
    find_astar(find(o(OracleNum)), AskedOracles, CurrentPos, Allowed_Energy, PathResult).

%Attempt to find a "secure" path to some new, nearby oracle. "secure" in this case means that when we arrive, we have enough energy to
%reach the next closest charger. Therefore, as it is assumed a recharge gives enough energy to reach any other charge station, this can be
%assumed to never be a fatal mistake  
attempt_secure_path_to_new_oracle(Agent, CurrentEnergy, EAsk, AskedOracles, OracleNum, PathToOracle, PathToCharger):-
    get_agent_position(Agent, CurrentPos),
    find_queariable_oracle(CurrentEnergy, EAsk, AskedOracles, CurrentPos, OracleNum, [PathToOracle, PathCost]),
    
    EnergyAfterOracle is CurrentEnergy - (PathCost + EAsk),
    (PathToOracle = [] ->
        get_agent_position(Agent, NextToOracle)
    ;
        last(PathToOracle, NextToOracle)
    ),
    find_astar(find(c(_)), [], NextToOracle, EnergyAfterOracle, [PathToCharger, LengthToCharger]),  %See if you can reach a charger from the next oracle

    %If we have found a path to both oracle and charger after that we can take...
    TotalEnergy is EnergyAfterOracle + LengthToCharger,
    TotalEnergy =< CurrentEnergy,
    !. %Greedily assume this is the correct path

%Fail case, there are no possible actors left. The actor is unknown
consider_next_move(_, _, _, _, _, [], unknown).
%Success case, there is only one actor left in the actor list. This is assumed to be the correct answer
consider_next_move(_, _, _, _, _, [SomeActor | []], SomeActor).
%Recursive case, unclear what the secret actor is, explore the oracles
consider_next_move(Agent, CurrentEnergy, EAsk, PathToCharger, AskedOracles, ActorList, SecretActor):-
    explore_oracles(Agent, CurrentEnergy, EAsk, PathToCharger, AskedOracles, ActorList, SecretActor).

%Assuming we are in a safe position, attempt to move to a new safe position. In this case, we succeed
explore_oracles(Agent, CurrentEnergy, EAsk, _, AskedOracles, ActorList, SecretActor):-
    %See if there is a "Secure" way of getting to an oracle while being able to go to a charger afterwards
    attempt_secure_path_to_new_oracle(Agent, CurrentEnergy, EAsk, AskedOracles, X, PathToOracle, NextPathToCharger),
    path_to_oracle(Agent, PathToOracle, X, OutLink, NextEnergy),
    NextAskedOracles = [o(X) | AskedOracles],
    filter_actors(ActorList, OutLink, FilteredList),
    %We have already moved, as we greedily assume this is optimum. Cut to prevent disasterous backtracking
    !,
    consider_next_move(Agent, NextEnergy, EAsk, NextPathToCharger, NextAskedOracles, FilteredList, SecretActor).

%In this case, we were unable to get a new secure path. Assuming we are in a safe position, move to the charger, then continue
explore_oracles(Agent, _, EAsk, [PHead | PTail], AskedOracles, ActorList, SecretActor):-
    path_to_charger(Agent, [PHead | PTail], NewEnergyHere),
    !, %Greedily assume this is optimal. You no longer have a route to a charger if you can't find a new oracle, otherwise it may
    %infinitely loop at this charger. So if the first case fails, you must now enter the later states
    explore_oracles(Agent, NewEnergyHere, EAsk, [], AskedOracles, ActorList, SecretActor).

%In this case, we just recharged, but can't find a safe oracle. So we must try to find one final unvisited oracle.
explore_oracles(Agent, CurrentEnergy, EAsk, [], AskedOracles, ActorList, SecretActor):-  
    get_agent_position(Agent, CurrentPos),
    find_queariable_oracle(CurrentEnergy, EAsk, AskedOracles, CurrentPos, X, [FinalPath, _]),
    path_to_oracle(Agent, FinalPath, X, OutLink, _),
    filter_actors(ActorList, OutLink, FilteredList),
    %We are done
    !,
    (FilteredList = [SomeActor | []] ->
        SecretActor = SomeActor
    ;
        SecretActor = unknown
    ).

%We can no longer find any oracles, safe or not. Therefore we set the answer to unknown or result
explore_oracles(_, _, _, [], _, [SecretActor | []], SecretActor):- !.
explore_oracles(_, _, _, [], _, _, unknown):- !.

find_identity(SecretIdentity):-
    my_agent(Agent),
    get_agent_energy(Agent, StartEnergy),
    ailp_grid_size(GSize),
    EAsk is (GSize * GSize) / 40,
    findall(A, actor(A), Actors),
    get_agent_position(Agent, Position),
    %Make sure it starts knowing how it could recharge
    find_astar(find(c(_)), [], Position, StartEnergy, [PathToCharger, _]),
    %Agent, with start Energy, energy to ask, no path, nor asked oracles, nor links currently
    explore_oracles(Agent, StartEnergy, EAsk, PathToCharger, [], Actors, SecretIdentity).