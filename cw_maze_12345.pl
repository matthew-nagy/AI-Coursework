hibernating.
exploring.
targeting.
going_to_finish.
finished.
no_move.
agentState(hibernating).
agentState(exploring).
agentState(targeting).
agentState(going_to_finish).
agentState(finished).


seeking.
known.
goalState(seeking).
goalState(known).

get_maze_heuristic(p(X, Y), Heuristic):-
    ailp_grid_size(GSize),
    XDif is GSize - X,
    YDif is GSize - Y,
    Heuristic is sqrt((XDif * XDif) + (YDif * YDif)).

%The adjacent point, and intersection path from 1
openPoint(p(_,_), _).

%Inserts a given node into a queue of nodes, ordered by their cost.
%Due to how the recursion works, the answer needs to reversed

finished_insert_point([], Acc, Ans):-reverse(Acc, Ans).
finished_insert_point([H | T], Acc, Ans):-
    finished_insert_point(T, [H | Acc], Ans).

w_insert_point([], openPoint(C, D), Acc, Ans) :- reverse([openPoint(C, D) | Acc], Ans).
w_insert_point([openPoint(A, B) | T], openPoint(C, D), Acc, Ans):-
    get_maze_heuristic(C, NewCost),
    get_maze_heuristic(A, HeadCost),

    NewCost < HeadCost,

    NewAcc = [openPoint(A, B) | [openPoint(C, D) | Acc]],
    finished_insert_point(T, NewAcc, Ans).
w_insert_point([openPoint(A, B)  | T], openPoint(C, D), Acc, Ans):-
    get_maze_heuristic(C, NewCost),
    get_maze_heuristic(A, HeadCost),
    NewCost >= HeadCost,
    w_insert_point(T, openPoint(C, D), [openPoint(A, B)  | Acc], Ans).


%Inserts nodes to the queue, ordering off cost 
insert_point([], openPoint(C, D), [openPoint(C, D)]).
insert_point([openPoint(A,B) | QueT], openPoint(C, D), Ans):- w_insert_point([openPoint(A, B) | QueT], openPoint(C, D), [], Ans).

insert_points(Ans, [], Ans).
insert_points(Acc, [openPoint(C,D) | T], Ans) :- 
    insert_point(Acc, openPoint(C,D), NAcc),
    insert_points(NAcc, T, Ans).

%Agent ID, its position, its intersection path, the path from the last intersection, the path its travelling
agentInfo(_, p(_, _), _, _, _).

%Representation of an agent
agent(agentState(_), agentInfo(_, _, _, _, _)).

%OpenPoint list, Intersections, intersection paths, goal state, numFinished, intersectionsToFinish
globalInfo(_, _, _, goalState(_), _, _).


%A move list looks like [ [From, To, Path] ]
%And assume if you are remembering that there will always be a path
remember_path([ [From, To, Path] | _ ], From, To, Path).
remember_path([ _ | T ], From, To, Path):-
    remember_path(T, From, To, Path).

remember_path([], _, _, _):-fail.

%Adds paths both ways from From and To with the known path
%The paths are backwards due to how we will stick them together
add_known_path(KnownPaths, From, To, Path, NextKnownPaths):-
    Path = [PH | _],
    (To == PH ->
        reverse(Path, FTPath),
        TFPath = Path
    ;
        FTPath = Path,
        reverse(Path, TFPath)
    ),
    FTPath = [_ | TowardsPath],
    TFPath = [_ | BackwardPath],
    
    NextKnownPaths = [[From, To, TowardsPath], [To, From, BackwardPath] | KnownPaths].


cut_off_after([Val | _], Val, Acc, Ans):-
    reverse([Val | Acc], Ans).
cut_off_after([H | T], Val, Acc, Ans):-
    cut_off_after(T, Val, [H | Acc], Ans).
cut_off_after(List, Val, Ans):-
    cut_off_after(List, Val, [], Ans).

stop_before([Val | _], Val, Ans, Ans).
stop_before([H | T], Val, Acc, Ans):-
    stop_before(T, Val, [H | Acc], Ans).
stop_before(List, Val, Ans):-
    stop_before(List, Val, [], Ans).

get_matching_point([Ans | _], List2, Ans):-
    contains(List2, Ans).
get_matching_point([_ | List1], List2, Ans):-
    get_matching_point(List1, List2, Ans).

get_intersect_path_to_goal(IntersectsToGoal, IntersectsToMe, Path):-
    get_matching_point(IntersectsToGoal, IntersectsToMe, P),
    cut_off_after(IntersectsToMe, P, Path1),
    stop_before(IntersectsToGoal, P, Path2),
    append(Path1, Path2, Path).


get_intersection_path(_, _, [], Ans, Ans).
get_intersection_path(KnownPaths, IntersectionAt, [HI | TI], Acc, Ans):-
    remember_path(KnownPaths, IntersectionAt, HI, PathPart),
    append(Acc, PathPart, NextAcc),
    get_intersection_path(KnownPaths, HI, TI, NextAcc, Ans).

%Given known paths, and two intersecting paths of intersections, find a path from where you are to the end of the other list
get_path_from_intersections(KnownPaths, IntersectsToGoal, MyIntersects, Path):-
    get_intersect_path_to_goal(IntersectsToGoal, MyIntersects, Intersections),
    Intersections = [IAt | IT],
    get_intersection_path(KnownPaths, IAt, IT, [], Path).
get_path_from_intersections(_, [Goal | _], [Position | _], Path):-
    find_astar(go(Goal), [], Position, 999, [Path, _]).

%manage_moving_agent_intersections(CurrentIntersections, NewPosition, KnownIntersections, NextCurrentIntersections)


remove_until([H | T], H, [H | T]).
remove_until([_ | T], Value, Ans):-
    remove_until(T, Value, Ans).


%If its the last head, don't add it
manage_moving_agent_intersections([H|T], H, _, [H|T]).
%If the next position is a new intersection, add it to your intersections, or stop to that point
manage_moving_agent_intersections(Ci, P, Ki, OutCi):-
    contains(Ki, P),
    (contains(Ci, P) ->
        remove_until(Ci, P, OutCi)
    ;
        OutCi = [P | Ci]
    ).
%Otherwise, just do nothing
manage_moving_agent_intersections(Ci, _, _, Ci).


%Can't get an open list path if there is no open list
pop_open_list(_, [], _, _, _, _):-fail.
%Given an open list, Position, Intersection info, NextOpenList, and Path, gets the path from the open list
pop_open_list(KnownPaths, [Open | T], Position, IntersectsInfo, T, Path):-
    Open = openPoint(OpenPosition, OpenIntersections),
    IntersectsInfo = [LastIntersection | _],
    find_astar(go(LastIntersection), [], Position, 999, [ToIntersectPath, _]),
    get_path_from_intersections(KnownPaths, OpenIntersections, IntersectsInfo, PathFromIntersections),
    append(ToIntersectPath, PathFromIntersections, AlmostPath),
    append(AlmostPath, [OpenPosition], Path).


map_adjacent_without(AgentID, NoPos, AdjPos, Object):-
    agent_adjacent(AgentID, AdjPos, Object),
    NoPos \= AdjPos.

    
acc_get_new_open_positions([], _, OP, OP).
acc_get_new_open_positions([Pos | T], PathFrom1, Acc, Op):-
    acc_get_new_open_positions(T, PathFrom1, [openPoint(Pos, PathFrom1) | Acc], Op).
get_new_open_positions(Positions, PathFrom1, OpenPositions):- acc_get_new_open_positions(Positions, PathFrom1, [], OpenPositions).


%gm_finishing_agent(AInfo, GlobalInfo, ReservedPositions, NextAgent, NextGlobalInfo, Move)
%If its at the finish, leave
gm_finishing_agent(agentInfo(ID, Pos, _, _, []), globalInfo(OPl, KI, Ip, Gs, NumFinished, Itf), _, agent(agentState(finished), agentInfo(ID, Pos, [], [], [])), globalInfo(OPl, KI, Ip, Gs, NextNumFinished, Itf), no_move):-
    leave_maze(ID),
    NextNumFinished is NumFinished + 1.
%If its next position is reserved already, don't move
gm_finishing_agent(agentInfo(Id, Pos, _, _, [NPos | T]), GlobalInfo, ReservedPositions, agent(agentState(going_to_finish), agentInfo(Id, Pos, [],[],[NPos | T])), GlobalInfo, no_move):-
        %Again, this is only true on the condition the next position has already been reserved or has an agent on it
        contains(ReservedPositions, NPos) ; lookup_pos(NPos, a(_)).


gm_finishing_agent(agentInfo(Id, _, _, _, [NPos| T]), GlobalInfo, _, agent(agentState(going_to_finish), agentInfo(Id, NPos, [], [], T)), GlobalInfo, NPos).


%The adjacent point, and intersection path from 1
%Agent ID, its position, its intersection path, the path from the last intersection, the path its travelling
%gi: OpenPoint list, Intersections, intersection paths, goal state, numFinished, intersectionsToFinish

gm_get_path_to_finish(agentInfo(ID, Pos, AIPath, _, _), KnownPaths, IntersectsToGoal, agentInfo(ID, Pos, [], [], PathToGoal)):-
    AIPath = [LastIntersection | _],
    find_astar(go(LastIntersection), [], Pos, 999, [PathToLastIntersection, _]),
    get_path_from_intersections(KnownPaths, IntersectsToGoal, AIPath, PathFromLastIntersection),
    append(PathToLastIntersection, PathFromLastIntersection, PathToGoal).

%gm_get_targeting_agent(AInfo, GlobalInfo, ReservedPositions, NextAgent, Move).
%If the next position is reserved, don't do anything
gm_get_targeting_agent(agentInfo(ID, Pos, IPath, _, [NPos | T]), _, ReservedPositions, agent(agentState(targeting), agentInfo(ID, Pos, IPath, [], [NPos | T])), no_move):-
    contains(ReservedPositions, NPos) ; lookup_pos(NPos, a(_)).
%If the agent has finished the path, set it to exploring    %assume that the intersection you are at is already on your IPath
gm_get_targeting_agent(agentInfo(ID, Pos, IPath, _, [LP | []]), _, _, agent(agentState(exploring), agentInfo(ID, LP, IPath, [LP, Pos], [])), LP).
%Otherwise its just moving about. 

%gm_get_targeting_agent(agentInfo(7, p(1, 3), [p(1, 1)], [], [p(1, 2), p(1, 1), p(2, 1)]), globalInfo([], [p(1, 1)], [], goalState(seeking), 0, []), [], _25866, _25870)
gm_get_targeting_agent(agentInfo(ID, _, IPath, _, [NextP | T]), globalInfo(_, KI, _, _, _, _), _, agent(agentState(targeting), agentInfo(ID, NextP, NIPath, [], T)), NextP):-
        manage_moving_agent_intersections(IPath, NextP, KI, NIPath).

%The adjacent point, and intersection path from 1
%Agent ID, its position, its intersection path, the path from the last intersection, the path its travelling
%gi: OpenPoint list, Intersections, intersection paths, goal state, numFinished, intersectionsToFinish


%Success case
gm_get_exploring_agent(agentInfo(ID, p(V,V), [IPH | IPT], PTH, _), globalInfo(_, KI, KnownPaths, _, _, _), agent(agentState(finished), agentInfo(ID, p(V,V), [], [], [])), NextGlobalInfo, no_move):-
    ailp_grid_size(GSize),
    GSize == V,
    leave_maze(ID),
    add_known_path(KnownPaths, IPH, p(V, V), PTH, NextKnownPaths),
    NextGlobalInfo = globalInfo([], [p(V, V) | KI], NextKnownPaths, goalState(known), 1, [p(V,V), IPH | IPT]).
%Other case
%gm_get_exploring_agent(ainfo, global([], [p(1, 1)], [], goalState(seeking), 0, []), _60000, _60002, _60004)
gm_get_exploring_agent(AInfo, globalInfo(OpenPoints, KI, KnownPaths, GS, NF, ITF), NextAgent, globalInfo(NextOpenPoints, NKI, NewKnownPaths, GS, NF, ITF), Move):-
        AInfo = agentInfo(ID, Pos, IPath, [Pos, LastPos | TPath], _),
        %Get all routes not including the one you just came from
        findall(AdjPos, map_adjacent_without(ID, LastPos, AdjPos, empty), Routes),
        length(Routes, NumOfRoutes),
        ((NumOfRoutes == 0) -> %deadend, hibernate and figure out what to do next turn
            NextAgent = agent(agentState(hibernating), agentInfo(ID, Pos, IPath, [], [])),
            NextOpenPoints = OpenPoints,
            NKI = KI,
            NewKnownPaths = KnownPaths,
            Move = no_move
        ;((NumOfRoutes == 1) -> %keep going
            Routes = [Move],
            NextAgent = agent(agentState(exploring), agentInfo(ID, Move, IPath, [Move, Pos, LastPos | TPath], [])),
            NextOpenPoints = OpenPoints,
            NKI = KI,
            NewKnownPaths = KnownPaths
        ; %New intersection, deal with heuristics later, you already have a predicate
            Routes = [MyNextPos | NewPositions],
            %Turn the routes you won't take into open positions
            get_new_open_positions(NewPositions, [Pos | IPath], NewPositionsToAdd),
            %Move to the open pos you took
            Move = MyNextPos,
            NextAgent = agent(agentState(exploring), agentInfo(ID, MyNextPos, [Pos | IPath], [MyNextPos, Pos], [])),
            %Next open points and the current open points and the ones you just found
            insert_points(OpenPoints, NewPositionsToAdd, NextOpenPoints),
            

            %append(OpenPoints, NewPositionsToAdd, NextOpenPoints),
            
            
            NKI = [Pos | KI],
            %Add the path to this intersection
            IPath = [LastIntersection | _],
            add_known_path(KnownPaths, LastIntersection, Pos, [Pos, LastPos | TPath], NewKnownPaths)
        )).




%The adjacent point, and intersection path from 1
%Agent ID, its position, its intersection path, the path from the last intersection, the path its travelling
%gi: OpenPoint list, Intersections, intersection paths, goal state, numFinished, intersectionsToFinish


%If the agent is finished, there is no need for it to move
get_agent_move(agent(agentState(finished), I), GI, _, agent(agentState(finished), I), GI, no_move).

%If he agent is heading to finish, get the move from that
get_agent_move(agent(agentState(going_to_finish), AInfo), GlobalInfo, ReservedPositions, NextAgent, NextGlobalInfo, Move):-
    gm_finishing_agent(AInfo, GlobalInfo, ReservedPositions, NextAgent, NextGlobalInfo, Move).

%No matter the state now, if it isn't going to finish or done, if the goal is known, path to it and start moving there
get_agent_move(agent(_, AInfo), globalInfo(G1, G2, KnownPaths, goalState(known), G3, IToFinish), _, agent(agentState(going_to_finish), FinishingAInfo), globalInfo(G1, G2, KnownPaths, goalState(known), G3, IToFinish), no_move):-
    gm_get_path_to_finish(AInfo, KnownPaths, IToFinish, FinishingAInfo).

get_agent_move(agent(agentState(targeting), AInfo), GlobalInfo, ReservedPositions, NextAgent, GlobalInfo, Move):-
    gm_get_targeting_agent(AInfo, GlobalInfo, ReservedPositions, NextAgent, Move).

get_agent_move(agent(agentState(exploring), AInfo), GlobalInfo, _, NextAgent, NextGlobalInfo, Move):-
    gm_get_exploring_agent(AInfo, GlobalInfo, NextAgent, NextGlobalInfo, Move).

%If it is hibernating and there are no open nodes, stay hibernating
get_agent_move(agent(agentState(hibernating), AInfo), globalInfo([], G1, G2, G3, G4, G5), _, agent(agentState(hibernating), AInfo), globalInfo([], G1, G2, G3, G4, G5), no_move).
%Otherwise find a new path
get_agent_move(agent(agentState(hibernating), AInfo), globalInfo(OpenList, G2, KnownPaths, G3, G4, G5), _, agent(agentState(targeting), NAInfo), globalInfo(NOpenList, G2, KnownPaths, G3, G4, G5), no_move):-
    AInfo = agentInfo(ID, Pos, IPath, _, _),
    pop_open_list(KnownPaths, OpenList, Pos, IPath, NOpenList, Path),
    NAInfo = agentInfo(ID, Pos, IPath, [], Path).






%No more agents, unify with all the accumulators, global info stays the same
get_agent_moves([], GlobalInfo, NextAgents, AgentOrder, Moves, NextAgents, GlobalInfo, AgentOrder, Moves).
%Run the current agent, add to he accumulators
get_agent_moves([Agent | RemainingAgents], GlobalInfo, NAAcc, AOAcc, MAcc, NextAgents, NextGlobalInfo, AgentOrder, Moves):-
    get_agent_move(Agent, GlobalInfo, MAcc, UpdatedAgent, UpdatedGlobalInfo, Move),
    Agent = agent(_, agentInfo(ID, _, _, _, _)),
    
    %If it hasn't got a move, the next accumulators are the same as this time
    (Move == no_move ->
        NAOACC = AOAcc,
        NMAcc = MAcc
    ;
    %Otherwise the next accumulators need the agents ID and move in it
        NAOACC = [ID | AOAcc], 
        NMAcc = [Move | MAcc]
    ),

    get_agent_moves(RemainingAgents, UpdatedGlobalInfo, [UpdatedAgent | NAAcc], NAOACC, NMAcc, NextAgents, NextGlobalInfo, AgentOrder, Moves).
%The version without accumulators
get_agent_moves(Agents, GlobalInfo, NextAgents, NextGlobalInfo, AgentOrder, Moves):-
    get_agent_moves(Agents, GlobalInfo, [], [], [], NextAgents, NextGlobalInfo, AgentOrder, Moves).



get_and_perform_moves(Agents, GlobalInfo, NextAgents, NextGlobalInfo):-
    get_agent_moves(Agents, GlobalInfo, NextAgents, NextGlobalInfo, AgentOrder, Moves),
    agents_do_moves(AgentOrder, Moves).

%Everyone has finished, end.
perform_step(NumberOfAgents, _, globalInfo(_, _, _, goalState(known), NumberOfAgents, _)).
perform_step(NumberOfAgents, Agents, GlobalInfo):-
    get_and_perform_moves(Agents, GlobalInfo, NextAgents, NextGlobalInfo),
    !,
    perform_step(NumberOfAgents, NextAgents, NextGlobalInfo).


%The adjacent point, and intersection path from 1
%Agent ID, its position, its intersection path, the path from the last intersection, the path its travelling
%gi: OpenPoint list, Intersections, intersection paths, goal state, numFinished, intersectionsToFinish


get_start_paths([], _, Ans, Ans).
get_start_paths([_ | Tq], [], Acc, Ans):-
    get_start_paths(Tq, Tq, Acc, Ans).
get_start_paths([Hq | Tq], [Hq | Tc], Acc, Ans):-
    get_start_paths([Hq | Tq], Tc, Acc, Ans).
get_start_paths([Hq | Tq], [Hc | Tc], Acc, Ans):-
    find_astar(go(Hc), [], Hq, 999, [Path,_]),
    add_known_path(Acc, Hq, Hc, [Hq |Path], NAcc),
    get_start_paths([Hq | Tq], Tc, NAcc, Ans).
get_start_paths(KI, StartPaths):-
    get_start_paths(KI, KI, [], StartPaths).

acc_setup_infos([], globalInfo(OpenPoints, KI, [], Gs, Nf, Itf), Agents, Agents, globalInfo(OpenPoints, KI, StartPaths, Gs, Nf, Itf), A, B, A, B):-
    get_start_paths(KI, StartPaths).
acc_setup_infos([ID | AgentIDs], globalInfo(OpenPoints, KI, [], Gs, Nf, Itf), AAcc, Agents, StartGlobalInfo, FirstMA, FirstMM, MAOut, MMOut):-
    get_agent_position(ID, Pos),
    NKI = [Pos | KI],
    findall(AdjPos, agent_adjacent(ID, AdjPos, empty), Routes),
    length(Routes, NumOfRoutes),
    (NumOfRoutes == 0 ->
        NAAcc = [agent(agentState(hibernating), agentInfo(ID, Pos, [Pos], [], [])) | AAcc],
        NewOpenPoints = OpenPoints,
        NMA = FirstMA,
        NMM = FirstMM
    ;
        Routes = [MyNextPos | NewPositions],
        %Turn the routes you won't take into open positions
        get_new_open_positions(NewPositions, [Pos], NewPositionsToAdd),
        NAAcc = [agent(agentState(exploring), agentInfo(ID, MyNextPos, [Pos], [MyNextPos, Pos], [])) | AAcc],
        append(OpenPoints, NewPositionsToAdd, NewOpenPoints),
        NMA = [ID | FirstMA],
        NMM = [MyNextPos| FirstMM]
    ),
    acc_setup_infos(AgentIDs, globalInfo(NewOpenPoints, NKI, [], Gs, Nf, Itf), NAAcc, Agents, StartGlobalInfo, NMA, NMM, MAOut, MMOut).


setup_infos(AgentIDs, PreGLobalInfo, Agents, StartGlobalInfo, FirstMA, FirstMM):-
    acc_setup_infos(AgentIDs, PreGLobalInfo, [], Agents, StartGlobalInfo, [], [], FirstMA, FirstMM).

solve_maze:-
    my_agents(AgentIDs),
    PreGLobalInfo = globalInfo([], [], [], goalState(seeking), 0, []),
    setup_infos(AgentIDs, PreGLobalInfo, Agents, StartGlobalInfo, FirstMA, FirstMM),
    agents_do_moves(FirstMA, FirstMM),
    length(AgentIDs, NumberOfAgents),
    !,
    perform_step(NumberOfAgents, Agents, StartGlobalInfo).

% Solve the maze, aiming to get all the agents to p(N,N)
solve_maze_random :-
    my_agents(Agents),
    find_moves(Agents,Moves),
    agents_do_moves(Agents,Moves),
    solve_maze_random.
    

%%%%%%%%%%%%%%%% USEFUL PREDICATES %%%%%%%%%%%%%%%%%%
% Find a possible move for each agent
find_moves([],[]).
find_moves([A|As],[M|Moves]) :-
    findall(P,agent_adjacent(A,P,_),PosMoves),
    random_member(M,PosMoves),
    find_moves(As,Moves).

