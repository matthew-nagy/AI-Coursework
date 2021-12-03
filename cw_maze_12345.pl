hibernating.
exploring.
pathing_to_open_position.
pathing_to_finish.
finished.
no_move.
agentState(hibernating).
agentState(exploring).
agentState(pathing_to_open_position).
agentState(pathing_to_finish).
agentState(finished).


seeking.
known.
goalState(seeking).
goalState(known).

%The adjacent point, and intersection path from 0
openPoint(p(_,_), _).

%Agent ID, its position, its intersection path, the path from the last intersection, the path its travelling
agentInfo(_, p(_, _), _, _, _).

%Representation of an agent
agent(agentState(_), agentInfo(_, _, _, _, _)).

%OpenPoint list, intersection paths, goal state, numFinished, intersectionsToFinish
globalInfo(_, _, goalState(_), _, _).


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

get_final_path(KnownPaths, IntersectsToGoal, MyIntersects, Path):-
    get_intersect_path_to_goal(IntersectsToGoal, MyIntersects, Intersections),
    Intersections = [IAt | IT],
    get_intersection_path(KnownPaths, IAt, IT, [], Path).
    


%Assuming that the agent is finishing, lets figure out what to do
%If they are at the goal, remove them, they are now finished
get_move_from_finishing_agent(_, ID, APos, [], GlobalInfo, APos, [], UpdatedGlobalInfo, no_move, agentState(finished)):-
    ailp_grid_size(GridSize),
    APos = p(GridSize, GridSize),
    leave_maze(ID),
    GlobalInfo = globalInfo(IL, IP, GS, NumFinished, ITF),
    NextNumFinished is NumFinished + 1,
    UpdatedGlobalInfo = globalInfo(IL, IP, GS, NextNumFinished, ITF).
%If another agent is in the way, do nothing
get_move_from_finishing_agent(Res, _, APos, [NextPos | RemainingPath], GlobalInfo, APos, [NextPos | RemainingPath], GlobalInfo, no_move, agentState(pathing_to_finish)):-
    lookup_pos(NextPos, a(_));
    contains(Res, NextPos).
%Otherwise move them
get_move_from_finishing_agent(_, _, _, [NextPos | RemainingPath], GlobalInfo, NextPos, RemainingPath, GlobalInfo, NextPos, agentState(pathing_to_finish)).


%get_move_from_backtracking_agent(agentInfo(ID, Position, IntersectionPath, PathFromIntersection, CurrentPath), Reserved, UpdatedAgent, Move).
%Case where you have backtracked to the intersection where you want to be
%so your path is now only 1 off
get_move_from_backtracking_agent(_, agentInfo(ID, Position, IntersectionPath, _, [ Pos | [] ]), _, UpdatedAgent, no_move):-
    UpdatedAgent = agent(agentState(exploring), agentInfo(ID, Position, [Position | IntersectionPath], [], [Pos | []])).
%What if your next position is reserved? Don't do it
get_move_from_backtracking_agent(_, agentInfo(ID, Position, IntersectionPath, PathFromIntersection, [NextPos | Rest]), Reserved, agentInfo(ID, Position, IntersectionPath, PathFromIntersection, [NextPos | Rest]), no_move):-
    lookup_pos(NextPos, a(_));
    contains(Reserved, NextPos).
%If you are about to be at an intersection you try and figure that shit out
get_move_from_backtracking_agent(KnownPaths, agentInfo(ID, _, [IAt , IN | IRest], [PNext | []], [PNext | PT]), _, UpdatedAgent, PNext):-
    remember_path(KnownPaths, IAt, IN, PathToThisIntersection),
    PathToThisIntersection = [_ | IPath],
    UpdatedAgent = agent(agentState(pathing_to_open_position), agentInfo(ID, PNext, [IN | IRest], IPath, PT)).
%Last case, you just do the move
get_move_from_backtracking_agent(agentInfo(ID, _, IntersectionPath, [NPos | NPTI], [NPos | NP]), _, agent(agentState(pathing_to_open_position), agentInfo(ID, NPos, IntersectionPath, NPTI, NP)), NPos).


%If the agent has finished, then no need for it to be updated
get_agent_move(agent(agentState(finished), AgentInfo), GlobalInfo, _, agent(agentState(finished), AgentInfo), GlobalInfo, no_move).
%If the agent is finishing, run its own functions for that
get_agent_move(agent(agentState(pathing_to_finish), AgentInfo), GlobalInfo, Res, UpdatedAgent, UpdatedGlobalInfo, Move):-
    AgentInfo = agentInfo(AgentID, APos, AIntersectionsVisited, _, ACurrentPath),
    get_move_from_finishing_agent(Res, AgentID, APos, ACurrentPath, GlobalInfo, NAPos, NACurrentPath, UpdatedGlobalInfo, Move, NextState),
    UpdatedAgent = agent(NextState, agentInfo(AgentID, NAPos, AIntersectionsVisited, _, NACurrentPath)).
%If the agent is doing anything else, and the goal has been discovered
get_agent_move(agent(_, AgentInfo), globalInfo(IL, KnownPaths, goalState(known), NumFinished, IntersectionsToGoal), _, UpdatedAgent, globalInfo(IL, KnownPaths, goalState(known), NumFinished, IntersectionsToGoal), no_move):-
    AgentInfo = agentInfo(ID, Position, IntersectionsVisited, PathFromLastIntersection, _),
    %Gets the path from the last intersection to the goal
    get_final_path(KnownPaths, IntersectionsToGoal, IntersectionsVisited, PathToGoalFromIntersection),
    %Now get the path from our current position to our last intersection
    PathFromLastIntersection = [_ | ReverseToLastIntersect],
    reverse(ReverseToLastIntersect, ToLastIntersect),
    %Append those, we have a path from where we are to the goal
    append(ToLastIntersect, PathToGoalFromIntersection, FinalPath),
    %Make sure we know whas up. Half the data here doesn't matter anymore so we throw that shit away
    UpdatedAgent = agent(agentState(pathing_to_finish), agentInfo(ID, Position, IntersectionsVisited, [], FinalPath)).


get_agent_move(agent(agentState(pathing_to_open_position), AgentInfo), GlobalInfo, Res, UpdatedAgent, GlobalInfo, Move):-
    GlobalInfo = globalInfo(_, KnownPaths, _, _, _),
    get_move_from_backtracking_agent(KnownPaths, AgentInfo, Res, UpdatedAgent, Move).


%If there are no open nodes, stay hibernating
get_agent_move(agent(agentState(hibernating), AgentInfo), GlobalInfo, _, agent(agentState(hibernating), AgentInfo), GlobalInfo, no_move):-
    GlobalInfo == globalInfo([], _, _, _, _).
%otherwise start pathing to that position
get_agent_move(agent(agentState(hibernating), AgentInfo), GlobalInfo, _, agent(agentState(pathing_to_open_position), NextAgentInfo), NextGlobalInfo, no_move):-
    AgentInfo = agentInfo(AID, Pos, IP, LastIntersectPath, _),
    GlobalInfo = globalInfo([openPoint(Pos, IntersectpathToOpen) | NOpenList], KnownPaths, GoalState, NumFinished, IntersectToFinish),
    get_final_path(KnownPaths, IntersectpathToOpen, IP, PathFromIntersect),
    append(PathFromIntersect, [Pos], PathFromIToOpen),
    append(LastIntersectPath, PathFromIToOpen, NewPath),
    NextAgentInfo = agentInfo(AID, Pos, IP, Last, NewPath),
    NextGlobalInfo = globalInfo(NOpenList, KnownPaths, GoalState, NumFinished, IntersectToFinish).

%OpenPoint list, intersection paths, goal state, numFinished, intersectionsToFinish
%The adjacent point, and intersection path from 0


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



%Everyone has finished, end.
perform_step(NumberOfAgents, _, globalInfo(_, _, goalState(known), NumberOfAgents, _)).
perform_step(NumberOfAgents, Agents, GlobalInfo):-
    get_agent_moves(Agents, GlobalInfo, NextAgents, NextGlobalInfo, AgentOrder, Moves),
    agents_do_moves(AgentOrder, Moves),
    !,
    perform_step(NumberOfAgents, NextAgents, NextGlobalInfo).

% Solve the maze, aiming to get all the agents to p(N,N)
solve_maze :-
    my_agents(Agents),
    find_moves(Agents,Moves),
    agents_do_moves(Agents,Moves),
    solve_maze.
    

%%%%%%%%%%%%%%%% USEFUL PREDICATES %%%%%%%%%%%%%%%%%%
% Find a possible move for each agent
find_moves([],[]).
find_moves([A|As],[M|Moves]) :-
    findall(P,agent_adjacent(A,P,_),PosMoves),
    random_member(M,PosMoves),
    find_moves(As,Moves).

