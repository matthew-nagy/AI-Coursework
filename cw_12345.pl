%These are the directions in which an agent may move
m(n).
m(e).
m(w).
m(s).

%Given a direction and a position, find what the new position is
get_moved_position(n, p(X, Y), p(X, NY)) :- NY is Y-1.
get_moved_position(e, p(X, Y), p(NX, Y)) :- NX is X+1.
get_moved_position(s, p(X, Y), p(X, NY)) :- NY is Y+1.
get_moved_position(w, p(X, Y), p(NX, Y)) :- NX is X-1.

%Get the board dimension. Removes the need for ailp knowlage
get_board_dimension(Dimension):- ailp_grid_size(Dimension).

%Make sure that position X, Y is on the board with size Dimension
on_board(p(X,Y), BoardDimension) :-
    between(1, BoardDimension, X),
    between(1, BoardDimension, Y).


%Binding of Prolog predicate to a name I will understand
contains(List, Element) :- member(Element, List).


%--------------------------------------------------
% node contains:   Position, PreviouslyTravelled, Cost, DistanceTravelled, EnergyHere
%       PreviouslyTravelled is a list of prior positions
%       Cost is the heuristic + DistanceTravelled
%       DistanceTravelled is the number of cells visited before arriving here
% searchData: OpenList, ClosedCells, BoardDimension
%       OpenList is the list of nodes to be searched
%       OpenCells are cells being searched.
%       ClosedCells are cells that have been searched.
%           They are unavailable to be added to the open list
%       BoardDimension is the size of the board
%--------------------------------------------------

not_last_travelled(_, []).
not_last_travelled(NewPosition, [Last | _]) :- NewPosition \= Last.

get_single_possible_position([Position, Travelled, _, _, _], [_, OpenCells, ClosedCells, BoardDimension], OutPos):-
    m(Direction),
    get_moved_position(Direction, Position, NextPosition),
    not_last_travelled(NextPosition, Travelled),
    on_board(NextPosition, BoardDimension),
    map_adjacent(Position, NextPosition, empty),
    %Put the most costly predicates at the end to reduce likelyhood of them being explored
    not(
        contains(OpenCells, NextPosition) ;
        contains(ClosedCells, NextPosition)        
    ),
    OutPos = NextPosition.

%Gets possible traversal positions from a node
get_possible_positions(Node, SearchData, PossiblePositions):-
    findall(OutPos, get_single_possible_position(Node, SearchData, OutPos), PossiblePositions).


%Gets the manhattan distance
manhattan_heuristic(DistanceToHere, p(TargX, TargY), p(HereX, HereY), NodeCost):-
    XDif is TargX - HereX,
    YDif is TargY - HereY,
    SquareGuess is (XDif * XDif) + (YDif * YDif),
    HeuristicDistance is sqrt(SquareGuess),
    NodeCost is HeuristicDistance + DistanceToHere.

get_heuristic(DistanceToHere, go(Target), Here, NodeCost):- manhattan_heuristic(DistanceToHere, Target, Here, NodeCost).
get_heuristic(DistanceToHere, find(_), _, DistanceToHere).

%Assuming you have the energy, set this new node for exploration
get_new_node(Task, LastNode, NewPosition, NewNode):-
    LastNode = [Position, PreviouslyTravelled, _, DistanceTravelled, OldEnergy],

    NewDistanceTravelled is DistanceTravelled + 1,
    get_heuristic(NewDistanceTravelled, Task, NewPosition, NodeCost),
    NewEnergyHere is OldEnergy - 1,
    NewNode = [NewPosition, [Position | PreviouslyTravelled], NodeCost, NewDistanceTravelled, NewEnergyHere].

get_new_nodes(OpenNodes, OpenCells, _, _, [], OpenNodes, OpenCells).

%OpenNodes is the list of currently openNodes
%Task is the task for the astar to complete
%LastNode is the node we are on
%posH posT is a list of positions to search
%NowNodes is the OpenList and New Node sorted in
get_new_nodes(OpenNodes, OpenCells, Task, LastNode, [PosH | PosT], NewNodes, NewCells):-
    get_new_nodes(OpenNodes, OpenCells, Task, LastNode, PosT, SemiNew, SemiCell),
    get_new_node(Task, LastNode, PosH, NewNode),
    NewNode = [Pos, _, _, _, _],
    NewCells = [Pos | SemiCell],
    insert_node(SemiNew, NewNode, NewNodes).



%Inserts a given node into a queue of nodes, ordered by their cost.
%Due to how the recursion works, the answer needs to reversed

finished_insert_node([], Acc, Ans):-reverse(Acc, Ans).
finished_insert_node([H | T], Acc, Ans):-
    finished_insert_node(T, [H | Acc], Ans).

w_insert_node([], InsertingNode, Acc, Ans) :- reverse([InsertingNode | Acc], Ans).
w_insert_node([H | T], InsertingNode, Acc, Ans):-
    H = [_, _, HeadCost, _, _],
    InsertingNode = [_, _, NewCost, _, _],
    NewCost < HeadCost,
    NewAcc = [H | [InsertingNode | Acc]],
    finished_insert_node(T, NewAcc, Ans).
w_insert_node([H | T], InsertingNode, Acc, Ans):-
    H = [_, _, HeadCost, _, _],
    InsertingNode = [_, _, NewCost, _, _],
    NewCost >= HeadCost,
    w_insert_node(T, InsertingNode, [H | Acc], Ans).


%Inserts nodes to the queue, ordering off cost 
insert_node([], InsertingNode, [InsertingNode]).
insert_node([QueH | QueT], InsertingNode, Ans):- w_insert_node([QueH | QueT], InsertingNode, [], Ans).

%No energy at cell case
explore_node(_, [Position,_,_,_,E], [OL, OC, CC, BD], [OL, OC, [Position | CC], BD]):- E =< 0, !, fail.

%Regular Case
explore_node(Task, Node, SearchData, NewSearchData):-
    Node = [ExploredPosition, _, _, _, _],
    get_possible_positions(Node, SearchData, PossiblePositions),
    SearchData = [Sd_OpenList, Sd_OpenCells, Sd_ClosedCells, BoardDimension],
    get_new_nodes(Sd_OpenList, Sd_OpenCells, Task, Node, PossiblePositions, N_OpenList, N_OpenCells),
    NewSearchData =[N_OpenList, N_OpenCells, [ExploredPosition | Sd_ClosedCells], BoardDimension].

check_success(go(X), EndPosition, _) :- achieved(go(X), EndPosition).
check_success(find(X), EndPosition, IlligalGoals) :-
    achieved(find(X), EndPosition),
    not(contains(IlligalGoals, X)).


%Exhaustive case
astar_step(_, _, SearchData, _, _) :-
    SearchData = [[], [], _, _],
    %Your open list is empty. Fail to find a path.
    fail.
%Success case
astar_step(Task, IlligalGoals, SearchData, Path, PathCost):-
    SearchData = [ [ThisNode | _], _, _, EnergyHere ],
    ThisNode = [EndPosition, PathToGetThere, PathCost, _, _],
    check_success(Task, EndPosition, IlligalGoals),
    EnergyHere > 0,
    %Found a path
    reverse([EndPosition | PathToGetThere], Path).
%Generic case
astar_step(Task, IlligalGoals, SearchData, Path, PathCost):-
    SearchData = [ [ThisNode | OpenList], OpenCells, TravelledList, BD ],
    ThisNode = [EndPosition, _, _, _, _],
    not(check_success(Task, EndPosition, IlligalGoals)),
    explore_node(Task, ThisNode, [OpenList, OpenCells, TravelledList, BD], NewSearchData),
    astar_step(Task, IlligalGoals, NewSearchData, Path, PathCost).

%This almost does it. But it includes the starting position
almost_find_astar(Task, IlligalGoals, StartPosition, StartEnergy, Path, PathCost):-
    get_heuristic(0, Task, StartPosition, Cost),
    StartNode = [StartPosition, [], Cost, 0, StartEnergy],
    ailp_grid_size(BD),
    astar_step(Task, IlligalGoals, [ [StartNode], [StartPosition], [], BD ], Path, PathCost).

find_astar(Task, IlligalGoals, StartPosition, StartEnergy, [Path, PathCost]):-
    almost_find_astar(Task, IlligalGoals, StartPosition, StartEnergy, AlmostPath, PathCost),
    AlmostPath = [_ | RestOfIt],
    Path = RestOfIt.



charge_station_not_visited(_, []).
charge_station_not_visited(c(X), [[empty, _] | Tail]):-
    charge_station_not_visited(c(X), Tail).
charge_station_not_visited(c(X), [c(Y) | Tail]):-
    X \= Y,
    charge_station_not_visited(c(X), Tail).
    
find_action(Task, IlligalGoals, Position, Energy, DesiredLocationEnergy, Action, OutAction, OutCost):-
    find_astar(Task, IlligalGoals, Position, Energy, [Path, OutCost]),
    RemainingEnergyAtGoal is Energy - OutCost,
    RemainingEnergyAtGoal >= DesiredLocationEnergy,
    !,%You have a path to target, stop looking
    OutAction = [[empty, Path] | Action].

%If you can't find a charger with the first goal you are screwed
find_action(find(c()), _, _, _, _, _, _, _) :- !, fail.
find_action(Task, IlligalGoals, Position, Energy, DesiredLocationEnergy, Action, OutAction, OutCost):-
    charge_station_not_visited(c(X), Action),
    find_astar(find(c(X)), IlligalGoals, Position, Energy, [ToChargePath, ToChargeCost]),
    last(ToChargePath, ChargePosition),
    SemiAction = [ c(X) , [empty, ToChargePath] | Action ],

    ailp_grid_size(GridSize),
    MaxEnergy is (GridSize * GridSize) / 4,
    find_action(Task, IlligalGoals, ChargePosition, MaxEnergy, DesiredLocationEnergy, SemiAction, OutAction, SemiCost),
    OutCost is SemiCost + ToChargeCost.
    




run_path(_, []).
run_path(Agent, [c(X) | Tail]):-
    run_path(Agent, Tail),
    agent_topup_energy(Agent, c(X)).
run_path(Agent, [ [empty, Path] | Tail ]):-
    run_path(Agent, Tail),
    agent_do_moves(Agent, Path).


% Accomplish a given Task and return the Cost
solve_task(Task,Cost) :-
    my_agent(A), get_agent_position(A,P),
    get_agent_energy(A, Energy),
    find_action(Task, [], P, Energy, 0, [], OutAction, Cost),
    run_path(A, OutAction).

% True if the Task is achieved with the agent at Pos
achieved(Task,Pos) :- 
    Task=find(Obj), map_adjacent(Pos,_,Obj)
    ;
    Task=go(Pos).