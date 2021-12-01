/*
 * game_predicates.pl
 *
 * Do not call the exported predicates directly, but access them via http through oscar_library.pl!
 *
 */

:- module(game_predicates,
  [ agent_current_position/2, 
    get_agent_position/2,
    agent_current_energy/2,
    get_agent_energy/2,
    internal_topup_energy/2,
    agent_topup_energy/2,
    internal_ask_oracle/4,
    agent_ask_oracle/4,
    internal_check_oracle/2,
    agent_check_oracle/2,
    internal_agent_do_moves/2,
    agent_do_moves/2,
    internal_agents_do_moves/2,
    agents_do_moves/2,
    internal_poss_step/4,
    internal_leave_game/1,
    internal_join_game/1,
    internal_lookup_pos/2,
    lookup_pos/2,
    game_status/1,
    internal_start_game/0,
    ailp_reset/0,
    map_adjacent/3,
    agent_adjacent/3,
    map_distance/3
  ]
).

:- use_module('../command_channel.pl').
:- use_module('oscar_library.pl',[query_world/2]).


% Dynamic predicates to store internal information 
:- dynamic
  ailp_internal/1,
  ailp_seen/1,
  available_colours/1,
  random_grid_size/1.

% Randomly define  a grid size for part 2
:- random_between(0,10,N),assert(random_grid_size(N)).
%%%%%%%%%% Changeable Parameters %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Available colours in the game, There must be at least as many as the number of players
:- assert(available_colours([purple, blue, beige, white, gray, pink, indianred, khaki, lavender, lightsalmon, mediumaquamarine])).

% There is ALWAYS 1 non playable player, which is used to send some commands
% so X = 11 implies that only 10 real players can join
max_players(X) :-
  ( part_module(3)    -> X = 11
  ; part_module(test) -> X = 11 
  ; otherwise         -> X = 2
  ).

internal_grid_size(X) :- 
  ( part_module(0) -> X = 10 % Lab Grid
  ; part_module(1) -> X = 20 % CW part 1
  ; part_module(2) -> random_grid_size(N), X is 15+N % CW part 2
  ; part_module(3) -> random_grid_size(N), X is 11+2*N % CW part 3
  % This must be odd or the maze will fail to generate
  ; part_module(101) -> X = 10 % Lab Search
  ; otherwise      -> X = 20).  

% Exported predicate for use in part3
ailp_grid_size(X) :- internal_grid_size(X).

get_num(oracle, X) :-
  internal_grid_size(N),
  ( part_module(0)    -> X = 0
  ; part_module(1)    -> X = 1
  ; part_module(2)    -> X = 10
  ; part_module(3)    -> X = 0
  ; part_module(100)  -> X = 1
  ; part_module(101)  -> X = 1

  ; part_module(test) -> X = N/2
  ; otherwise -> fail
  ).
get_num(charging_station, X) :-
  internal_grid_size(N),
  ( part_module(0)    -> X = 0
  ; part_module(1)    -> X = 4
  ; part_module(2)    -> X = 2
  ; part_module(3)    -> X = 0
  ; part_module(100)    -> X = 4
  ; part_module(101)    -> X = 0
  ; part_module(test) -> X = N/10
  ; otherwise -> fail
  ).
% 'thing' = wall
get_num(thing, X) :-
  internal_grid_size(N),
  ( part_module(0)    -> X = 0
  ; part_module(1)    -> X = 80
  ; part_module(2)    -> X is N*N/4
  ; part_module(3)    -> X = 0  % Part 3 uses an alternative method to place walls
  ; part_module(100)    -> X = 80
  ; part_module(101)    -> X = 25
  ; part_module(test) -> X is N*N/4
  ; otherwise -> fail
  ).

%%% End of changeable parameters %%%

%%%%%%%%%% Setup predicates %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%randomly generate an unique id for a new agent
new_agent_id(Max,Id) :-
  random(1, Max, PossId),
  ( agent_current_energy(PossId,_) -> new_agent_id(Max,Id)
  ; otherwise                      -> Id = PossId
  ).

colour_agent_position([A,_,_,X,Y]) :-
  agent_colour_path( A,Cpath),
  do_command([A, colour, X,Y,Cpath]),
  atomic_list_concat(['starts at p(',X,',',Y,')'], Message),
  do_command([A,console,Message]).

game_status(S) :-
  ailp_internal(game_status(S)).

% assign drawable features to the agent
% DrawableA has format [AgentId, Shape(n sides), Colour, initialX, initialY]
drawable_agent(A , DrawableA) :-
  random(3, 10, S), % Number of sides
  available_colours(Colours),
  random_member(C, Colours),!,
  select(C,Colours,Colours1),
  retract(available_colours(Colours)),
  assert(available_colours(Colours1)),
  Cpath = C,
  assert(ailp_internal(agent_colour_path(A, Cpath))),
  ( part_module(0) -> X=1, Y=1
  ; part_module(1) -> X=1, Y=1
  ; part_module(3) -> (maze_free_pos(p(X,Y)),internal_reveal_grid(p(X,Y),1))
  ; part_module(100) -> X=1, Y=1
  ; otherwise      -> random_free_pos(p(X,Y))
  ),
  assert(ailp_internal(agent_position(A, p(X,Y)))),
  internal_topup(Emax),
  L is ceiling(Emax/2),
  (part_module(1) -> Estart = 100
  ;otherwise     -> random(L,Emax,Estart)),
  assert(ailp_internal(agent_energy(A, Estart))),
  DrawableA = [A,S,C,X,Y].

% assigns a unique numerical id for a new agent
internal_join_game(Agent) :-
  \+game_status(running),
  max_players(Max),
  new_agent_id(Max, Agent),!,
  assert(ailp_internal(agent_energy(Agent, 0))), %temp assert so that ids can be retrieved by ailp_reset
  retractall(ailp_internal(game_status(ready))),
  atomic_list_concat(['Agent ',Agent,' joined game'], Message),
  do_command([Agent,console,Message]).
  
internal_leave_game(Agent) :-
  retract(ailp_internal(agent_position(Agent,_))),
  retract(ailp_internal(agent_energy(Agent,_))),
  retract(ailp_internal(agent_colour_path(Agent,_))),
  do_command([Agent,leave]).

%reset and draw the grid map
ailp_reset :-
  internal_grid_size(N),
  findall(A, (ailp_internal(agent_energy(A,_))), Agents),
  retractall(ailp_internal(_)),
  retractall(ailp_seen(_)),
  retractall(my_agent(_)),
  get_num(charging_station, NC),
  init_things(charging_station,NC),
  get_num(oracle, NO),
  init_things(oracle,NO),
  get_num(thing, NT),
  init_things(thing,NT), 
  (part_module(3) -> make_maze
  ;otherwise      -> true),
  wp:init_identity,  % defined in wp.pl
  maplist( drawable_agent, Agents, DrawableAgents),
  append( DrawableAgents, [[dyna, 0,red, 1,1]], AllAgents), % adds a dummy agent to use in do_command predicate
  ( part_module(100) -> true
  ; otherwise      -> reset([grid_size=N, cells=[[green,1,1,N,N]], agents=AllAgents]),
                      maplist( colour_agent_position, DrawableAgents),
                      internal_colour_map  % make objects visible at the start
  ),
  assert(ailp_internal(game_status(ready))).

% change game status from ready to running
internal_start_game :-
  % check if map is drawn/updated
  ( \+game_status(ready) -> atomic_list_concat(['Reset the map before starting the game.'], Message),
                            do_command([dyna,console,Message]), fail
  ; otherwise            -> retract(ailp_internal(game_status(_))),
                            assert(ailp_internal(game_status(running)))
  ).
%%%%%%%%%% Map predicates %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% internal_lookup_pos(+Pos, -OID)
% OID = (object at Pos) (Saves using map_adj to map positions)
internal_lookup_pos(Pos, OID) :-
  ground(Pos),
  ( internal_off_board(Pos)                               -> fail
  ; bagof( A, ailp_internal(agent_position(A, Pos)), [H]) -> OID = a(H)
  ; (part_module(3) -> seen_object(O,Pos,_)
    ;otherwise      -> internal_object(O,Pos,_))              -> OID = O
  ; otherwise                                             -> OID = empty
  ).

lookup_pos(Pos,OID) :- 
  query_world(internal_lookup_pos,[Pos,OID]).

% Reveals cells that are <= Dist away from Pos, batches colour commands simultaneously
% internal_reveal_grid(+Pos,+Dist)
internal_reveal_grid(Pos,Dist) :-
  internal_reveal_grid(Pos,Dist,C),
  do_commands(C).
internal_reveal_grid(Pos,Dist,CommandQueue) :-
  internal_adj_range(Pos,Dist,Cells),
  findall(Command,
         (member(P,Cells),internal_reveal_cell(P,Command), Command \= [])
         ,CommandQueue).

% This should not be called directly, only through internal reveal grid
% Command = [] if Pos has already been revealed
internal_reveal_cell(Pos,Command) :-
  Pos = p(X,Y),
  (retract(ailp_seen(unknown(Pos))) -> 
      (ailp_internal(thing(I,Pos)) -> (assert(ailp_seen(thing(I,Pos))),Command=[dyna,colour,X,Y,black])
      ;otherwise                   -> (Command=[dyna,colour,X,Y,green]))
  ;otherwise                            -> Command=[]).


% map_adjacent(+Pos, -AdjPos, -Occ)
% Occ = empty / agent / c(X) / o(X)  - charging station / oracle and ids
map_adjacent(Pos, AdjPos, OID) :-
  nonvar(Pos),
  internal_poss_step(Pos, _M, AdjPos, 1),
  query_world( internal_lookup_pos, [AdjPos, OID]).

% map_distance(+Pos1, +Pos2, -Distance)
% Manhattan distance between two grid squares
map_distance(p(X,Y),p(X1,Y1), D) :-
  D is abs(X - X1) + abs(Y - Y1).

% Places agent at either p(1,1) or next to another agent
maze_free_pos(P) :-
  (ailp_internal(agent_position(_,Pos)),
  map_adj(Pos,PPos,_),
  (check_pos(PPos, empty) -> (P = PPos,!)
  ;otherwise              -> fail));
  (P = p(1,1),!).

random_free_pos(P) :-
  internal_grid_size(N),
  random(1,N,X),
  random(1,N,Y),
  ( check_pos(p(X,Y), empty) -> (P = p(X,Y),!)
  ; otherwise                -> random_free_pos(P)
  ).

map_adj(Pos, AdjPos, OID) :-
  nonvar(Pos),
  internal_poss_step(Pos, _M, AdjPos, 1),
  check_pos(AdjPos, OID).

% Discover the cells up to N units away from Pos
internal_adj_range(Pos,0,[Pos]).
internal_adj_range(Pos,N,Range) :-
  N > 0,
  N1 is N-1,
  findall(Children,
         (map_adj(Pos,NPos,_),(internal_adj_range(NPos,N1,Children))),
         TRange),
  foldl(append,TRange,[],LRange),
  append(LRange,[Pos],LLRange),
  list_to_set(LLRange,Range).

%%%%%%%%%% Agent predicates %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% agent_adjacent(+Agent, -AdjPos, -Occ)
agent_adjacent(Agent, AdjPos, OID) :-
  nonvar(Agent),
  get_agent_position(Agent,Pos),
  internal_poss_step(Pos, _M, AdjPos, 1),
  lookup_pos(AdjPos, OID).

% agent_current_energy(+Agent, -Energy)
agent_current_energy(Agent, Energy) :-
  nonvar(Agent),
  var(Energy),
  ailp_internal(agent_energy(Agent,Energy)),
  atomic_list_concat(['Current energy:',Energy],' ',_A).
  %do_command([Agent,console,A]).

% Exported predicate used by agent
get_agent_energy(Agent,Energy) :-
  query_world(agent_current_energy,[Agent,Energy]).

% agent_current_position(+Agent, -Pos)
agent_current_position(Agent, Pos) :-
  nonvar(Agent),
  var(Pos),
  ailp_internal(agent_position(Agent,Pos)).

% Exported predicate used by agent
get_agent_position(Agent,Pos) :-
  query_world(agent_current_position,[Agent,Pos]).

% internal_topup_energy(+Agent, +OID)
% Agent's position needs to be map_adj to charging station identified by OID
internal_topup_energy(Agent, OID) :-
  nonvar(Agent),
  nonvar(OID),
  agent_current_position(Agent,Pos),
  map_adj(Pos, _AdjPos, OID),
  OID = c(_),
  retract(ailp_internal(agent_energy(Agent, _E))),
  internal_topup(Emax),
  assert(ailp_internal(agent_energy(Agent,Emax))).

agent_topup_energy(Agent, OID) :-
  query_world(internal_topup_energy,[Agent,OID]).

% internal_ask_oracle(+Agent, +OID, +Question, -Answer)
% Agent's position needs to be map_adj to oracle identified by OID
% fails if oracle already visited by Agent
internal_ask_oracle(Agent, OID, Question, Answer) :-
  nonvar(Agent),
  nonvar(OID),
  ( part_module(100) -> true
  ; otherwise      -> ( game_status(running) -> true
                      ; otherwise            -> do_command([Agent, console, 'start the game first']), fail
                      ),
                      \+ ailp_internal(agent_visited_oracle(Agent, OID))
  ),
  nonvar(Question),
  var(Answer),
  ( part_module(100) -> OID = o(_),
                      internal_object(OID, _AdjPos, Options),
                      member(question(Q)/answer(A),Options),
                      ( Question=Q -> Answer=A ; Answer='I do not know' )
  ; otherwise      -> internal_topup(Emax),
                      Cost is ceiling(Emax/10),
                      ailp_internal(agent_energy(Agent,Energy)),
                      ( Energy>=Cost -> agent_current_position(Agent,Pos),
                                       map_adj(Pos, AdjPos, OID),
                                       OID = o(_),
                                       internal_object(OID, AdjPos, Options),
                                       member( question(Q)/answer(A),Options),
                                       ( Question=Q -> Answer=A ; Answer='42' ),
                                       atomic_list_concat( [Question,Answer],': ',AA),
                                       internal_use_energy( Agent,Cost),
                                       assert( ailp_internal(agent_visited_oracle(Agent, OID)))
                      ; otherwise -> Answer='Sorry, not enough energy',AA=Answer
                      ),
                      do_command([Agent,console,AA])
  ).

agent_ask_oracle(Agent, OID, Question, Answer) :-
  (part_module(100) -> internal_ask_oracle(Agent,OID,Question,Answer)
  ;otherwise -> query_world(internal_ask_oracle,[Agent, OID, Question, Answer])).

% agent_colour_path(+Agent, -ColourPath)
agent_colour_path(Agent, ColourPath) :-
  nonvar(Agent),
  ailp_internal(agent_colour_path(Agent, ColourPath)).

% internal_check_oracle(+Agent, +OID)
% checks whether oracle already visited by Agent
internal_check_oracle(Agent, OID) :-
  nonvar(Agent),
  nonvar(OID),
  ailp_internal(agent_visited_oracle(Agent, OID)).

agent_check_oracle(Agent,OID) :-
  query_world(internal_check_oracle,[Agent,OID]).
% internal_agents_do_moves(+Agents,+Moves)
% Executes agent_do_move for zip(Agents,Moves), batches commands into single request
% Importantly this only executes one move per agent
internal_agents_do_moves(Agents,Moves) :-
  internal_agents_do_moves(Agents,Moves,Commands),
  do_commands(Commands,_).

internal_agents_do_moves(_,[],[]).
internal_agents_do_moves([A|As],[M|Ms],Commands) :-
  (agent_do_move(A,M,Command);Command = []),
  internal_agents_do_moves(As,Ms,OCommands),
  append(Command,OCommands,Commands).

agents_do_moves(Agents,Moves) :-
  query_world(internal_agents_do_moves,[Agents,Moves]).

% internal_agent_do_moves(+Agent, +ListOfMoves)
% seperate into individual commands  
internal_agent_do_moves(_, []).
internal_agent_do_moves(Agent, [H|T]) :-
  agent_do_move(Agent, H,Command),
  do_command(Command,_),
  internal_agent_do_moves(Agent,T).

agent_do_moves(A,Moves) :-
  query_world(internal_agent_do_moves,[A,Moves]).

% agent_do_move(+Agent, +To)
% Has constraint that To is map_adj to Agent's current position
% Reduces energy by 1 if step is valid
agent_do_move(Agent,To,Commands) :-
  nonvar(Agent),
  nonvar(To),
  game_status(running),
  agent_current_energy(Agent, F),
  F>0,
  %% check p(X,Y) if To is map_adj to current position and free
  agent_current_position(Agent,Pos),
  map_adj(Pos, To, Obj),
  Obj = empty,!,
  %% send move to server
  p(X,Y) = To,
  (part_module(3) -> internal_reveal_grid(To,1,RevealCommands)
  ;otherwise      -> RevealCommands = []),
  agent_colour_path(Agent, Cpath),
  Commands = [[Agent, move, X, Y],[Agent, colour, X, Y, Cpath]|RevealCommands],
  %% move was successful so decrease agent energy
  internal_use_energy(Agent,1),
  retract(ailp_internal(agent_position(Agent, _))),
  assert(ailp_internal(agent_position(Agent, To))).
  
%%%%%%%%%% Internal predicates %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
internal_topup(Emax) :-
  (part_module(0) -> Emax is 999999
  ;part_module(3) -> Emax is 999999
  ;part_module(101) -> Emax is 999999
  ;otherwise      -> (internal_grid_size(N),Emax is ceiling(N*N/4))
  ).
  

compute_step(p(X,Y), M, p(X1,Y1), I) :-
  ( M = s -> X1 =  X,    Y1 is Y+I
  ; M = e -> X1 is X+I,  Y1 =  Y
  ; M = n -> X1 =  X,    Y1 is Y-I
  ; M = w -> X1 is X-I,  Y1 =  Y
  ).

internal_poss_step(P0, M, PossPosition, I) :-
  member(M, [s,e,n,w]), % try moves in this order
  compute_step( P0, M, PossPosition, I).

internal_poss_step(P0, M, PossMoves, PossPosition, I) :-
  random_member(M, PossMoves), % moves randomly to any possible direction
  compute_step(P0, M, PossPosition, I).

% Internal predicate that will always have access to the ground truth
% check_pos(+Pos, -OID)
check_pos(Pos, OID) :-
  nonvar(Pos),
  ( internal_off_board(Pos)                               -> fail
  ; bagof( A, ailp_internal(agent_position(A, Pos)), _As) -> OID = agent
  ; internal_object(O,Pos,_)                             -> OID = O
  ; otherwise                                             -> OID = empty
  ).

internal_off_board(p(X,Y)) :-
  internal_grid_size(N),
  ( X < 1
  ; X > N
  ; Y < 1
  ; Y > N
  ).

internal_use_energy(Agent,Cost) :-
  nonvar(Agent),
  retract(ailp_internal(agent_energy(Agent, E))),
  E>0, E1 is E - Cost,
  assert(ailp_internal(agent_energy(Agent,E1))),
  ( E1 < 20 -> atomic_list_concat(['WARNING -- Low energy:',E1],' ',A),
               do_command([Agent,console,A])
  ; true
  ).

%% The position and number of these objects changes every time ailp_reset/0 is called
internal_object(c(I),Pos,[]) :-
  ailp_internal(charging_station(I,Pos)).
%% Oracles that have information
internal_object(o(I),Pos,[question(link)/answer(Link)]):-
  ailp_internal(oracle(I,Pos)),
  wp:ailp_identity(A),
  wp:random_link(A,Link).
%% Obstacles (things)
internal_object(t(I),Pos,[]) :-
  ailp_internal(thing(I,Pos)).

% Seen objects for part 3
seen_object(t(I),Pos,[]) :-
  ailp_seen(thing(I,Pos)).

% Unseen objects for part 3
seen_object(unknown,Pos,[]) :-
  ailp_seen(unknown(Pos)).

% Finds a command that will colour Pos according to Object
% internal_colour_loc(+Object,+Pos,-Command)
internal_colour_loc(O,p(X,Y),Command) :-
  ( O=t(_) -> Colour=black   % obstacle
  ; O=c(_) -> Colour=orange  % charging station
  ; O=o(_) -> Colour=red     % oracle
  ; O=unknown -> Colour=darkgray % unknown
  ),
  Command = [dyna,colour,X,Y,Colour].

% Creates a queue of commands using internal_colour_loc to shade the grid
internal_colour_map :-
  findall(Command,
  ((part_module(3) -> seen_object(O,Loc,_)
  ;otherwise      -> internal_object(O,Loc,_)),
  internal_colour_loc(O,Loc,Command)),
  CommandQueue
  ),
  do_commands(CommandQueue,_).

% Used to place objects on the grid
init_things(Label,_) :-
  (part_module(1);part_module(100)),!,
  ( Label=oracle           -> S=[164]
  ; Label=charging_station -> S=[720,1529,659,8]
  ; Label=thing            -> S=[2,6,10,11,12,15,16,17,81,85,86,88,93,94,165,171,172,173,241,242,244,247,257,258,320,322,324,328,329,331,401,402,405,406,409,413,414,416,482,498,560,563,566,573,575,644,645,657,727,807,813,818,880,886,890,898,961,972,978,1041,1043,1044,1047,1059,1128,1135,1139,1204,1206,1207,1214,1217,1287,1292,1298,1364,1374,1378,1443,1445,1446,1449,1521,1525,1530,1532,1534,1537]
  ; otherwise              -> S=[], fail
  ),
  internal_grid_size(N),
  internal_things(S,N,Label,1).
init_things(Label,Exp) :-
  K is ceiling(Exp),   % round up if Exp evaluates to a fraction
  KK = 99999,
  randset(K,KK,S),
  internal_grid_size(N),
  internal_things(S,N,Label,1).
  
internal_things([],_N,_L,_M).
internal_things([Z|Zs],N,Label,M) :-
  internal_number2pos(Z,N,Pos),
  Fact =.. [Label,M,Pos],
  ( check_pos(Pos, empty) -> assert(ailp_internal(Fact))
  ; otherwise             -> true
  ),
  M1 is M+1,
  internal_things(Zs,N,Label,M1).

% Convert a 1D coordinate into a 2D coordinate
internal_1d_to_2d(Z, N, p(X,Y)) :-
  X is mod(Z,N)+1,
  Y is div(Z,N)+1.

% Convert a number to a valid board position 
internal_number2pos(Z,N,p(X,Y)) :-
  K is ceiling(N*N/5),  % roughly one in five cells is an obstacle
  Z1 is mod(Z,K),
  Z2 is (Z-Z1)/K,
  X is mod(Z1,N) + 1,
  Y is mod(Z2,N) + 1.

%%%%%%%%%% Maze Generation predicates %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Uses randomized kruskals to create a Maze
make_maze :-
  internal_grid_size(N),
  NCells is (N*N)-1,
  maze_walls(NCells,N),
  findall(Pos,
         (between(0,NCells,W), internal_isWall(W,N),internal_1d_to_2d(W,N,Pos)),
         Walls),
  findall([Pos],
         (between(0,NCells,C), internal_isCell(C,N),internal_1d_to_2d(C,N,Pos)),
         Cells),
  random_permutation(Walls,ShuffledWalls),
  kruskals(Cells,ShuffledWalls).

% Create a lattice where empty cells are all spaced 1 unit apart
maze_walls(0,_).
maze_walls(Z,N) :-
  internal_1d_to_2d(Z,N,Pos),
  Pos = p(X,Y),
  assert(ailp_seen(unknown(Pos))),
  ( (1 is mod(X,2), 1 is mod(Y,2)) -> true
  ; otherwise                      -> assert(ailp_internal(thing(1,Pos)))
  ),
  Z1 is Z-1,
  maze_walls(Z1,N).

% True if the Z is a 1D coordinate adjacent to a empty cell
internal_isWall(Z,N) :-
  X is mod(Z,N)+1,
  Y is div(Z,N)+1,
  X1 is mod(X,2),
  Y1 is mod(Y,2),
  dif(X1,Y1).

% True if Z is a 1D coordinate of an empty cell
internal_isCell(Z,N) :-
  X is mod(Z,N)+1,
  Y is div(Z,N)+1,
  1 is mod(X,2),
  1 is mod(Y,2). 

% Implementation of randomised Kruskals to generate a maze by deleting walls without
% creating cycles
% kruskals(+CellSet,+Walls)

kruskals(_,[]).
kruskals(Cells,[Wall|Walls]):-
  map_adj(Wall,C1,empty),
  map_adj(Wall,C2,empty),
  C2 \= C1,
  member(CellSet1,Cells),
  member(C1,CellSet1),
  (member(C2,CellSet1) -> kruskals(Cells,Walls)
  ; otherwise          -> (member(CellSet2,Cells),
                           member(C2,CellSet2),
                           append(CellSet1,CellSet2,MergedCellSet),
                           append([MergedCellSet],Cells,NewCells),
                           delete(NewCells,CellSet1,NewCells2),
                           delete(NewCells2,CellSet2,NewCells3),
                           retract(ailp_internal(thing(1,Wall))),
                           kruskals(NewCells3,Walls))).
