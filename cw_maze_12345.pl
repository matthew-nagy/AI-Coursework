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

