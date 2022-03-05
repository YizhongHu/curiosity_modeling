# Curiosity Modeling 

In this project, we are trying to model the board game [Othello](https://en.wikipedia.org/wiki/Reversi).  

## Game Description
It is a two-player game with turns alternating between them. Players take turns to place down their disks on the board, with the objective to be the player with the most pieces of their color on the board at the end of the game. The rules of the game are as follows: Whenever a player places their piece on the board, any opposing pieces that are bordered at each end by that piece and another disc of the same color are flipped. In every move, a player must flip over at least one piece of the opponents. If they are unable to do so, their turn is skipped. The game ends when all the possible spots on the board have been occupied, or when no more valid moves are available.

## Model Structure
	
We chose to split a game up into individual turns. Our model represents the board at each turn, with the turns connected by a move predicate. Each turn corresponds to a State, and each player’s piece on the board corresponds to a Player Sig, with row and column values to represent where the piece should be on the board. Furthermore, we included a visualization script, othello.js, with our model to make visual interpretation of our model simpler.

In our model, we run test expect blocks to ensure that the basic setup of the board is satisfiable. Namely, the wellformed predicate is satisfiable, the initial state (ie. starting turn of the game) is satisfiable and the two win conditions, winning with more pieces and winning by converting all pieces on the board to one player’s piece is possible. In addition, we also included the cases where both a row and column piece could be flipped by one move and six pieces could be flipped by one move in test expect blocks. Finally, we included an inductive proof that cheating is not possible in our model.

However, there are a few key differences between our model and the actual game of Othello. Firstly, due to the run-time limitations of Forge, we had to shrink down the game board from its regular 8x8 size to 4x4. Secondly, in the actual game, if it is player A’s turn but they have no valid moves, player A’s turn is skipped and player B will take an extra turn. We had to exclude this case from our move predicate as we found that it would take Forge far too long to run. 

We provided a visualizer together with the model. Copying `orthello.js` into the SVG section of Sterling
and pressing run should give a diagram of the placement of discs at each state for each instance.

## Meanings of `sig` and `pred`

The model contains Player and State sigs. Each State represents a game board, while the Player represents the black and white pieces on the board. States are connected by a move pred, where a move is a valid move according to the rules of the game. In a State, at each position on the game board, a piece can either belong to player A with black pieces, player B with white pieces or have no piece there. No position on the game board can have more than one piece at any time. This representation allows us to model the game board at each turn and check that each turn has a valid transition and find any interesting turns or end game states.

The wellformed predicate ensures the board is a 4x4 size board.

The winAllPiecesSame and winByMorePieces pred each represent a game end condition, with the first being the case where all the pieces on the board belong to the same player while the second being the case where the board is full and the player with more pieces on the board wins.

The `canFlipTile` predicate checks for tiles we can flip in the conventional way. It is used for testing
It is composed of 8 sub-predicates: `canFlipColUp`, `canFlipColDown`, `canFlipRowLeft`, `canFlipRowRight`, `canFlipDiagTL`, `canFlipDiagTR`, `canFlipDiagBL`, `canFlipDiagBR`. For each a position on the board `(row2, col2)`, we check if it can be flipped by a piece at `(row, col)` in
a certain direction. We have positive tests for all of them.

A shorter version of `canFlipTile`, `canFlip`, is the one we used. Instead of listing every possible
direction there is, we calculate the directions. With full forge, this can hopefully reduce computation
in the future. We tested with simple configurations to check that in each direction, a tile flip
can be detected, and that no other tile flips can happen. 

We made an attempt at checking that a move can and must exist if some tile can be flipped by some placement of hand, with the `moveIFFCanFlip` test. However, we were running short of time and it was
having issues by the time of submission.

The cheating predicate checks for various cheating methods, namely, a player replaces a piece illegally, a player flips a piece illegally, a player takes two turns in a row or a player plays more than one piece in a turn. This is by no means a comprehensive test, and we reuse most of our model's
code to test for that, especially with if a piece is flipped illegally. However, this does build
confidence that as of the correctness of our model.

Most importantly, we made checks for states where one player cannot play anywhere. It is an integral 
part of the game that we omitted, but we can at least prove there are such states.

We have two run statements, one is a trace from the initial state. It has 8 States, but given the
computational power, we may be able to trace more states. We have another trace that demonstrate
a state transition (2 states) from a non-initial state. Some of them are not reachable from initial
state, as we will be able to see, 
