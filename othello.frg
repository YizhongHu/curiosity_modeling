#lang forge/bsl "cm" "dfz64hwblegqmenu; nhxnc2rfkjov1qjp"

abstract sig Player { }
-- Represents black and white
one sig B, W extends Player { }

sig State {
    next: lone State, 
    board: pfunc Int -> Int -> Player,
    nextPlayer: lone Player
}

pred wellformed {
    -- The board is 7x7 (subject to change)
    /*
    all s: State | {
        all i, j: Int {
            (i < 0 or i > 7 or j < 0 or j > 7)
                => no s.board[i][j]
        }
    }
    */
    // Temporarily shrinking board for testing
    -- The board is 4x4 (simplifying to reduce run time)
        all s: State | {
        all i, j: Int {
            (i < 0 or i > 3 or j < 0 or j > 3)
                => no s.board[i][j]
        }
    }
}

pred nextStateExists[s: State] {
    one s.next
}

pred initState[s: State] {
    -- the board is empty except for the B and W in the middle
    all i, j: Int | {
        {i = 1 and j = 1} => {s.board[i][j] = W}
            else {i = 1 and j = 2} => {s.board[i][j] = B}
                else {i = 2 and j = 2} => {s.board[i][j] = W}
                    else {i = 2 and j = 1} => {s.board[i][j] = B}
                        else no s.board[i][j]
    }
    /*
    all i, j: Int | {
        {i = 3 and j = 3} => {s.board[i][j] = W}
            else {i = 3 and j = 4} => {s.board[i][j] = B}
                else {i = 4 and j = 3} => {s.board[i][j] = B}
                    else {i = 4 and j = 4} => {s.board[i][j] = W}
                        else s.board[i][j]
    }
    */
    -- the first player is black
    s.nextPlayer = B
    -- A next state must exist
    nextStateExists[s]
}

pred pieceExists[i, j: Int, s: State] {
    some s.board[i][j]
}

fun countPlayerPieces[s: State, p: Player]: Int{
    #{i, j: Int | s.board[i][j] = p}
}

pred winAllPiecesSame[s: State, p: Player] {
    all i, j: Int | {
        -- all pieces on the board belong to the winning player
        pieceExists[i, j, s] => s.board[i][j] = p
        -- the next player is the loser
        s.nextPlayer != p
    }
    -- Not possible to win on initial board
    countPlayerPieces[s, p] > 4
    -- no next state
    not nextStateExists[s]
}

pred winByMorePieces[s: State, p: Player] {
    some p2: Player | {
        -- 2 distinct players
        p != p2

        -- p1 wins as they have more pieces on the board
        countPlayerPieces[s, p] > countPlayerPieces[s, p2]

        -- Board is full
        all i, j: Int | {
            -- (i >= 0 and i <= 7 and j >= 0 and j <= 7)
            -- needs this line otherwise unsat even tho already guaranteed in wellformed
                (i >= 0 and i <= 3 and j >= 0 and j <= 3)
                    => pieceExists[i, j, s]
        }
    }
    
    -- no next state
    not nextStateExists[s]

}

test expect {
    -- Initial and final states are satisfiable:
    baselineNotVacuous: {}
    for exactly 1 State is sat
    boardNotVacuous: {wellformed}
    for exactly 1 State, 4 Int is sat
    initIsSat: {
        wellformed
        some init: State | initState[init]
    } for exactly 1 State, 4 Int is sat
    winByAllPieces: {
        wellformed
        some s: State | some p: Player | winAllPiecesSame[s, p]
    } for exactly 1 State, 4 Int is sat
    winWithMorePieces: {
        wellformed
        some s: State | some p: Player |  winByMorePieces[s, p]
    } for exactly 1 State, 4 Int is sat
}

pred canFlipRowRight[prev: State, row, col: Int, post: State, row2, col2: Int] {
    -- The players cannot be the same
    prev.nextPlayer != post.nextPlayer

    -- row, col is where new piece is placed down
    -- row2, col2 is where a previously existing piece on the board is
    row = row2
    col2 > col
    
    -- Must have no piece there beforehand
    no prev.board[row][col]
    -- Must have player piece there after
    post.board[row][col] = prev.nextPlayer

    some colEnd: Int | {
        -- Checking only to the right
        colEnd > col2
        -- Must exist a piece to the right that belongs to the player who just placed a piece down
        prev.board[row][colEnd] = prev.nextPlayer
        all colBetween: Int | {
            -- Checking all positions between colEnd and col
            -- All pieces along the way must belong to the opposing player
            -- Must have piece at every step on the way
            (colBetween > col and colBetween < colEnd) => prev.board[row][colBetween] = post.nextPlayer
        }
    }
}

pred canFlipRowLeft[prev: State, row, col: Int, post: State, row2, col2: Int] {
    -- The players cannot be the same
    prev.nextPlayer != post.nextPlayer

    -- row, col is where new piece is placed down
    -- row2, col2 is where a previously existing piece on the board is
    row = row2
    col2 < col
    
    -- Must have no piece there beforehand
    no prev.board[row][col]
    -- Must have player piece there after
    post.board[row][col] = prev.nextPlayer

    some colEnd: Int | {
        -- Checking only to the left
        colEnd < col2
        -- Must exist a piece to the left that belongs to the player who just placed a piece down
        prev.board[row][colEnd] = prev.nextPlayer
        all colBetween: Int | {
            -- Checking all positions between colEnd and col
            -- All pieces along the way must belong to the opposing player
            -- Must have piece at every step on the way
            (colBetween > colEnd and colBetween < col) => prev.board[row][colBetween] = post.nextPlayer
        }
    }
}

pred canFlipColUp[prev: State, row, col: Int, post: State, row2, col2: Int] {
    -- The players cannot be the same
    prev.nextPlayer != post.nextPlayer

    -- row, col is where new piece is placed down
    -- row2, col2 is where a previously existing piece on the board is
    row > row2
    col2 = col
    
    -- Must have no piece there beforehand
    no prev.board[row][col]
    -- Must have player piece there after
    post.board[row][col] = prev.nextPlayer

    some rowEnd: Int | {
        -- Checking only above, take 0 as highest row
        row2 > rowEnd
        -- Must exist a piece above that belongs to the player who just placed a piece down
        prev.board[rowEnd][col] = prev.nextPlayer
        all rowBetween: Int | {
            -- Checking all positions between rowEnd and row
            -- All pieces along the way must belong to the opposing player
            -- Must have piece at every step on the way
            (rowBetween > rowEnd and rowBetween < row) => prev.board[rowBetween][col] = post.nextPlayer
        }
    }
}

pred canFlipColDown[prev: State, row, col: Int, post: State, row2, col2: Int] {
    -- The players cannot be the same
    prev.nextPlayer != post.nextPlayer

    -- row, col is where new piece is placed down
    -- row2, col2 is where a previously existing piece on the board is
    row < row2
    col2 = col
    
    -- Must have no piece there beforehand
    no prev.board[row][col]
    -- Must have player piece there after
    post.board[row][col] = prev.nextPlayer

    some rowEnd: Int | {
        -- Checking only below, take 0 as highest row
        row2 < rowEnd
        -- Must exist a piece below that belongs to the player who just placed a piece down
        prev.board[rowEnd][col] = prev.nextPlayer
        all rowBetween: Int | {
            -- Checking all positions between rowEnd and row
            -- All pieces along the way must belong to the opposing player
            -- Must have piece at every step on the way
            (rowBetween < rowEnd and rowBetween > row) => prev.board[rowBetween][col] = post.nextPlayer
        }
    }
}

pred canFlipDiagBR[prev: State, row, col: Int, post: State, row2, col2: Int] {
    -- The players cannot be the same
    prev.nextPlayer != post.nextPlayer

    -- row, col is where new piece is placed down
    -- row2, col2 is where a previously existing piece on the board is
    row2 > row
    subtract[row2, row] = subtract[col2, col]  // Major diagonal
    
    -- Must have no piece there beforehand
    no prev.board[row][col]
    -- Must have player piece there after
    post.board[row][col] = prev.nextPlayer

    some rowEnd, colEnd: Int | {
        -- Checking only the top-left diagonal of row2 col2
        rowEnd > row2
        subtract[rowEnd, row] = subtract[colEnd, col]
        -- Must exist a piece to the bottom right
        -- that belongs to the player who just placed a piece down
        prev.board[rowEnd][colEnd] = prev.nextPlayer
        all rowBetween, colBetween: Int | {
            -- Checking all positions between rowEnd and row
            -- All pieces along the way must belong to the opposing player
            -- Must have piece at every step on the way
            (subtract[rowEnd, row] = subtract[colEnd, col] and
                rowBetween < rowEnd and rowBetween > row)
                => prev.board[rowBetween][rowBetween] = post.nextPlayer
        }
    }
}

pred canFlipDiagTL[prev: State, row, col: Int, post: State, row2, col2: Int] {
    -- The players cannot be the same
    prev.nextPlayer != post.nextPlayer

    -- row, col is where new piece is placed down
    -- row2, col2 is where a previously existing piece on the board is
    row2 < row
    subtract[row2, row] = subtract[col2, col]  // Major diagonal
    
    -- Must have no piece there beforehand
    no prev.board[row][col]
    -- Must have player piece there after
    post.board[row][col] = prev.nextPlayer

    some rowEnd, colEnd: Int | {
        -- Checking only the top-left diagonal of row2 col2
        rowEnd < row2
        subtract[rowEnd, row] = subtract[colEnd, col]
        -- Must exist a piece to the top left that belongs to the player who just placed a piece down
        prev.board[rowEnd][colEnd] = prev.nextPlayer
        all rowBetween, colBetween: Int | {
            -- Checking all positions between rowEnd and row
            -- All pieces along the way must belong to the opposing player
            -- Must have piece at every step on the way
            (subtract[rowEnd, row] = subtract[colEnd, col] and
                rowBetween > rowEnd and rowBetween < row)
                => prev.board[rowBetween][rowBetween] = post.nextPlayer
        }
    }
}

pred canFlipDiagTR[prev: State, row, col: Int, post: State, row2, col2: Int] {
    -- The players cannot be the same
    prev.nextPlayer != post.nextPlayer

    -- row, col is where new piece is placed down
    -- row2, col2 is where a previously existing piece on the board is
    row2 > row
    subtract[row2, row] = subtract[col, col2]  // Minor diagonal
    
    -- Must have no piece there beforehand
    no prev.board[row][col]
    -- Must have player piece there after
    post.board[row][col] = prev.nextPlayer

    some rowEnd, colEnd: Int | {
        -- Checking only the top-right diagonal of row2 col2
        rowEnd > row2
        subtract[rowEnd, row] = subtract[col, colEnd]
        -- Must exist a piece to the top right that belongs to the player who just placed a piece down
        prev.board[rowEnd][colEnd] = prev.nextPlayer
        all rowBetween, colBetween: Int | {
            -- Checking all positions between rowEnd and row
            -- All pieces along the way must belong to the opposing player
            -- Must have piece at every step on the way
            (subtract[rowEnd, row] = subtract[col, colEnd] and
                rowBetween < rowEnd and rowBetween > row)
                => prev.board[rowBetween][rowBetween] = post.nextPlayer
        }
    }
}

pred canFlipDiagBL[prev: State, row, col: Int, post: State, row2, col2: Int] {
    -- The players cannot be the same
    prev.nextPlayer != post.nextPlayer

    -- row, col is where new piece is placed down
    -- row2, col2 is where a previously existing piece on the board is
    row2 < row
    subtract[row2, row] = subtract[col, col2]  // Minor diagonal
    
    -- Must have no piece there beforehand
    no prev.board[row][col]
    -- Must have player piece there after
    post.board[row][col] = prev.nextPlayer

    some rowEnd, colEnd: Int | {
        -- Checking only the top-right diagonal of row2 col2
        rowEnd < row2
        subtract[rowEnd, row] = subtract[col, colEnd]
        -- Must exist a piece to the bottom left
        -- that belongs to the player who just placed a piece down
        prev.board[rowEnd][colEnd] = prev.nextPlayer
        all rowBetween, colBetween: Int | {
            -- Checking all positions between rowEnd and row
            -- All pieces along the way must belong to the opposing player
            -- Must have piece at every step on the way
            (subtract[rowEnd, row] = subtract[col, colEnd] and
                rowBetween > rowEnd and rowBetween < row)
                => prev.board[rowBetween][rowBetween] = post.nextPlayer
        }
    }
}

fun countPieces[s: State]: Int{
    #{i, j: Int | some s.board[i][j]}
}

pred canFlipTile[prev: State, row, col: Int, post: State, row2, col2: Int] {
    -- After a piece is played at (row, col), check if a piece at (row2, col2)
    -- need to be flipped
    canFlipRowRight[prev, row, col, post, row2, col2]
    or canFlipRowLeft[prev, row, col, post, row2, col2]
    or canFlipColUp[prev, row, col, post, row2, col2]
    or canFlipColDown[prev, row, col, post, row2, col2]
    or canFlipDiagTL[prev, row, col, post, row2, col2]
    or canFlipDiagTR[prev, row, col, post, row2, col2]
    or canFlipDiagBL[prev, row, col, post, row2, col2]
    or canFlipDiagBR[prev, row, col, post, row2, col2]
}

pred move[prev: State, row: Int, col: Int, post: State] {
    -- Guard
    -- The place where the next piece is placed is empty
    no prev.board[row][col]
    
    -- The player needs to change
    prev.nextPlayer != post.nextPlayer
    
    -- Only one piece was placed down
    subtract[countPieces[post], countPieces[prev]] = 1
    
    -- Must have difference of at least 2 pieces between each board for current player as this implies that a piece was flipped
    subtract[countPlayerPieces[post, prev.nextPlayer], countPlayerPieces[prev, prev.nextPlayer]] > 1

    all row2, col2: Int | {
        (row = row2 and col = col2) => {
            -- Player placed down piece
            post.board[row2][col2] = prev.nextPlayer
        } else {
            -- Changed due to being able to flip the piece
            { canFlipTile[prev, row, col, post, row2, col2] }
                => prev.board[row2][col2] != post.board[row2][col2]
                -- otherwise stays the same
                else prev.board[row2][col2] = post.board[row2][col2]
        }
    }
}

pred cheatReplacePiece[prev: State, row, col: Int, post: State] {
    -- Player makes their move by swapping a pre-exisiting piece with their own
    pieceExists[row, col, prev]
    prev.board[row][col] != prev.nextPlayer
    post.board[row][col] = prev.nextPlayer
    
    -- Appears as though no piece was placed down
    subtract[countPieces[post], countPieces[prev]] = 0
}

pred cheatIllegalFlip[prev: State, row, col: Int, post: State] {
    -- Player flips pieces that should not be able to be flipped
    some row2, col2 : Int | {
        not canFlipTile[prev, row, col, post, row2, col2]
        prev.board[row2][col2] != post.board[row2][col2]
    }
}

pred cheatTwoTurns[prev: State, row, col: Int, post: State] {
    -- Player takes two turns in a row
    prev.nextPlayer = post.nextPlayer
}

pred cheatMoreThanOnePiecePlayed[prev: State, row, col: Int, post: State] {
    -- Player places multiple pieces down
    subtract[countPieces[post], countPieces[prev]] > 1
}


pred cheating[s: State] {
    some row, col: Int | {
        cheatReplacePiece[s, row, col, s.next] or
        cheatIllegalFlip[s, row, col, s.next] or
        cheatTwoTurns[s, row, col, s.next] or
        cheatMoreThanOnePiecePlayed[s, row, col, s.next] 
    }
}


-- Both rows and col can be flipped at once
test expect {
    bothRowAndColFlip: {
        wellformed
        some s1, s2: State | {
            some row, col: Int | {
                s1.next = s2
                move[s1, row, col, s2]
                some col2: Int | s2.board[row][col2] != s1.board[row][col2]
                some row2: Int | s2.board[row2][col] != s1.board[row2][col]
            }
        }
    } for exactly 2 State, 4 Int for {next is linear} is sat

    -- At most 6 pieces can be flipped from a single move on a wellformed board
    flipSixAtOnce: {
    wellformed
    some s1, s2: State | {
        some row, col: Int | {
            s1.next = s2
            move[s1, row, col, s2]
            subtract[countPlayerPieces[s2, s1.nextPlayer], countPlayerPieces[s1, s1.nextPlayer]] = 6
            }
        }
    } for exactly 2 State, 4 Int for {next is linear} is sat
}

-- inductive proof of no cheating
test expect {
    inductive: {
        wellformed
        some disj pre, post: State | 
        some row, col: Int | {       
            move[pre, row, col, post]
            not cheating[pre]
            cheating[post]
        }
    } for 2 State, 4 Int is unsat
}

run {
    wellformed
    all s: State | {
        {some s.next} => {
            some row, col: Int | move[s, row, col, s.next]
        }
    }
} for exactly 4 State, 4 Int for {next is linear}
