#lang forge/bsl "cm" "dfz64hwblegqmenu; nhxnc2rfkjov1qjp"

abstract sig Player { }
-- Represents black and white
one sig B, W extends Player { }

sig State {
    next: lone State, 
    board: pfunc Int -> Int -> Player,
    nextPlayer: one Player
}

pred inbounds[row, col: Int] {
    row >= 0 and row <= 3 and col >= 0 and col <= 3
} 

pred wellformed {
    all s: State | {
        all i, j: Int {
            (not inbounds[i, j]) => no s.board[i][j]
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

example canFlipInitialRight is {
    wellformed 
    some s: State | {
        some s.next
        canFlipRowRight[s, 1, 0, s.next, 1, 1]
    }
} for {
    State = `S0 + `S1
    B = `B0
    W = `W0
    Player = B + W
    next = `S0 -> `S1
    nextPlayer = `S0 -> `B0 + `S1 -> `W0

    board = `S0 -> 1 -> 1 -> `W0 + `S0 -> 1 -> 2 -> `B0 +
            `S0 -> 2 -> 1 -> `B0 + `S0 -> 2 -> 2 -> `W0 + 
            `S1 -> 1 -> 0 -> `B0 + `S1 -> 1 -> 1 -> `B0 + `S1 -> 1 -> 2 -> `B0 +
                                   `S1 -> 2 -> 1 -> `B0 + `S1 -> 2 -> 2 -> `W0
}

pred canFlipRowLeft[prev: State, row, col: Int, post: State, row2, col2: Int] {
    -- The players cannot be the same
    prev.nextPlayer != post.nextPlayer

    -- row, col is where new piece is placed down
    -- row2, col2 is where a previously existing piece on the board is
    row = row2
    col2 < col

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

example canFlipInitialLeft is {
    wellformed 
    some s: State | {
        some s.next
        canFlipRowLeft[s, 2, 3, s.next, 2, 2]
    }
} for {
    State = `S0 + `S1
    B = `B0
    W = `W0
    Player = B + W
    next = `S0 -> `S1
    nextPlayer = `S0 -> `B0 + `S1 -> `W0

    board = `S0 -> 1 -> 1 -> `W0 + `S0 -> 1 -> 2 -> `B0 +
            `S0 -> 2 -> 1 -> `B0 + `S0 -> 2 -> 2 -> `W0 + 
            `S1 -> 1 -> 1 -> `W0 + `S1 -> 1 -> 2 -> `B0 +
            `S1 -> 2 -> 1 -> `B0 + `S1 -> 2 -> 2 -> `B0 + `S1 -> 2 -> 3 -> `B0
}

pred canFlipColUp[prev: State, row, col: Int, post: State, row2, col2: Int] {
    -- The players cannot be the same
    prev.nextPlayer != post.nextPlayer

    -- row, col is where new piece is placed down
    -- row2, col2 is where a previously existing piece on the board is
    row > row2
    col2 = col

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


example canFlipInitialUp is {
    wellformed 
    some s: State | {
        some s.next
        canFlipColUp[s, 3, 2, s.next, 2, 2]
    }
} for {
    State = `S0 + `S1
    B = `B0
    W = `W0
    Player = B + W
    next = `S0 -> `S1
    nextPlayer = `S0 -> `B0 + `S1 -> `W0

    board = `S0 -> 1 -> 1 -> `W0 + `S0 -> 1 -> 2 -> `B0 +
            `S0 -> 2 -> 1 -> `B0 + `S0 -> 2 -> 2 -> `W0 + 
            `S1 -> 1 -> 1 -> `W0 + `S1 -> 1 -> 2 -> `B0 +
            `S1 -> 2 -> 1 -> `B0 + `S1 -> 2 -> 2 -> `B0
                                 + `S1 -> 3 -> 2 -> `B0
}

pred canFlipColDown[prev: State, row, col: Int, post: State, row2, col2: Int] {
    -- The players cannot be the same
    prev.nextPlayer != post.nextPlayer

    -- row, col is where new piece is placed down
    -- row2, col2 is where a previously existing piece on the board is
    row < row2
    col2 = col

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

example canFlipInitialDown is {
    wellformed 
    some s: State | {
        some s.next
        canFlipColDown[s, 0, 1, s.next, 1, 1]
    }
} for {
    State = `S0 + `S1
    B = `B0
    W = `W0
    Player = B + W
    next = `S0 -> `S1
    nextPlayer = `S0 -> `B0 + `S1 -> `W0

    board = `S0 -> 1 -> 1 -> `W0 + `S0 -> 1 -> 2 -> `B0 +
            `S0 -> 2 -> 1 -> `B0 + `S0 -> 2 -> 2 -> `W0 + 
            `S1 -> 0 -> 1 -> `B0 +
            `S1 -> 1 -> 1 -> `B0 + `S1 -> 1 -> 2 -> `B0 +
            `S1 -> 2 -> 1 -> `B0 + `S1 -> 2 -> 2 -> `W0
}

pred sameMajorDiag[row, col, row2, col2: Int] {
    subtract[row2, row] = subtract[col2, col]
}

pred sameMinorDiag[row, col, row2, col2: Int] {
    subtract[row2, row] = subtract[col, col2]
}

pred canFlipDiagBR[prev: State, row, col: Int, post: State, row2, col2: Int] {
    -- The players cannot be the same
    prev.nextPlayer != post.nextPlayer

    -- row, col is where new piece is placed down
    -- row2, col2 is where a previously existing piece on the board is
    row2 > row
    sameMajorDiag[row, col, row2, col2]

    some rowEnd, colEnd: Int | {
        -- Checking only the top-left diagonal of row2 col2
        rowEnd > row2
        sameMajorDiag[row, col, rowEnd, colEnd]
        -- Must exist a piece to the bottom right
        -- that belongs to the player who just placed a piece down
        prev.board[rowEnd][colEnd] = prev.nextPlayer
        all rowBetween, colBetween: Int | {
            -- Checking all positions between rowEnd and row
            -- All pieces along the way must belong to the opposing player
            -- Must have piece at every step on the way
            (sameMajorDiag[row, col, rowBetween, colBetween] and
                rowBetween < rowEnd and rowBetween > row)
                => {prev.board[rowBetween][colBetween] = post.nextPlayer}
        }
    }
}

example someFlipDiagBR is {
    wellformed 
    some s: State | {
        some s.next
        canFlipDiagBR[s, 0, 0, s.next, 1, 1]
    }
} for {
    State = `S0 + `S1
    B = `B0
    W = `W0
    Player = B + W
    next = `S0 -> `S1
    nextPlayer = `S0 -> `B0 + `S1 -> `W0

    board = `S0 -> 1 -> 1 -> `W0 + `S0 -> 1 -> 2 -> `B0 +
            `S0 -> 2 -> 1 -> `B0 + `S0 -> 2 -> 2 -> `B0 + 
            `S1 -> 0 -> 0 -> `B0 +
                                   `S1 -> 1 -> 1 -> `B0 + `S1 -> 1 -> 2 -> `B0 +
                                   `S1 -> 2 -> 1 -> `B0 + `S1 -> 2 -> 2 -> `B0
}

pred canFlipDiagTL[prev: State, row, col: Int, post: State, row2, col2: Int] {
    -- The players cannot be the same
    prev.nextPlayer != post.nextPlayer

    -- row, col is where new piece is placed down
    -- row2, col2 is where a previously existing piece on the board is
    row2 < row
    sameMajorDiag[row, col, row2, col2] // Major diagonal

    some rowEnd, colEnd: Int | {
        -- Checking only the top-left diagonal of row2 col2
        rowEnd < row2
        sameMajorDiag[row, col, rowEnd, colEnd]
        -- Must exist a piece to the top left that belongs to the player who just placed a piece down
        prev.board[rowEnd][colEnd] = prev.nextPlayer
        all rowBetween, colBetween: Int | {
            -- Checking all positions between rowEnd and row
            -- All pieces along the way must belong to the opposing player
            -- Must have piece at every step on the way
            (sameMajorDiag[row, col, rowBetween, colBetween] and
                rowBetween > rowEnd and rowBetween < row)
                => prev.board[rowBetween][colBetween] = post.nextPlayer
        }
    }
}

example someFlipDiagTL is {
    wellformed 
    some s: State | {
        some s.next
        canFlipDiagTL[s, 3, 3, s.next, 2, 2]
    }
} for {
    State = `S0 + `S1
    B = `B0
    W = `W0
    Player = B + W
    next = `S0 -> `S1
    nextPlayer = `S0 -> `B0 + `S1 -> `W0

    board = `S0 -> 1 -> 1 -> `B0 + `S0 -> 1 -> 2 -> `B0 +
            `S0 -> 2 -> 1 -> `B0 + `S0 -> 2 -> 2 -> `W0 + 
            `S1 -> 1 -> 1 -> `B0 + `S1 -> 1 -> 2 -> `B0 +
            `S1 -> 2 -> 1 -> `B0 + `S1 -> 2 -> 2 -> `B0
                                                        + `S1 -> 3 -> 3 -> `B0
}

pred canFlipDiagTR[prev: State, row, col: Int, post: State, row2, col2: Int] {
    -- The players cannot be the same
    prev.nextPlayer != post.nextPlayer

    -- row, col is where new piece is placed down
    -- row2, col2 is where a previously existing piece on the board is
    row2 < row
    sameMinorDiag[row, col, row2, col2]

    some rowEnd, colEnd: Int | {
        -- Checking only the top-right diagonal of row2 col2
        rowEnd < row2
        sameMinorDiag[row, col, rowEnd, colEnd]
        -- Must exist a piece to the top right that belongs to the player who just placed a piece down
        prev.board[rowEnd][colEnd] = prev.nextPlayer
        all rowBetween, colBetween: Int | {
            -- Checking all positions between rowEnd and row
            -- All pieces along the way must belong to the opposing player
            -- Must have piece at every step on the way
            (sameMinorDiag[row, col, rowBetween, colBetween] and
                rowBetween > rowEnd and rowBetween < row)
                => prev.board[rowBetween][colBetween] = post.nextPlayer
        }
    }
}

example someFlipDiagTR is {
    wellformed 
    some s: State | {
        some s.next
        canFlipDiagTR[s, 3, 0, s.next, 2, 1]
    }
} for {
    State = `S0 + `S1
    B = `B0
    W = `W0
    Player = B + W
    next = `S0 -> `S1
    nextPlayer = `S0 -> `B0 + `S1 -> `W0

    board = `S0 -> 1 -> 1 -> `B0 + `S0 -> 1 -> 2 -> `B0 +
            `S0 -> 2 -> 1 -> `W0 + `S0 -> 2 -> 2 -> `B0 + 
                                   `S1 -> 1 -> 1 -> `B0 + `S1 -> 1 -> 2 -> `B0 +
                                   `S1 -> 2 -> 1 -> `B0 + `S1 -> 2 -> 2 -> `B0 +
            `S0 -> 3 -> 0 -> `B0
}

pred canFlipDiagBL[prev: State, row, col: Int, post: State, row2, col2: Int] {
    -- The players cannot be the same
    prev.nextPlayer != post.nextPlayer

    -- row, col is where new piece is placed down
    -- row2, col2 is where a previously existing piece on the board is
    row2 > row
    sameMinorDiag[row, col, row2, col2]  // Minor diagonal

    some rowEnd, colEnd: Int | {
        -- Checking only the top-right diagonal of row2 col2
        rowEnd > row2
        sameMinorDiag[row, col, rowEnd, colEnd]
        -- Must exist a piece to the bottom left
        -- that belongs to the player who just placed a piece down
        prev.board[rowEnd][colEnd] = prev.nextPlayer
        all rowBetween, colBetween: Int | {
            -- Checking all positions between rowEnd and row
            -- All pieces along the way must belong to the opposing player
            -- Must have piece at every step on the way
            (sameMinorDiag[row, col, rowBetween, colBetween] and
                rowBetween < rowEnd and rowBetween > row)
                => prev.board[rowBetween][colBetween] = post.nextPlayer
        }
    }
}

/*
example someFlipDiagBL is {
    wellformed 
    some s: State | {
        some s.next
        canFlipDiagBL[s, 0, 3, s.next, 1, 2]
    }
} for {
    State = `S0 + `S1
    B = `B0
    W = `W0
    Player = B + W
    next = `S0 -> `S1
    nextPlayer = `S0 -> `B0 + `S1 -> `W0

    board = `S0 -> 1 -> 1 -> `B0 + `S0 -> 1 -> 2 -> `W0 +
            `S0 -> 2 -> 1 -> `B0 + `S0 -> 2 -> 2 -> `B0
                                                        + `S1 -> 0 -> 3 -> `B0
            `S1 -> 1 -> 1 -> `B0 + `S1 -> 1 -> 2 -> `B0 +
            `S1 -> 2 -> 1 -> `B0 + `S1 -> 2 -> 2 -> `B0
}*/


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

fun abs(x : Int): Int {
    (x >= 0) => x else subtract[0, x]
}

fun sign(x : Int): Int {
    (x > 0) => 1
        else {(x = 0) => 0 else -1}
}

fun offsetRC(row, offset, row2: Int) : Int {
    // offset units from (row, col) in the direction of (row2, col2)
    // Same operation on rows and columns
    (row < row2)
        => add[row, offset]
        else {
            (row = row2)
                => row
                else subtract[row, offset]
        }
}

pred offsetInbounds[row, offset, row2: Int] {
    (row < row2)
        => offset <= subtract[3, row]
        else {(row > row2) => offset <= subtract[row, 0]}
}

test expect {
    inboundsTest1: { offsetInbounds[0, 2, 3] } for 4 Int is sat
    inboundsTest2: { offsetInbounds[1, 2, 3] } for 4 Int is sat
    inboundsTest3: { offsetInbounds[3, 2, 0] } for 4 Int is sat
    inboundsTest4: { offsetInbounds[2, 2, 1] } for 4 Int is sat
    outboundsTest1: { offsetInbounds[2, 2, 3] } for 4 Int is unsat
    outboundsTest2: { offsetInbounds[1, 2, 0] } for 4 Int is unsat
}

fun absDiff(x, y: Int): Int {
    // calculates the absolute difference of x and y
    (x <= y) => {subtract[y, x]} else {subtract[x, y]}
}

pred canFlip[prev: State, row, col: Int, row2, col2: Int] {
    -- (row, col) and (row2, col2) are on the same row, column, or diagonal
    row = row2 or
    col = col2 or
    absDiff[row, row2] = absDiff[col, col2]
    not (row = row2 and col = col2)

    some p: Player | some o: Player | {
        p = prev.nextPlayer
        o != p

        -- There is some end element that is the same piece as the player just played
        -- (subtract[row2, row], subtract[col2, col]) give the direction. we multiply that by an integer
        some end: Int | {
            -- The end point must be beyond the (row2, col2)
            end > absDiff[row, row2]
            end > absDiff[col, col2]

            -- The resulting element is inbounds
            offsetInbounds[row, end, row2]
            offsetInbounds[col, end, col2]

            prev.board[offsetRC[row, end, row2]][offsetRC[col, end, col2]] = p

            -- All pieces between are the piece of the opposite player
            all bet: Int | {
                (bet > 0 and bet < end) implies
                    prev.board[offsetRC[row, bet, row2]][offsetRC[col, bet, col2]] = o
            }
        }
    }
}

pred onlyOneFlip[row, col, rowf, colf: Int] {
    // The placement at (row, col) only flips (rowf, colf)
    // For testing purposes
    some s: State | {
        all row2, col2: Int | {
            -- inbounds
            {inbounds[row2, col2]}
                => {(row2 = rowf and col2 = colf) <=> canFlip[s, row, col, row2, col2]}
}
    }
}


example canFlipOrthogonal is {
    wellformed 
    onlyOneFlip[1, 0, 1, 1]
    onlyOneFlip[0, 1, 1, 1]
    onlyOneFlip[2, 3, 2, 2]
    onlyOneFlip[3, 2, 2, 2]
} for {
    State = `S0
    B = `B0
    W = `W0
    Player = B + W
    nextPlayer = `S0 -> `B0

    board = `S0 -> 1 -> 1 -> `W0 + `S0 -> 1 -> 2 -> `B0 +
            `S0 -> 2 -> 1 -> `B0 + `S0 -> 2 -> 2 -> `W0
}

example canFlipTL is {wellformed and onlyOneFlip[3, 3, 2, 2]} for {
    State = `S0
    B = `B0
    W = `W0
    Player = B + W
    nextPlayer = `S0 -> `B0

    board = `S0 -> 1 -> 1 -> `B0 + `S0 -> 1 -> 2 -> `B0 +
            `S0 -> 2 -> 1 -> `B0 + `S0 -> 2 -> 2 -> `W0
}
example canFlipBL is {wellformed and onlyOneFlip[0, 3, 1, 2]} for {
    State = `S0
    B = `B0
    W = `W0
    Player = B + W
    nextPlayer = `S0 -> `B0

    board = `S0 -> 1 -> 1 -> `W0 + `S0 -> 1 -> 2 -> `W0 +
            `S0 -> 2 -> 1 -> `B0 + `S0 -> 2 -> 2 -> `W0
}
example canFlipTR is {wellformed and onlyOneFlip[3, 0, 2, 1]} for {
    State = `S0
    B = `B0
    W = `W0
    Player = B + W
    nextPlayer = `S0 -> `B0

    board = `S0 -> 1 -> 1 -> `B0 + `S0 -> 1 -> 2 -> `B0 +
            `S0 -> 2 -> 1 -> `W0 + `S0 -> 2 -> 2 -> `W0
}
example canFlipBR is {wellformed and onlyOneFlip[0, 0, 1, 1]} for {
    State = `S0
    B = `B0
    W = `W0
    Player = B + W
    nextPlayer = `S0 -> `B0

    board = `S0 -> 1 -> 1 -> `W0 + `S0 -> 1 -> 2 -> `W0 +
            `S0 -> 2 -> 1 -> `B0 + `S0 -> 2 -> 2 -> `B0
}

pred move[prev: State, row: Int, col: Int, post: State] {
    -- Guard
    -- The place where the next piece is placed is empty
    no prev.board[row][col]
    
    -- The player needs to change
    prev.nextPlayer != post.nextPlayer
    
    -- Only one piece was placed down
    --subtract[countPieces[post], countPieces[prev]] = 1
    
    -- Must have difference of at least 2 pieces between each board for current player as this implies that a piece was flipped
    some row2, col2: Int | {
        some prev.board[row2, col2]
        prev.board[row2, col2] != post.board[row2, col2]
    }

    all row2, col2: Int | {
        (inbounds[row2, col2]) => {
        (row = row2 and col = col2) => {
            -- Player placed down piece
            post.board[row2][col2] = prev.nextPlayer
        } else {
            -- Changed due to being able to flip the piece
                { canFlip[prev, row, col, row2, col2] }
                    => {
                        some post.board[row2, col2]
                        prev.board[row2][col2] != post.board[row2][col2]
                    }
                -- otherwise stays the same
                else prev.board[row2][col2] = post.board[row2][col2]
            }
        }
    }
}

-- this example is totally valid, but not contained in the run for some reason
-- we ran it specifying this instance as well, and it worked, but it just did not
-- appear in the final output
example canMoveFlipUp is {wellformed and trace} for {
    State = `S0 + `S1
    B = `B0
    W = `W0
    Player = B + W
    next = `S0 -> `S1
    nextPlayer = `S0 -> `B0 + `S1 -> `W0

    board = `S0 -> 1 -> 1 -> `W0 + `S0 -> 1 -> 2 -> `B0 +
            `S0 -> 2 -> 1 -> `B0 + `S0 -> 2 -> 2 -> `W0 + 
            `S1 -> 1 -> 1 -> `W0 + `S1 -> 1 -> 2 -> `B0 +
            `S1 -> 2 -> 1 -> `B0 + `S1 -> 2 -> 2 -> `B0
                                 + `S1 -> 3 -> 2 -> `B0
}

/*
pred validMove[prev: State, post: State] {
    // Check if the transition from previous state to the post state is valid
    {some row, col: Int | some s: State | move[prev, row, col, s]}
        => {some row, col: Int | move[prev, row, col, post]}
        else {
            all row, col: Int | { prev.board[row][col] = post.board[row][col] }
            prev.nextPlayer != post.nextPlayer
        }
}*/

pred trace {
    some init: State | {
        no s: State | { s.next = init }
        initState[init]
    }
    
    all s: State | {
        {some s.next} => {some row, col: Int | move[s, row, col, s.next]}
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

/*
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
}*/

run {
    wellformed
    trace
} for exactly 2 State, 4 Int for {
    State = `S0 + `S1
    B = `B0
    W = `W0
    Player = B + W
    next = `S0 -> `S1
    nextPlayer = `S0 -> `B0 + `S1 -> `W0

    board = `S0 -> 1 -> 1 -> `W0 + `S0 -> 1 -> 2 -> `B0 +
            `S0 -> 2 -> 1 -> `B0 + `S0 -> 2 -> 2 -> `W0 + 
            `S1 -> 1 -> 1 -> `W0 + `S1 -> 1 -> 2 -> `B0 +
            `S1 -> 2 -> 1 -> `B0 + `S1 -> 2 -> 2 -> `B0
                                 + `S1 -> 3 -> 2 -> `B0
}