const d3 = require('d3')
d3.selectAll("svg > *").remove();

function printValue(row, col, yoffset, value) {
    d3.select(svg)
        .append("text")
        .style("fill", "black")
        .attr("x", (row + 1) * 15)
        .attr("y", (col + 1) * 15 + yoffset)
        .text(value);
}

function printState(stateAtom, yoffset) {
    for (r = 0; r <= 3; r++) {
        for (c = 0; c <= 3; c++) {
            printValue(r, c, yoffset,
                stateAtom.board[r][c]
                    .toString().substring(0, 1))
        }
    }

    d3.select(svg)
        .append('rect')
        .attr('x', 10)
        .attr('y', yoffset + 1)
        .attr('width', 70)
        .attr('height', 70)
        .attr('stroke-width', 2)
        .attr('stroke', 'black')
        .attr('fill', 'transparent');
}


var offset = 0
for (b = 0; b <= 3; b++) {
    if (State.atom("State" + b) != null)
        printState(State.atom("State" + b), offset)
    offset = offset + 80
}
