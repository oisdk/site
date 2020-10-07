const Comb = {S: 0, K: 1, I: 2, B: 3, C: 4, A: 5, M: 6, T: 7};
Object.freeze(Comb);

function clone(expr) {
    let res = {op: expr.op, stack: []};
    for (const x of expr.stack) {
        res.stack.push(clone(x));
    }
    return res;
}

function step(expr) {
    let x, y, z;
    switch(expr.op) {
        case Comb.S:
            if (expr.stack.length<3) {
                return false;
            }
            [x, y, z] = [expr.stack.pop(), expr.stack.pop(), expr.stack.pop()];
            y.stack.unshift(z);
            expr.stack.push(y);
            expr.stack.push(clone(z));
            break;
        case Comb.K:
            if (expr.stack.length<2) {
                return false;
            }
            [x, y] = [expr.stack.pop(), expr.stack.pop()];
            break;
        case Comb.I:
            if (expr.stack.length<1) {
                return false;
            }
            x = expr.stack.pop();
            break;
        case Comb.B:
            if (expr.stack.length<3) {
                return false;
            }
            [x, y, z] = [expr.stack.pop(), expr.stack.pop(), expr.stack.pop()];
            y.stack.unshift(z);
            expr.stack.push(y);
            break;
        case Comb.C:
            if (expr.stack.length<3) {
                return false;
            }
            [x, y, z] = [expr.stack.pop(), expr.stack.pop(), expr.stack.pop()];
            expr.stack.push(y);
            expr.stack.push(z);
            break;
        case Comb.A:
            if (expr.stack.length<2) {
                return false;
            }
            [y, x] = [expr.stack.pop(), expr.stack.pop()];
            break;
        case Comb.M:
            if (expr.stack.length<1) {
                return false;
            }
            x = expr.stack.pop()
            expr.stack.push(clone(x))
            break;
        case Comb.T:
            if (expr.stack.length<2) {
                return false;
            }
            [y, x] = [expr.stack.pop(), expr.stack.pop()];
            expr.stack.push(y)
            break;
        default: return false;
    }
    for (const xe of x.stack) {
        expr.stack.push(xe);
    }
    expr.op = x.op;
    return true;
}

function* display_helper(expr, parens) {
    if ((expr.stack.length>0)&&(parens)) {
        yield '(';
    }
    switch(expr.op) {
        case Comb.S: yield 'S'; break;
        case Comb.K: yield 'K'; break;
        case Comb.I: yield 'I'; break;
        case Comb.B: yield 'B'; break;
        case Comb.C: yield 'C'; break;
        case Comb.A: yield 'A'; break;
        case Comb.M: yield 'M'; break;
        case Comb.T: yield 'T'; break;
        default: yield expr.op;
    }
    for (let i = expr.stack.length - 1; i >= 0; i--) {
        yield* display_helper(expr.stack[i],true);
    }
    if ((expr.stack.length>0)&&(parens)) {
        yield ')';
    }
}

function show_expr(expr) {
    res = '';
    for (const x of display_helper(expr, false)) {
        res = res + x;
    }
    return res;
}

function parse_ski_single(inp, mask) {
    while (true) {
        let x = inp.next();
        if (x.done) {
            return null;
        }
        switch (x.value) {
            case '(': return parse_ski_many(inp, mask);
            case ')': return null;
            case 'S': return {op: (((mask & (1 << Comb.S)) != 0) ? Comb.S : x.value), stack: []};
            case 'K': return {op: (((mask & (1 << Comb.K)) != 0) ? Comb.K : x.value), stack: []};
            case 'I': return {op: (((mask & (1 << Comb.I)) != 0) ? Comb.I : x.value), stack: []};
            case 'B': return {op: (((mask & (1 << Comb.B)) != 0) ? Comb.B : x.value), stack: []};
            case 'C': return {op: (((mask & (1 << Comb.C)) != 0) ? Comb.C : x.value), stack: []};
            case 'A': return {op: (((mask & (1 << Comb.A)) != 0) ? Comb.A : x.value), stack: []};
            case 'M': return {op: (((mask & (1 << Comb.M)) != 0) ? Comb.M : x.value), stack: []};
            case 'T': return {op: (((mask & (1 << Comb.T)) != 0) ? Comb.T : x.value), stack: []};
            case ' ': break;
            default: return {op: x.value, stack: []};
        }
    }
}

function reverse_all(expr) {
    expr.stack.reverse();
    for (const x of expr.stack) {
        reverse_all(x);
    }
}

function parse_ski_many(inp, mask) {
    let res = parse_ski_single(inp, mask);
    if (res === null) {
        return null;
    }
    let next_arg = parse_ski_single(inp, mask);
    while (next_arg !== null) {
        res.stack.push(next_arg);
        next_arg = parse_ski_single(inp, mask);
    }
    return res;
}

function parse_ski(combo_set, string) {
    let mask = 0;
    for (const c of combo_set) {
        mask |= (1 << c);
    }
    const res = parse_ski_many(string[Symbol.iterator](), mask);
    reverse_all(res);
    return res
}

function steps(expr) {
    while (step(expr)) {
      console.log(show_expr(expr));
    }
}

function small_repl(p_id, n_lines, def_val, ...combo_set) {
    const par = document.getElementById(p_id);

    const inp = document.createElement("input");
    inp.type = "text";
    inp.value = def_val;
    par.appendChild(inp);

    const button = document.createElement("input");
    button.type = "button";
    button.value = "step";
    par.appendChild(button);

    const out = document.createElement("pre");
    for (let i = 0; i < n_lines; i++) {
        out.innerHTML += ">\n";
    }
    par.appendChild(out);

    let initial = null;
    let stored = null;
    let lines = [];
    button.addEventListener("click", function () {
        let new_expr = inp.value;
        if (new_expr != initial) {
            initial = new_expr;
            stored = parse_ski(combo_set, initial);
            lines = [];
        }
        if ((stored !== null) && step(stored)) {
            lines.push("> " + show_expr(stored));
            if (lines.length > n_lines) {
                lines.shift();
            }
        }
        if ((stored !== null) && (lines.length == 0)) {
            lines.push("> " + show_expr(stored));
        }
        out.innerHTML = "";
        for (let i = 0; i < n_lines; i++) {
            if (i < lines.length) {
                out.innerHTML += lines[i];
            } else {
                out.innerHTML += "> ";
            }
            out.innerHTML += "\n";
        }
    })
}

