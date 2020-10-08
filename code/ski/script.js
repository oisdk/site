"use strict";

const Comb = {S: 0, K: 1, I: 2, B: 3, C: 4, A: 5, M: 6, T: 7, W: 8};
Object.freeze(Comb);

function make_comb_set(combs) {
    return combs.reduce((mask, c) => (mask | (1 << c)), 0);
}

function in_comb_set(mask, comb) {
    return ((mask & (1 << comb)) != 0);
}

class Expr {
    constructor(op) {
        this.op = op;
        this.stack = [];
    }

    clone() {
        const res = new Expr(this.op);
        for (const x of this.stack) {
            res.stack.push(x.clone());
        }
        return res;
    }

    equals(other) {
        if (this.op != other.op) {
            return false;
        }
        if (this.stack.length != other.stack.length) {
            return false;
        }
        for (let i = 0; i < this.stack.length; i++) {
            if (!(this.stack[i].equals(other.stack[i]))) {
                return false;
            }
        }
        return true;
    }

    step() {
        let x, y, z;
        switch(this.op) {
            case Comb.S:
                if (this.stack.length<3) {
                    return false;
                }
                [x, y, z] = [this.stack.pop(), this.stack.pop(), this.stack.pop()];
                y.stack.unshift(z);
                this.stack.push(y);
                this.stack.push(z.clone());
                break;
            case Comb.K:
                if (this.stack.length<2) {
                    return false;
                }
                [x, y] = [this.stack.pop(), this.stack.pop()];
                break;
            case Comb.I:
                if (this.stack.length<1) {
                    return false;
                }
                x = this.stack.pop();
                break;
            case Comb.B:
                if (this.stack.length<3) {
                    return false;
                }
                [x, y, z] = [this.stack.pop(), this.stack.pop(), this.stack.pop()];
                y.stack.unshift(z);
                this.stack.push(y);
                break;
            case Comb.C:
                if (this.stack.length<3) {
                    return false;
                }
                [x, y, z] = [this.stack.pop(), this.stack.pop(), this.stack.pop()];
                this.stack.push(y);
                this.stack.push(z);
                break;
            case Comb.A:
                if (this.stack.length<2) {
                    return false;
                }
                [y, x] = [this.stack.pop(), this.stack.pop()];
                break;
            case Comb.M:
                if (this.stack.length<1) {
                    return false;
                }
                x = this.stack.pop()
                this.stack.push(x.clone())
                break;
            case Comb.T:
                if (this.stack.length<2) {
                    return false;
                }
                [y, x] = [this.stack.pop(), this.stack.pop()];
                this.stack.push(y)
                break;
            case Comb.W:
                if (this.stack.length<2) {
                    return false;
                }
                [x, y] = [this.stack.pop(), this.stack.pop()];
                this.stack.push(y);
                this.stack.push(y.clone());
                break;
            default: return false;
        }
        for (const xe of x.stack) {
            this.stack.push(xe);
        }
        this.op = x.op;
        return true;
    }

    show() {
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
                case Comb.W: yield 'W'; break;
                default: yield expr.op;
            }
            for (let i = expr.stack.length - 1; i >= 0; i--) {
                yield* display_helper(expr.stack[i],true);
            }
            if ((expr.stack.length>0)&&(parens)) {
                yield ')';
            }
        }
        let res = '';
        for (const x of display_helper(this, false)) {
            res = res + x;
        }
        return res;
    }

    static parse(combos, string) {

        const mask = make_comb_set(combos);
        const inp  = string[Symbol.iterator]();

        function parse_ski_single() {
            while (true) {
                let x = inp.next();
                if (x.done) {
                    return null;
                }
                switch (x.value) {
                    case '(': return parse_ski_many();
                    case ')': return null;
                    case 'S': return new Expr(in_comb_set(mask, Comb.S) ? Comb.S : x.value);
                    case 'K': return new Expr(in_comb_set(mask, Comb.K) ? Comb.K : x.value);
                    case 'I': return new Expr(in_comb_set(mask, Comb.I) ? Comb.I : x.value);
                    case 'B': return new Expr(in_comb_set(mask, Comb.B) ? Comb.B : x.value);
                    case 'C': return new Expr(in_comb_set(mask, Comb.C) ? Comb.C : x.value);
                    case 'A': return new Expr(in_comb_set(mask, Comb.A) ? Comb.A : x.value);
                    case 'M': return new Expr(in_comb_set(mask, Comb.M) ? Comb.M : x.value);
                    case 'T': return new Expr(in_comb_set(mask, Comb.T) ? Comb.T : x.value);
                    case 'W': return new Expr(in_comb_set(mask, Comb.W) ? Comb.W : x.value);
                    case ' ': break;
                    default: return new Expr(x.value);
                }
            }
        }

        function parse_ski_many() {
            let res = parse_ski_single();
            if (res === null) {
                return null;
            }
            let next_arg = parse_ski_single();
            while (next_arg !== null) {
                res.stack.push(next_arg);
                next_arg = parse_ski_single();
            }
            return res;
        }

        function reverse_all(expr) {
            expr.stack.reverse();
            expr.stack.forEach(reverse_all);
        }
        
        const res = parse_ski_many();
        
        if (res === null) {
            return null;
        }
        reverse_all(res);
        return res;
    }

    free_vars() {
        return (typeof this.op === 'string') || this.stack.some(e => e.free_vars());
    }
}

function small_repl({input_id: p_id, output_lines: n_lines, initial_expr, allowed_combos: combo_set}) {
    const par = document.getElementById(p_id);

    const inp = document.createElement("input");
    inp.type = "text";
    inp.value = initial_expr;
    par.appendChild(inp);

    const button = document.createElement("input");
    button.type = "button";
    button.value = "step";
    par.appendChild(button);

    inp.addEventListener("keyup", function(event) {
        if (event.keyCode === 13) {
            event.preventDefault();
            button.click();
        }
    })

    const out = document.createElement("pre");
    for (let i = 0; i < n_lines; i++) {
        out.innerHTML += "\n";
    }
    par.appendChild(out);

    let initial = null;
    let stored = null;
    let lines = [];
    button.addEventListener("click", function () {
        let new_expr = inp.value;
        if (new_expr != initial) {
            initial = new_expr;
            stored = Expr.parse(combo_set, initial);
            lines = [];
        }
        if ( (stored !== null) && stored.step() ) {
            lines.push("~> " + stored.show());
            if (lines.length > n_lines) {
                lines.shift();
            }
        }
        if ((stored !== null) && (lines.length == 0)) {
            lines.push("~> " + stored.show());
        }
        out.innerHTML = "";
        for (let i = 0; i < n_lines; i++) {
            if (i < lines.length) {
                out.innerHTML += lines[i];
            }
            out.innerHTML += "\n";
        }
    })
}

function small_tester({input_id: p_id, output_lines: n_lines, initial_expr, vars, expect, allowed_combos: combo_set}) {
    const expect_expr = Expr.parse(combo_set, expect);

    const par = document.getElementById(p_id);

    const inp = document.createElement("input");
    inp.type = "text";
    inp.value = initial_expr;
    par.appendChild(inp);

    const vsp = document.createElement("code");
    vsp.innerHTML = vars;
    par.appendChild(vsp);

    const button = document.createElement("input");
    button.type = "button";
    button.value = "step";
    par.appendChild(button);

    inp.addEventListener("keyup", function(event) {
        if (event.keyCode === 13) {
            event.preventDefault();
            button.click();
        }
    })

    const out = document.createElement("pre");
    out.innerHTML = "\n".repeat(n_lines);
    par.appendChild(out);

    const targ = document.createElement("pre");
    targ.innerHTML = "target: " + expect;
    par.appendChild(targ);

    function check_correct(candidate) {
        if (candidate.equals(expect_expr)) {
            return ("✓  " + candidate.show());
        } else {
            return ("~> " + candidate.show());
        }
    }

    let initial = null;
    let stored = null;
    let lines = [];
    
    button.addEventListener("click", function () {
        let new_expr = inp.value;
        let given = Expr.parse(combo_set, new_expr);
        if ((given === null) || (given.free_vars())) {
            return;
        }

        if (new_expr != initial) {
            initial = new_expr;
            stored = Expr.parse(combo_set, initial + vars);
            lines = [];
        }
        if (stored !== null) {
            if (stored.step()) {
                lines.push(check_correct(stored));
                if (lines.length > n_lines) {
                    lines.shift();
                }
            } else {
                if (!(stored.equals(expect_expr))) {
                    lines.pop();
                    lines.push("✗  " + stored.show());
                }
            }
        }
        if ((stored !== null) && (lines.length == 0)) {
            lines.push(check_correct(stored));
        }
        out.innerHTML = "";
        for (let i = 0; i < n_lines; i++) {
            if (i < lines.length) {
                out.innerHTML += lines[i];
            }
            out.innerHTML += "\n";
        }
    })
}
