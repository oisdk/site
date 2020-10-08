"use strict";

const Comb = {S: 0, K: 1, I: 2, B: 3, C: 4, A: 5, M: 6, T: 7, W: 8};
Object.freeze(Comb);

function make_comb_set(combs) {
    const res = new Set();
    combs.forEach(c => res.add(c));
    return res;
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
                    case 'S': return new Expr(mask.has(Comb.S) ? Comb.S : x.value);
                    case 'K': return new Expr(mask.has(Comb.K) ? Comb.K : x.value);
                    case 'I': return new Expr(mask.has(Comb.I) ? Comb.I : x.value);
                    case 'B': return new Expr(mask.has(Comb.B) ? Comb.B : x.value);
                    case 'C': return new Expr(mask.has(Comb.C) ? Comb.C : x.value);
                    case 'A': return new Expr(mask.has(Comb.A) ? Comb.A : x.value);
                    case 'M': return new Expr(mask.has(Comb.M) ? Comb.M : x.value);
                    case 'T': return new Expr(mask.has(Comb.T) ? Comb.T : x.value);
                    case 'W': return new Expr(mask.has(Comb.W) ? Comb.W : x.value);
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

function make_prompt(
    { input_par
    , input_width = 20
    , output_lines: n_lines
    , initial_expr
    }) {
    const lab = document.createElement("label");
    input_par.appendChild(lab)

    const prompt = document.createElement("code");
    prompt.innerHTML = ("λ> ");
    lab.appendChild(prompt);

    const inp = document.createElement("input");
    inp.type = "text";
    inp.value = initial_expr;
    inp.size = input_width;
    lab.appendChild(inp);

    const out = document.createElement("pre");
    for (let i = 0; i < n_lines; i++) {
        out.innerHTML += "\n";
    }
    input_par.appendChild(out);

    return {inp, out};
}

function small_repl(
    { input_id: p_id
    , input_width = 20
    , output_lines: n_lines
    , initial_expr
    , allowed_combos: combo_set
    }) {

    const par = document.getElementById(p_id);

    const {inp, out} =
        make_prompt({
            input_par: par, 
            input_width: input_width, 
            output_lines: n_lines,
            initial_expr: initial_expr
        });

    let initial = null;
    let stored = null;
    let lines = [];

    inp.addEventListener("keydown", function (event) {
        if (event.key === "Enter") {
            let new_expr = inp.value;
            if (new_expr != initial) {
                initial = new_expr;
                stored = Expr.parse(combo_set, initial);
                lines = [];
            }
            if (stored !== null) {
                if (lines.length === 0 || stored.step()) {
                    lines.push("~> " + stored.show());
                    if (lines.length > n_lines) {
                        lines.shift();
                    }
                }
            }
            out.innerHTML = "";
            for (let i = 0; i < n_lines; i++) {
                if (i < lines.length) {
                    out.innerHTML += lines[i];
                }
                out.innerHTML += "\n";
            }
        }
    })
}

function small_tester(
    { input_id: p_id
    , input_width = 20
    , output_lines: n_lines
    , initial_expr
    , vars
    , expect
    , allowed_combos: combo_set
    }) {
    const expect_expr = Expr.parse(combo_set, expect);

    const par = document.getElementById(p_id);

    const {inp, out} =
        make_prompt({
            input_par: par, 
            input_width: input_width, 
            output_lines: n_lines,
            initial_expr: initial_expr
        });

    const vsp = document.createElement("code");
    vsp.innerHTML = vars + " ~> " + expect;
    par.insertBefore(vsp, out);

    const check_correct = (e) => 
        (e.equals(expect_expr) ? "✓  " : "~> ") + e.show();

    let initial = null;
    let stored = null;
    let lines = [];
    
    inp.addEventListener("keydown", function(event) {
        if (event.key === "Enter") {
            event.preventDefault();
            let new_expr = inp.value;
            let given = Expr.parse(combo_set, new_expr);
            if (given === null || given.free_vars()) {
                return;
            }

            if (new_expr != initial) {
                initial = new_expr;
                stored = Expr.parse(combo_set, initial + vars);
                lines = [];
            }

            if (stored !== null) {
                if (lines.length === 0 || stored.step()) {
                    lines.push(check_correct(stored));
                    if (lines.length > n_lines) {
                        lines.shift();
                    }
                } else if (!(stored.equals(expect_expr))) {
                    lines.pop();
                    lines.push("✗  " + stored.show());
                }
            }
            out.innerHTML = "";
            for (let i = 0; i < n_lines; i++) {
                if (i < lines.length) {
                    out.innerHTML += lines[i];
                }
                out.innerHTML += "\n";
            }
        }
    })
}
