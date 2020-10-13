"use strict";

const Comb = {S: 0, K: 1, I: 2, B: 3, C: 4, A: 5, M: 6, T: 7, W: 8};
Object.freeze(Comb);

function make_comb_set(combs) {
    const res = new Set();
    combs.forEach(c => res.add(c));
    return res;
}

function show_comb(comb) {
    switch(comb) {
        case Comb.S: return 'S';
        case Comb.K: return 'K';
        case Comb.I: return 'I';
        case Comb.B: return 'B';
        case Comb.C: return 'C';
        case Comb.A: return 'A';
        case Comb.M: return 'M';
        case Comb.T: return 'T';
        case Comb.W: return 'W';
        default: return null;
    }
}

class Expr {
    constructor(op, stack = []) {
        this.op = op;
        this.stack = stack;
    }

    map(f) {
        return new Expr(f(this.op), this.stack.map(x => x.map(f)));
    }

    bind(f) {
        const clos = f(this.op);
        const out_stack = this.stack.map(x => x.bind(f));
        const out = new Expr(clos.op, out_stack);
        for (const x of clos.stack) {
            out.stack.push(x);
        }
        return out;
    }

    clone() {
        return this.map(x => x);
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
                x = this.stack.pop();
                this.stack.push(x.clone());
                break;
            case Comb.T:
                if (this.stack.length<2) {
                    return false;
                }
                [y, x] = [this.stack.pop(), this.stack.pop()];
                this.stack.push(y);
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

    step_normal() {
        if (this.step()) {
            return true;
        }
        for (let i = this.stack.length - 1; i >= 0; i--) {
            if (this.stack[i].step_normal()) {
                return true;
            }
        }
        return false;
    }

    steps() {
        console.log(this.show());
        while (this.step_normal()) {
            console.log(this.show());
        }
    }

    show() {
        function* display_helper(expr, parens) {
            if ((expr.stack.length>0)&&(parens)) {
                yield '(';
            }
            yield show_comb(expr.op) ?? expr.op;
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

    conv_combos(combos) {
        const combo_strs = new Map();
        for (const x of combos) {
            combo_strs.set(show_comb(x), x);
        }
        return this.map(x => combo_strs.has(x) ? combo_strs.get(x) : x);
    }

    static parse(string) {

        function* tokens() {
            const str = string[Symbol.iterator]();
            let cur_num = null;

            function* cur_num_yield() {
                if (cur_num !== null) {
                    yield cur_num;
                    cur_num = null;
                }
            }

            let c = str.next();

            while (!(c.done)) {
                switch (c.value) {
                    case '(': yield* cur_num_yield(); yield '('; break;
                    case ')': yield* cur_num_yield(); yield ')'; break;
                    case ' ': yield* cur_num_yield(); break;
                    case '0' : cur_num = (cur_num === null) ? 0 : 10 * cur_num; break;
                    case '1' : cur_num = (cur_num === null) ? 1 : 1 + 10 * cur_num; break;
                    case '2' : cur_num = (cur_num === null) ? 2 : 2 + 10 * cur_num; break;
                    case '3' : cur_num = (cur_num === null) ? 3 : 3 + 10 * cur_num; break;
                    case '4' : cur_num = (cur_num === null) ? 4 : 4 + 10 * cur_num; break;
                    case '5' : cur_num = (cur_num === null) ? 5 : 5 + 10 * cur_num; break;
                    case '6' : cur_num = (cur_num === null) ? 6 : 6 + 10 * cur_num; break;
                    case '7' : cur_num = (cur_num === null) ? 7 : 7 + 10 * cur_num; break;
                    case '8' : cur_num = (cur_num === null) ? 8 : 8 + 10 * cur_num; break;
                    case '9' : cur_num = (cur_num === null) ? 9 : 9 + 10 * cur_num; break;
                    default: yield* cur_num_yield(); yield c.value;
                }
                c = str.next();
            }
            yield* cur_num_yield();
        }

        const inp = tokens()[Symbol.iterator]();

        let parens = 0;

        function parse_ski_single() {
            while (true) {
                let x = inp.next();
                if (x.done) {
                    return null;
                }
                switch (x.value) {
                    case '(': 
                        parens++;
                        return parse_ski_many();
                    case ')':
                        if (--parens < 0) {
                            throw new EvalError();
                        }
                        return null;
                    default: return new Expr(x.value);
                }
            }
        }

        function parse_ski_many() {
            let res = parse_ski_single();
            if (res === null) {
                throw new EvalError();
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

        var res = null;

        try {
            res = parse_ski_many();
        } catch (e) {
            if (e instanceof EvalError) {
                return null;
            } else {
                throw e;
            }
        }
        
        if (res === null || parens !== 0) {
            return null;
        }
        reverse_all(res);
        return res;
    }

    static number(n) {
        const res = new Expr("error: internal bug");
        let cur = res;

        while (true) {
            switch (n) {
                case 0: 
                    cur.op = Comb.A;
                    return res;
                case 1: 
                    cur.op = Comb.I;
                    return res;
                case 2:
                    cur.op = Comb.W;
                    cur.stack = [new Expr(Comb.B)];
                    return res;
                case 3:
                    cur.op = Comb.S;
                    cur.stack = [new Expr(Comb.W, [new Expr(Comb.B)]), new Expr(Comb.B)];
                    return res;
                default: 
                    if (n % 2 === 1) {
                        cur.op = Comb.S;
                        cur.stack = [new Expr("error: internal bug"), new Expr(Comb.B)];
                        cur = cur.stack[0];
                        n--;
                    }
                    cur.op = Comb.B;
                    cur.stack = [new Expr("error: internal bug"), new Expr(Comb.W, [new Expr(Comb.B)])];
                    cur = cur.stack[0];
                    n /= 2;
            }
        }
    }

    get_numbers() {
        return this.bind(x => (typeof x === 'number') ? Expr.number(x) : new Expr(x))
    }

    get_definitions(dict) {
        return this.bind(x => dict.has(x) ? dict.get(x) : new Expr(x));
    }
}

function make_prompt(
    { input_par
    , output_lines: n_lines
    , initial_expr
    }) {
    const lab = document.createElement("label");
    input_par.appendChild(lab);

    const prompt = document.createElement("code");
    prompt.innerHTML = ("λ> ");
    lab.appendChild(prompt);

    const inp = document.createElement("input");
    inp.type = "text";
    inp.value = initial_expr;
    lab.appendChild(inp);

    const out = document.createElement("code");
    out.innerHTML = "<br>".repeat(n_lines+1);
    input_par.appendChild(out);

    return {inp, out};
}

function repl(
    { input_id: p_id
    , output_lines: n_lines = 5
    , initial_expr = ""
    , normal = false
    , allowed_combos: combo_set =
      [ Comb.S
      , Comb.K
      , Comb.I
      , Comb.B
      , Comb.C
      , Comb.A 
      , Comb.M 
      , Comb.T 
      , Comb.W
      ]
    , allow_numbers = false
    }) {

    const par = document.getElementById(p_id);

    const {inp, out} =
        make_prompt({
            input_par: par, 
            output_lines: n_lines,
            initial_expr: initial_expr
        });

    inp.pattern = "([" + combo_set.map(show_comb).join('') + "]| |\\(|\\)|[a-z]" + (allow_numbers ? "|[0-9]" : "") + ")+";

    let initial = null;
    let stored = null;
    let lines = [];

    inp.addEventListener("input", function () {
        inp.setCustomValidity("");
    });

    inp.addEventListener("keydown", function (event) {
        if (event.key === "Enter") {
            event.preventDefault();
            if (inp.validity.patternMismatch) {
                return;
            }
            let new_expr = inp.value;

            if (new_expr != initial) {
                initial = new_expr;
                stored = Expr.parse(initial)
                if (allow_numbers) {
                    stored = stored.get_numbers();
                }
                stored = stored.conv_combos(combo_set);
                lines = [];
            }
            if (stored !== null) {
                if (lines.length === 0 || (!normal && stored.step()) || (normal && stored.step_normal())) {
                    lines.push("~> " + stored.show());
                    if (lines.length > n_lines) {
                        lines.shift();
                    }
                }
            } else {
                inp.setCustomValidity("invalid");
            }
            out.innerHTML = "<br>";
            for (let i = 0; i < n_lines; i++) {
                if (i < lines.length) {
                    out.innerHTML += lines[i];
                }
                out.innerHTML += "<br>";
            }
        }
    });
}

function puzzle(
    { input_id: p_id
    , output_lines: n_lines = 5
    , initial_expr = ""
    , normal = false
    , vars
    , expect
    , allowed_combos: combo_set =
      [ Comb.S
      , Comb.K
      , Comb.I
      , Comb.B
      , Comb.C
      , Comb.A 
      , Comb.M 
      , Comb.T 
      , Comb.W
      ]
    }) {
    const expect_expr = Expr.parse(expect).conv_combos(combo_set);

    const par = document.getElementById(p_id);

    const {inp, out} =
        make_prompt({
            input_par: par, 
            output_lines: n_lines,
            initial_expr: initial_expr
        });

    const combo_letters = combo_set.map(show_comb).join('');

    inp.pattern = "([" + combo_letters + "]| |\\(|\\))+";
    inp.placeholder = "?";

    const vsp = document.createElement("par");
    vsp.innerHTML = 
      `&#8226; Find a <code>?</code> such that <code>?${vars} ~> ${expect}</code>, using only the combinators <code>${combo_letters}</code>.<br>`;
    par.insertBefore(vsp, inp.parentElement);

    const check_correct = (e) => 
        (e.equals(expect_expr) ? "✓&nbsp;&nbsp;" : "~> ") + e.show();

    let initial = null;
    let stored = null;
    let lines = [];

    inp.addEventListener("input", function () {
        inp.setCustomValidity("");
    });
    
    inp.addEventListener("keydown", function(event) {
        if (event.key === "Enter") {
            event.preventDefault();
            if (inp.validity.patternMismatch) {
                return;
            }
            let new_expr = inp.value;

            if (Expr.parse(new_expr) === null) {
                inp.setCustomValidity("invalid");
                return;
            }

            if (new_expr != initial) {
                initial = new_expr;
                stored = Expr.parse(initial + vars).conv_combos(combo_set);
                lines = [];
            }

            if (stored !== null) {
                if (lines.length === 0 || (!normal && stored.step()) || (normal && stored.step_normal())) {
                    lines.push(check_correct(stored));
                    if (lines.length > n_lines) {
                        lines.shift();
                    }
                } else if (!(stored.equals(expect_expr))) {
                    lines.pop();
                    lines.push("✗&nbsp;&nbsp;" + stored.show());
                }
            }
            out.innerHTML = "<br>";
            for (let i = 0; i < n_lines; i++) {
                if (i < lines.length) {
                    out.innerHTML += lines[i];
                }
                out.innerHTML += "<br>";
            }
        }
    });
}
