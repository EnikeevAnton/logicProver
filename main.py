import re
import logic_help


# Аксиомы
AXIOMS = {
    'A1': "A->(B->A)",
    'A2': "(A->(B->C))->((A->B)->(A->C))",
    'A3': "((~B)->(~A))->(((~B)->A)->B)"
}

# --- 1. Классы данных ---

class Formula:
    def __init__(self, kind, left=None, right=None, name=None):
        self.kind = kind
        self.left = left
        self.right = right
        self.name = name
    
    def __str__(self):
        if self.kind == 'var': return self.name
        if self.kind == 'not':
            inner = str(self.left)
            if self.left.kind == 'imp': return "~(" + inner + ")"
            return "~" + inner
        if self.kind == 'imp':
            return "(" + str(self.left) + "->" + str(self.right) + ")"
        return "?"

    def __eq__(self, other):
        if not isinstance(other, Formula): return False
        if self.kind != other.kind: return False
        if self.kind == 'var': return self.name == other.name
        if self.kind == 'not': return self.left == other.left
        return self.left == other.left and self.right == other.right

    def __hash__(self):
        if self.kind == 'var': return hash(('var', self.name))
        if self.kind == 'not': return hash(('not', self.left))
        return hash(('imp', self.left, self.right))

class Parser:
    pattern = re.compile(r'\s*(->|~|\(|\)|[A-Za-z0-9_]+)')
    def __init__(self):
        self.tokens = []
        self.pos = 0 

    def parse(self, s):
        self.tokens = [m.group(1) for m in Parser.pattern.finditer(s)]
        self.pos = 0
        return self._parse_imp()

    def _consume(self):
        t = self.tokens[self.pos]
        self.pos += 1
        return t
    def _peek(self): return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def _parse_imp(self):
        left = self._parse_neg()
        if self._peek() == '->':
            self._consume()
            right = self._parse_imp()
            return Formula('imp', left, right)
        return left

    def _parse_neg(self):
        if self._peek() == '~':
            self._consume()
            return Formula('not', left=self._parse_neg())
        if self._peek() == '(':
            self._consume()
            n = self._parse_imp()
            self._consume() # )
            return n
        return Formula('var', name=self._consume())

class Axiom:
    def __init__(self, name, schema_str, parser):
        self.name = name
        self.schema = parser.parse(schema_str)
        
    def match(self, formula):
        return self._match_rec(self.schema, formula, {})

    def _match_rec(self, pat, tgt, env):
        if pat.kind == 'var' and len(pat.name) == 1 and pat.name.isupper():
            if pat.name in env: return env if env[pat.name] == tgt else None
            return {**env, pat.name: tgt}
        if pat.kind != tgt.kind: return None
        if pat.kind == 'var': return env if pat.name == tgt.name else None
        if pat.kind == 'not': return self._match_rec(pat.left, tgt.left, env)
        l_env = self._match_rec(pat.left, tgt.left, env)
        if l_env is None: return None
        return self._match_rec(pat.right, tgt.right, l_env)

# --- 2. Класс Proof ---

class Proof:
    def __init__(self, axioms):
        self.lines = [] # (formula, text)
        self.axioms = axioms
    
    def add_line(self, f, text):
        self.lines.append((f, text))
    
    def extend(self, other):
        self.lines.extend(other.lines)
            
    def __str__(self):
        if not self.lines: return "Empty"
        
        # Запускаем фикс индексов перед печатью
        self.fix_mp_indices()
        
        max_len = max(len(str(line[0])) for line in self.lines)
        col_w = max_len + 4
        res = ""
        for i, (f, text) in enumerate(self.lines):
            res += f"{str(i).ljust(4)}{str(f).ljust(col_w)}[{text}]\n"
        return res

    def fix_mp_indices(self):
        """
        Проходит по доказательству и проставляет реальные индексы для MP.
        Ищет формулы P и P->Q для каждого шага Q, помеченного как MP.
        """
        for i in range(len(self.lines)):
            formula, text = self.lines[i]
            
            if "MP" in text and "из" not in text:
                target = formula
                
                found_premise = -1
                found_imp = -1
                
                for j in range(i - 1, -1, -1):
                    cand_formula = self.lines[j][0]
                    
                    if cand_formula.kind == 'imp' and cand_formula.right == target:
                        possible_premise = cand_formula.left
                        
                        for k in range(i - 1, -1, -1):
                            if self.lines[k][0] == possible_premise:
                                found_imp = j
                                found_premise = k
                                break
                        
                        if found_imp != -1:
                            break
                            
                if found_imp != -1 and found_premise != -1:
                    # Обновляем текст строки
                    new_text = f"{text} из {found_premise} и {found_imp}"
                    self.lines[i] = (formula, new_text)

# --- 3. Логика Доказательства ---

def transform_deduction(subproof, A, axioms):
    new_proof = Proof(axioms)
    for f, text in subproof.lines:
        is_target = (f == A and "Гипотеза" in text and "|_" not in text)
        
        if is_target:
            new_text = f"|_ {text.strip()}"
        else:
            new_text = f"|  {text}"
        new_proof.add_line(f, new_text)
        
    if subproof.lines:
        B = subproof.lines[-1][0]
        new_proof.add_line(Formula('imp', A, B), f"Дедукция ({A} -> ...)")
    else:
        new_proof.add_line(Formula('imp', A, A), "Дедукция")
    return new_proof

def solve_contradiction(proof, goal, H, not_H_idx, H_idx):
    not_H = proof.lines[not_H_idx][0]
    H_val = proof.lines[H_idx][0]
    not_Goal = None
    if goal.kind == 'not':
        not_Goal = goal.left
    else:
        not_Goal = Formula('not', goal)
    
    # 1. ~H -> (~Goal -> ~H)
    s1 = Formula('imp', not_H, Formula('imp', not_Goal, not_H))
    proof.add_line(s1, "Инстанция A1")
    
    # 2. ~Goal -> ~H
    s2 = Formula('imp', not_Goal, not_H)
    proof.add_line(s2, "MP") 
    
    # 3. H -> (~Goal -> H)
    s3 = Formula('imp', H_val, Formula('imp', not_Goal, H_val))
    proof.add_line(s3, "Инстанция A1")
    
    # 4. ~Goal -> H
    s4 = Formula('imp', not_Goal, H_val)
    proof.add_line(s4, "MP")
    
    # 5. A3
    ax3 = Formula('imp', s2, Formula('imp', s4, goal))
    proof.add_line(ax3, "Инстанция A3")
    
    # 6. (~Goal -> H) -> Goal
    s6 = ax3.right
    proof.add_line(s6, "MP")
    
    # 7. Goal
    proof.add_line(goal, "MP")
    return proof

# --- Вспомогательные ---
def prepare_pool(goal, assumptions=None):
    pool = set()
    stack = [goal]
    if assumptions: stack.extend(assumptions)
    visited = set()
    while stack:
        f = stack.pop()
        if f in visited: continue
        visited.add(f)
        pool.add(f)
        if f.kind != 'not': pool.add(Formula('not', left=f))
        if f.kind == 'not': stack.append(f.left)
        elif f.kind == 'imp': 
            stack.append(f.left); stack.append(f.right)
    return list(pool)

# --- ОСНОВНОЙ РЕКУРСИВНЫЙ ПОИСК ---

def prove_recursive(goal, axioms, static_pool, assumptions=None, depth=0, max_depth=10):
    if assumptions is None: assumptions = set()
    
    # Тождество
    if goal.kind == 'imp' and goal.left == goal.right:
        p = Proof(axioms)
        A = goal.left
        # A -> ((A->A)->A)
        p.add_line(Formula('imp', A, Formula('imp', goal, A)), "Инстанция A1")
        # A2
        term2 = Formula('imp', Formula('imp', A, goal), goal)
        p.add_line(Formula('imp', p.lines[0][0], term2), "Инстанция A2")
        # MP
        p.add_line(term2, "MP")
        # A -> (A->A)
        p.add_line(Formula('imp', A, goal), "Инстанция A1")
        # Final
        p.add_line(goal, "MP")
        return p

    proof = Proof(axioms)

    if goal in assumptions:
        proof.add_line(goal, "Гипотеза")
        return proof
    
    for name, ax in axioms.items():
        if ax.match(goal):
            proof.add_line(goal, f"Инстанция {name}")
            return proof
            
    if depth > max_depth: return None

    for H in assumptions:
        neg_H = Formula('not', H)
        if neg_H in assumptions:
            proof.add_line(H, "Гипотеза")
            proof.add_line(neg_H, "Гипотеза")
            return solve_contradiction(proof, goal, H, 1, 0)

    # Дедукция
    if goal.kind == 'imp':
        A, B = goal.left, goal.right
        sub = prove_recursive(B, axioms, static_pool, assumptions | {A}, depth+1, max_depth)
        if sub: return transform_deduction(sub, A, axioms)


    imps = [f for f in assumptions if f.kind == 'imp']
    for imp in imps:
        X, Y = imp.left, imp.right
        if X in assumptions and Y not in assumptions:
            if Y in static_pool:
                res = prove_recursive(goal, axioms, static_pool, assumptions | {Y}, depth+1, max_depth)
                if res:
                    proof.add_line(imp, "Гипотеза")
                    proof.add_line(X, "Гипотеза")
                    proof.add_line(Y, "MP")
                    proof.extend(res)
                    return proof

    if depth < max_depth - 1:
        if goal.kind == 'not': neg_goal = goal.left
        else: neg_goal = Formula('not', goal)
        
        if neg_goal not in assumptions:
            facts = {neg_goal}
            if neg_goal.kind == 'not' and neg_goal.left.kind == 'not':
                facts.add(neg_goal.left.left)
            
            res = prove_recursive(goal, axioms, static_pool, assumptions | facts, depth+1, max_depth)
            if res:
                deduction = transform_deduction(res, neg_goal, axioms)
                deduction.add_line(goal, "Докажем от противного")
                return deduction

    return None

PRESETS = {
    '1': ('A4 A∧B→A', "~(A->~B)->(A->(B->A))"),
    '2': ('A5 A∧B→B', "~(A->~B)->(B->(A->B))"),
    '3': ('A6 A→(B→(A∧B))', "A->(B->~(A->~B))"),
    '4': ('A7 A→(A∨B)', "A->((~A)->B)->(A->((~A)->B))"),
    '5': ('A8  B→(A∨B)', "B->((~B)->A)->(B->((~B)->A))"),
    '6': ('A9 (A→C)→((B→C)→((A∨B)→C))', "(A->C)->((B->C)->((~A)->B->C))"),
    '7': ('A10 ¬A→(A→B)', "~A->(A->B)"),
    '8': ('A11 A∨¬A', "(A->A)->( (~A)->(A->A) )")
}
# --- ЗАПУСК ---
def main():
    psr = Parser()
    ax_map = {k: Axiom(k, v, psr) for k,v in AXIOMS.items()}
    
    print("\n--- Доказательство формул (A1-A3 + MP + Ded) ---")
    print("Вводите формулы используя: -> (импликация), ~ (отрицание), скобки.")
    print("Или выберите тест из списка:")
    for k, v in PRESETS.items(): print(f" {k}. {v[0]}")
    
    while True:
        print("\nМеню:")
        print(" [1-8] - Стандартные тесты")
        print(" [h]   - СПРАВКА (Новое окно)")
        print(" [q]   - Выход")
        
        sel = input("\nВаш выбор (можно сразу ввести формулу): ").strip()
        if sel.lower() == 'q': break
        
        # ВЫЗОВ СПРАВКИ
        if sel.lower() in ['h', 'help', 'справка']:
            logic_help.run_help()
            continue
        
        f_str = PRESETS[sel][1] if sel in PRESETS else sel
        try:
            goal = psr.parse(f_str)
            print(f"Доказываем: {goal}")
            pool = prepare_pool(goal)
            proof = prove_recursive(goal, ax_map, pool)
            if proof:
                print("ДОКАЗАНО:")
                print(proof)
            else:
                print("Не удалось доказать (возможно, не тавтология или слишком сложно).")
        except Exception as e:
            print(f"Ошибка: {e}")

if __name__ == "__main__":
    main()
