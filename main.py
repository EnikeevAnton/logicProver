import re
import logic_help


# Аксиомы
AXIOMS = {
    'A1': "A->(B->A)",
    'A2': "(A->(B->C))->((A->B)->(A->C))",
    'A3': "((~B)->(~A))->(((~B)->A)->B)"
}

class Colors:
    OKGREEN = '\033[92m'  # Зеленый цвет для выделения
    ENDC = '\033[0m'     # Сброс цвета (обязателен)
    BOLD = '\033[1m'

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

    def __str__(self):
        if not self.lines: return "Empty"
        
        self.fix_mp_indices()
        max_len = max(len(str(line[0])) for line in self.lines)
        col_w = max_len + 4
        res = ""
        
        for i, (f, text) in enumerate(self.lines):
            formula_str = str(f)
            rule_text = text.strip().lower()
            is_highlighted = ("дедукция" in rule_text) or ("<--" in rule_text)
            formatted_formula = formula_str
            if is_highlighted:
                formatted_rule = f"{Colors.BOLD}{Colors.OKGREEN}[{Colors.ENDC}{Colors.BOLD}{text}{Colors.BOLD}{Colors.OKGREEN}]{Colors.ENDC}"
            else:
                formatted_rule = f"[{text}]"
            padding = " " * (col_w - len(formula_str))
            res += f"{str(i).ljust(4)}{formatted_formula}{padding}{formatted_rule}\n"
            
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
    
    def get_line_number(self, f):
        """Возвращает индекс первой найденной формулы f."""
        for i, (formula, _) in enumerate(self.lines):
            if formula == f:
                return i
        return None
    
    def get_formulas(self):
        """Возвращает набор всех формул, присутствующих в доказательстве."""
        return {f for f, text in self.lines}

    def extend(self, other):
        existing_formulas = self.get_formulas()
        
        for f, text in other.lines:
            is_hypothesis = "Гипотеза" in text and text.strip() == "Гипотеза"
            if is_hypothesis and f in existing_formulas:
                continue

            self.lines.append((f, text))
            existing_formulas.add(f)


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


def dne_template(A_var, B_var):
    if A_var.kind == 'not':
        if A_var.left.kind == 'not' and A_var.left.left == B_var:
            return True
    return False

def get_claus(A_var, neg_A_var):
    left_part = Formula('imp', neg_A_var, A_var)
    return Formula('imp', left_part, A_var)


# --- ОСНОВНОЙ РЕКУРСИВНЫЙ ПОИСК ---

def prove_recursive(goal, axioms, static_pool, assumptions=None, depth=0, max_depth=10):
    if assumptions is None: assumptions = set()

    proof = Proof(axioms)

    if goal in assumptions:
        if proof.get_line_number(goal) is None:
            proof.add_line(goal, "Гипотеза")
        return proof
    
    for name, ax in axioms.items():
        if ax.match(goal):
            proof.add_line(goal, f"Инстанция {name}")
            return proof
    
    if goal.kind == 'imp':
        if dne_template(goal.left, goal.right) or dne_template(goal.right, goal.left):
            proof.add_line(goal, "Двойное отрицание") # берем за лемму
            return proof
        
    if depth > max_depth: return None

    # Если есть противоречие сразу получаем из него цель solve_contradiction()
    ordered_assumptions = sorted(list(assumptions), key=lambda f: str(f))
    for H in ordered_assumptions:
        neg_H = Formula('not', H)
        if neg_H in assumptions:
            proof.add_line(H, "Гипотеза")
            proof.add_line(neg_H, "Гипотеза")
            return solve_contradiction(proof, goal, H, 1, 0)

    # Дедукция (A -> ...)
    if goal.kind == 'imp':
        A, B = goal.left, goal.right
        sub = prove_recursive(B, axioms, static_pool, assumptions | {A}, depth+1, max_depth)
        if sub: return transform_deduction(sub, A, axioms)

    # MP среди гипотез для вывода новых 
    imps = [f for f in ordered_assumptions if f.kind == 'imp']
    for imp in imps:
        X, Y = imp.left, imp.right
        if Y == goal and X in assumptions:
            if proof.get_line_number(imp) is None:
                proof.add_line(imp, "Гипотеза")
                idx_imp = len(proof.lines) - 1

            if proof.get_line_number(X) is None:
                proof.add_line(X, "Гипотеза")
                idx_X = len(proof.lines) - 1

            proof.add_line(goal, f"MP")
            return proof
        if X in assumptions and Y not in assumptions:
            if Y in static_pool:
                res = prove_recursive(goal, axioms, static_pool, assumptions | {Y}, depth+1, max_depth)
                if res:
                    if proof.get_line_number(imp) is None:
                        proof.add_line(imp, "Гипотеза")
                    if proof.get_line_number(X) is None:
                        proof.add_line(X, "Гипотеза")
                    if proof.get_line_number(Y) is None:
                        proof.add_line(Y, "MP")
                    proof.extend(res)
                    return proof
    
    # Гипотеза P -> G и цель G
    P_imp_Goal = None
    P_val = None

    # Поиск в гипотезах P -> G, попытка доказать ~P -> G. Вывод (P -> G) : (~G -> ~P) и (~P -> G) : (~G -> P)
    # При получении (~G -> ~P) и (~G -> P) -  инстанция A3 (~G -> ~P) -> ((~G -> P) -> G)
    # Далее два раза применяется MP и выводится G (цель)
    for f in ordered_assumptions:
        if f.kind == 'imp' and f.right == goal:
            P_imp_Goal = f
            P_val = f.left
            break
            
    if P_imp_Goal and goal.kind == 'var':

        # Определяем вторую необходимую импликацию: ~P -> G
        not_P_val = Formula('not', P_val)
        notP_imp_Goal = Formula('imp', not_P_val, goal)
        
        current_assumptions = set(assumptions)

        # Если ~P -> G еще не в гипотезах, пытаемся его доказать
        if notP_imp_Goal not in current_assumptions:
            
            # Доказываем ~P -> G
            subproof_res = prove_recursive(notP_imp_Goal, axioms, static_pool, current_assumptions, depth + 1, max_depth)
            
            if not subproof_res:
                # Не смогли доказать ключевую импликацию, стратегия не сработала
                return None
            
            # Добавляем доказательство ~P -> G в основное доказательство
            proof.extend(subproof_res)
            current_assumptions.add(notP_imp_Goal)
        
        # Теперь у нас есть: P -> G (из гипотез) и ~P -> G (доказано/было в гипотезах)

        neg_Goal = Formula('not', goal)
        G1 = Formula('imp', neg_Goal, not_P_val)
        G2 = Formula('imp', neg_Goal, P_val)
        
        can_proceed = True
        current_assumptions = {P_imp_Goal}
        # P -> G |- ~G -> ~P
        if G1 not in current_assumptions:
            proof_G1 = prove_recursive(G1, axioms, static_pool, current_assumptions, depth + 1, max_depth)
            if proof_G1:
                proof.extend(proof_G1)
                current_assumptions.add(G1)
            else:
                can_proceed = False
        
        # ~P -> G |- ~G -> P
        current_assumptions = {notP_imp_Goal}
        if G2 not in current_assumptions and can_proceed:
            proof_G2 = prove_recursive(G2, axioms, static_pool, current_assumptions, depth + 1, max_depth)
            
            if proof_G2:
                proof.extend(proof_G2)
                current_assumptions.add(G2)
            else:
                 can_proceed = False
        
        if not can_proceed:
            return None # Не удалось доказать

        # A3: Из G1 (~G -> ~P) и G2 (~G -> P) выводим Goal (G)
        
        # A3 инстанция: (~G -> ~P) -> ((~G -> P) -> G)
        ax3_instance = Formula('imp', G1, Formula('imp', G2, goal))
        proof.add_line(ax3_instance, "Инстанция A3")
        
        # MP из G1 и A3
        s_step = ax3_instance.right
        proof.add_line(s_step, "MP")
        
        # MP из G2 (Финальный Goal)
        proof.add_line(goal, "MP")
        
        return proof

    # Статегия вывода противоречия: пусть в гипотезах ~P, попытаемся док-ть P
    for H in ordered_assumptions:
        if H.kind == 'not':
            target_conflict = H.left
            if target_conflict != goal and target_conflict not in assumptions:
                conflict_proof = prove_recursive(target_conflict, axioms, static_pool, assumptions, depth + 1, max_depth)
                
                if conflict_proof:
                    proof.extend(conflict_proof)
                    if proof.get_line_number(H) is None:
                        proof.add_line(H, "Гипотеза")
                    idx_X = len(proof.lines) - 2
                    idx_not_X = len(proof.lines) - 1
                    
                    # доказательство успеншо: выводим цель
                    return solve_contradiction(proof, goal, target_conflict, idx_not_X, idx_X)
    
    # Доказательсво от противного: цель G, докажем ~G->G. Далее (~G->G)->G (A3)
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
                deduction.add_line(goal, f'<--Текущая цель, пусть {neg_goal}')
                deduction.add_line(get_claus(goal, neg_goal), "Инстанция A3")
                deduction.add_line(goal, "MP")
                return deduction

    return None

PRESETS = {
    '1': ('A4 A∧B→A', "(~(A->~B)) -> A"),
    '2': ('A5 A∧B→B', "(~(A->~B)) -> B"),
    '3': ('A6 A→(B→(A∧B))', "A -> (B -> ~(A->~B))"),
    '4': ('A7 A→(A∨B)', "A -> (~A -> B)"),
    '5': ('A8  B→(A∨B)', "B -> (~A -> B)"),
    '6': ('A9 (A→C)→((B→C)→((A∨B)→C))', "(A->C) -> ((B->C) -> ((~A->B) -> C))"),
    '7': ('A10 ¬A→(A→B)', "~A -> (A -> B)"),
    '8': ('A11 A∨¬A', "~A -> ~A")
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