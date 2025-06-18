from dataclasses import dataclass
from typing import Union, Tuple, List, Optional
from enum import Enum
import subprocess

PRODUCE_PROOFS = True
PERFORM_ASSERTION = True
PRINT_MARKERS = True

proof_data = ""

class ConnectiveType(Enum):
    AND = "∧"
    OR = "∨"
    IMP = "⊃"
    COIMP = "⊂"

@dataclass(frozen=True)
class Atom:
    name: str
    
    def __str__(self):
        return self.name

@dataclass(frozen=True)
class Bot:
    def __str__(self):
        return "⊥"

@dataclass(frozen=True)
class Top:
    def __str__(self):
        return "⊤"

@dataclass(frozen=True)
class Compound:
    connective: ConnectiveType
    left: Union['Atom', 'Compound', 'Bot', 'Top']
    right: Union['Atom', 'Compound', 'Bot', 'Top']
    
    def __str__(self):
        return f"({self.left} {self.connective.value} {self.right})"

Formula = Union[Atom, Compound, Bot, Top]

@dataclass
class ProofNode:
    sequent: Tuple[Formula, Formula]
    rule: str
    premises: List['ProofNode']
    
    def __str__(self):
        return f"{self.sequent[0]} ⟹  {self.sequent[1]}"

def is_atom(formula: Formula) -> bool:
    return isinstance(formula, Atom)

def is_bot(formula: Formula) -> bool:
    return isinstance(formula, Bot)

def is_top(formula: Formula) -> bool:
    return isinstance(formula, Top)

def is_conjunction(formula: Formula) -> bool:
    return isinstance(formula, Compound) and formula.connective == ConnectiveType.AND

def is_disjunction(formula: Formula) -> bool:
    return isinstance(formula, Compound) and formula.connective == ConnectiveType.OR

def is_imp(formula: Formula) -> bool:
    return isinstance(formula, Compound) and formula.connective == ConnectiveType.IMP

def is_coimp(formula: Formula) -> bool:
    return isinstance(formula, Compound) and formula.connective == ConnectiveType.COIMP

def get_conjuncts(formula: Formula) -> Tuple[Formula, Formula]:
    assert is_conjunction(formula)
    return formula.left, formula.right

def get_disjuncts(formula: Formula) -> Tuple[Formula, Formula]:
    assert is_disjunction(formula)
    return formula.left, formula.right

def get_imp_parts(formula: Formula) -> Tuple[Formula, Formula]:
    assert is_imp(formula)
    return formula.left, formula.right

def get_coimp_parts(formula: Formula) -> Tuple[Formula, Formula]:
    assert is_coimp(formula)
    return formula.left, formula.right

def assertion_print(msg: str):
    if PERFORM_ASSERTION and PRINT_MARKERS:
        print(msg)

def test_derivable(sequent: tuple[Formula, Formula], expected: bool, test_str: str):
    global proof_data
    
    if PERFORM_ASSERTION:
        result = is_derivable(sequent)
        assert result == expected, f"{test_str}"
    
    if expected and PRODUCE_PROOFS:
        proof_data += ("\\section*{" + test_str[:test_str.index(":")+1].replace(" failed", "") + "}\n" +
            lift_object_to_bussproofs(derive_proof(sequent)) + "\\hfill\n\\break\n"*2)
    else:
        formula_left = lift_formula_to_latex_string(sequent[0])
        formula_right = lift_formula_to_latex_string(sequent[1])
        if expected:
            # This case happens when expected is True but PRODUCE_PROOFS is False
            status_text = "Derivable (proof generation disabled)"
        else:
            # This case happens when expected is False
            status_text = "Not derivable"
        
        proof_data += (f"\\section*{{{test_str[:test_str.index(':')+1].replace(' failed', '')}}}\n" +
                      f"${formula_left} \\implies {formula_right}$ \\\\\n" +
                      f"\\textit{{{status_text}}}\n" +
                      "\\hfill\n\\break\n"*2)

def derive_proof(sequent: Tuple[Formula, Formula], cache: Optional[dict] = None) -> Optional[ProofNode]:
    if cache is None:
        cache = {}

    if sequent in cache:
        return cache[sequent]

    alpha, beta = sequent
    
    # A (Axiom)
    if is_atom(alpha) and is_atom(beta) and alpha.name == beta.name:
        result = ProofNode(sequent, "A", [])
        cache[sequent] = result
        return result
    
    # ⊥ rule: ⊥ ⟹   α
    if is_bot(alpha):
        result = ProofNode(sequent, "⊥", [])
        cache[sequent] = result
        return result
    
    # ⊤ rule: α ⟹   ⊤
    if is_top(beta):
        result = ProofNode(sequent, "⊤", [])
        cache[sequent] = result
        return result

    # Weakening rules

    # we_L: if ⊤ ⟹   β then α ⟹   β
    if not is_top(alpha):
        top_to_beta = derive_proof((Top(), beta))
        if top_to_beta:
            result = ProofNode(sequent, "we_L", [top_to_beta])
            cache[sequent] = result
            return result
    
    # we_R: if α ⟹   ⊥ then α ⟹   β
    if not is_bot(beta):
        alpha_to_bot = derive_proof((alpha, Bot()))
        if alpha_to_bot:
            result = ProofNode(sequent, "we_R", [alpha_to_bot])
            cache[sequent] = result
            return result

    #### Left operations!
    # ∧L
    if is_conjunction(alpha):
        for i, ai in enumerate(get_conjuncts(alpha)):
            sub_proof = derive_proof((ai, beta))
            if sub_proof:
                result = ProofNode(sequent, f"∧L{i+1}", [sub_proof])
                cache[sequent] = result
                return result

    # ∨L
    if is_disjunction(alpha):
        a1, a2 = get_disjuncts(alpha)
        sub_proof_l = derive_proof((a1, beta))
        sub_proof_r = derive_proof((a2, beta))
        
        if sub_proof_l and sub_proof_r:
            result = ProofNode(sequent, "∨L", [sub_proof_l, sub_proof_r])
            cache[sequent] = result
            return result

    # ⊃L
    if is_imp(alpha):
        a1, a2 = get_imp_parts(alpha)
        top_to_a1 = derive_proof((Top(), a1))
        a2_to_beta = derive_proof((a2, beta))
        
        if top_to_a1 and a2_to_beta:
            result = ProofNode(sequent, "⊃L", [top_to_a1, a2_to_beta])
            cache[sequent] = result
            return result

    # ⊂L
    if is_coimp(alpha) and is_bot(beta):
        a1, a2 = get_coimp_parts(alpha)
        a1_to_a2 = derive_proof((a1, a2))
        if a1_to_a2:
            result = ProofNode(sequent, "⊂L", [a1_to_a2])
            cache[sequent] = result
            return result

    #### Right operations
    # ∧R
    if is_conjunction(beta):
        b1, b2 = get_conjuncts(beta)
        sub_proof_l = derive_proof((alpha, b1))
        sub_proof_r = derive_proof((alpha, b2))
        
        if sub_proof_l and sub_proof_r:
            result = ProofNode(sequent, "∧R", [sub_proof_l, sub_proof_r])
            cache[sequent] = result
            return result

    # ∨R
    if is_disjunction(beta):
        for i, bi in enumerate(get_disjuncts(beta)):
            sub_proof = derive_proof((alpha, bi))
            if sub_proof:
                result = ProofNode(sequent, f"∨R{i+1}", [sub_proof])
                cache[sequent] = result
                return result

    # ⊃R
    if is_imp(beta) and is_top(alpha):
        b1, b2 = get_imp_parts(beta)
        b1_to_b2 = derive_proof((b1, b2))
        if b1_to_b2:
            result = ProofNode(sequent, "⊃R", [b1_to_b2])
            cache[sequent] = result
            return result

    # ⊂R
    if is_coimp(beta):
        b1, b2 = get_coimp_parts(beta)
        alpha_to_b1 = derive_proof((alpha, b1))
        b2_to_bot = derive_proof((b2, Bot()))
        
        if alpha_to_b1 and b2_to_bot:
            result = ProofNode(sequent, "⊂R", [alpha_to_b1, b2_to_bot])
            cache[sequent] = result
            return result

    #### Order operations
    # ⊃_order
    if is_imp(alpha) and is_imp(beta):
        a1, a2 = get_imp_parts(alpha)
        b1, b2 = get_imp_parts(beta)
        
        b1_to_a1 = derive_proof((b1, a1))
        a2_to_b2 = derive_proof((a2, b2))
        
        if b1_to_a1 and a2_to_b2:
            result = ProofNode(sequent, "⊃order", [b1_to_a1, a2_to_b2])
            cache[sequent] = result
            return result

    # ⊂_order
    if is_coimp(alpha) and is_coimp(beta):
        a1, a2 = get_coimp_parts(alpha)
        b1, b2 = get_coimp_parts(beta)
        
        a1_to_b1 = derive_proof((a1, b1))
        b2_to_a2 = derive_proof((b2, a2))
        
        if a1_to_b1 and b2_to_a2:
            result = ProofNode(sequent, "⊂order", [a1_to_b1, b2_to_a2])
            cache[sequent] = result
            return result

    cache[sequent] = None
    return None

def is_derivable(sequent: Tuple[Formula, Formula]) -> bool:
    return derive_proof(sequent) is not None

def lift_formula_to_latex_string(formula: Formula) -> str:
    if is_atom(formula):
        return formula.name
    elif is_bot(formula):
        return "\\bot"
    elif is_top(formula):
        return "\\top"
    elif is_conjunction(formula):
        left = lift_formula_to_latex_string(formula.left)
        right = lift_formula_to_latex_string(formula.right)
        return f"({left} \\land {right})"
    elif is_disjunction(formula):
        left = lift_formula_to_latex_string(formula.left)
        right = lift_formula_to_latex_string(formula.right)
        return f"({left} \\lor {right})"
    elif is_imp(formula):
        left = lift_formula_to_latex_string(formula.left)
        right = lift_formula_to_latex_string(formula.right)
        return f"({left} \\supset {right})"
    elif is_coimp(formula):
        left = lift_formula_to_latex_string(formula.left)
        right = lift_formula_to_latex_string(formula.right)
        return f"({left} \\subset {right})"
    else:
        return str(formula)

def lift_proof_to_bussproofs(proof: ProofNode) -> str:
    if not proof.premises:
        alpha_latex = lift_formula_to_latex_string(proof.sequent[0])
        beta_latex = lift_formula_to_latex_string(proof.sequent[1])
        
        rule_latex = ""
        if proof.rule == "A":
            rule_latex = "\\RightLabel{$A$}"
        elif proof.rule == "⊥":
            rule_latex = "\\RightLabel{$\\bot$}"
        elif proof.rule == "⊤":
            rule_latex = "\\RightLabel{$\\top$}"
        else:
            raise ValueError(f"You can't have premises empty for the rule {proof.rule}.")
        
        return f"\\AxiomC{{}}\n{rule_latex}\n\\UnaryInfC{{${alpha_latex} \\Rightarrow {beta_latex}$}}"
    
    premises_latex = []
    for premise in proof.premises:
        premises_latex.append(lift_proof_to_bussproofs(premise))
    
    alpha_latex = lift_formula_to_latex_string(proof.sequent[0])
    beta_latex = lift_formula_to_latex_string(proof.sequent[1])

    rulestr = ""
    if proof.rule == "we_L":
        rulestr = "\\RightLabel{$we_L$}"
    elif proof.rule == "we_R":
        rulestr = "\\RightLabel{$we_R$}"
    elif proof.rule in ["∧L1", "∧L2"]:
        rulestr = f"\\RightLabel{{$\\land_{{{proof.rule[1:]}}}$}}"
    elif proof.rule == "∧R":
        rulestr = "\\RightLabel{$\\land_R$}"
    elif proof.rule == "∨L":
        rulestr = "\\RightLabel{$\\lor_L$}"
    elif proof.rule in ["∨R1", "∨R2"]:
        rulestr = f"\\RightLabel{{$\\lor_{{{proof.rule[1:]}}}$}}"
    elif proof.rule == "⊃L":
        rulestr = "\\RightLabel{$\\supset_L$}"
    elif proof.rule == "⊃R":
        rulestr = "\\RightLabel{$\\supset_R$}"
    elif proof.rule == "⊂L":
        rulestr = "\\RightLabel{$\\subset_L$}"
    elif proof.rule == "⊂R":
        rulestr = "\\RightLabel{$\\subset_R$}"
    elif proof.rule == "⊃order":
        rulestr = "\\RightLabel{$\\supset_{order}$}"
    elif proof.rule == "⊂order":
        rulestr = "\\RightLabel{$\\subset_{order}$}"
    else:
        rulestr = f"\\RightLabel{{{proof.rule}}}"
    
    if len(proof.premises) == 1:
        return f"{premises_latex[0]}\n{rulestr}\n\\UnaryInfC{{${alpha_latex} \\Rightarrow {beta_latex}$}}"
    elif len(proof.premises) == 2:
        return f"{premises_latex[0]}\n{premises_latex[1]}\n{rulestr}\n\\BinaryInfC{{${alpha_latex} \\Rightarrow {beta_latex}$}}"
    else:
        raise ValueError("More than 2 premises in a proof node, which is not supported.")

def lift_object_to_bussproofs(proof: ProofNode) -> str:
    proof_latex = lift_proof_to_bussproofs(proof)
    
    return f"""\\begin{{minipage}}{{0.3\\linewidth}}
\\begin{{prooftree}}
{proof_latex}
\\end{{prooftree}}
\\end{{minipage}}

"""

# Helper functions to create the formulas.
def atom(name: str) -> Atom:
    return Atom(name)

def bot() -> Bot:
    return Bot()

def top() -> Top:
    return Top()

def and_formula(left: Formula, right: Formula) -> Compound:
    return Compound(ConnectiveType.AND, left, right)

def or_formula(left: Formula, right: Formula) -> Compound:
    return Compound(ConnectiveType.OR, left, right)

def imp_formula(left: Formula, right: Formula) -> Compound:
    return Compound(ConnectiveType.IMP, left, right)

def coimp_formula(left: Formula, right: Formula) -> Compound:
    return Compound(ConnectiveType.COIMP, left, right)

# Test cases
if __name__ == "__main__":
    p = atom("p")
    q = atom("q")
    r = atom("r")

    assertion_print("\n=== RUNNING NEW LOGIC TESTS ===")
    
    assertion_print("\n=== BASIC AXIOM TESTS ===")
    # Test 1: Identity
    test_derivable((p, p), True, "Test 1: p ⟹  p")
    # Test 2: Bot elimination
    test_derivable((bot(), p), True, "Test 2: ⊥ ⟹  p")
    # Test 3: Top introduction
    test_derivable((p, top()), True, "Test 3: p ⟹  ⊤")
    assertion_print("Passed!")
    
    assertion_print("\n=== CONJUNCTION TESTS ===")
    pq = and_formula(p, q)
    # Test 4: ∧L1
    test_derivable((pq, p), True, "Test 4: p ∧ q ⟹  p")
    # Test 5: ∧L2
    test_derivable((pq, q), True, "Test 5: p ∧ q ⟹  q")
    # Test 6: ∧R
    test_derivable((p, and_formula(p, p)), True, "Test 6: p ⟹  p ∧ p")
    assertion_print("Passed!")
    
    assertion_print("\n=== DISJUNCTION TESTS ===")
    pq_or = or_formula(p, q)
    # Test 7: ∨R1
    test_derivable((p, pq_or), True, "Test 7: p ⟹  p ∨ q")
    # Test 8: ∨R2
    test_derivable((q, pq_or), True, "Test 8: q ⟹  p ∨ q")
    # Test 9: ∨L
    test_derivable((pq_or, pq_or), True, "Test 9: p ∨ q ⟹  p ∨ q")
    assertion_print("Passed!")
    
    assertion_print("\n=== IMP TESTS ===")
    # Test 10: ⊃R
    p_imp_p = imp_formula(p, p)
    test_derivable((top(), p_imp_p), True, "Test 10: ⊤ ⟹  p ⊃ p")
    assertion_print("Passed!")
    
    assertion_print("\n=== COIMP TESTS ===")
    # Test 11: ⊂L
    p_coimp_q = coimp_formula(p, q)
    test_derivable((p_coimp_q, bot()), False, "Test 11: p ⊂ q ⟹  ⊥ (when p ⟹  q is not derivable)")
    assertion_print("Passed!")
    
    assertion_print("\n=== WEAKENING TESTS ===")
    # Test 12: Weakening left
    test_derivable((p, top()), True, "Test 12: p ⟹  ⊤ (should work via ⊤ rule)")
    # Test 13: Weakening right  
    test_derivable((bot(), q), True, "Test 13: ⊥ ⟹  q (should work via ⊥ rule)")
    assertion_print("Passed!")

    assertion_print("\n=== ORDER RULE TESTS ===")
    # Test 14: ⊃ order rule - contravariant in first argument, covariant in second
    p_imp_q = imp_formula(p, q)
    q_imp_r = imp_formula(q, r)
    p_imp_r = imp_formula(p, r)
    test_derivable((q_imp_r, p_imp_r), False, "Test 14a: q ⊃ r ⟹ p ⊃ r (should fail without p ⟹ q)")
    
    # Test 15: ⊂ order rule - covariant in first argument, contravariant in second
    p_coimp_q = coimp_formula(p, q)
    q_coimp_r = coimp_formula(q, r)
    p_coimp_r = coimp_formula(p, r)
    test_derivable((p_coimp_r, q_coimp_r), False, "Test 15a: p ⊂ r ⟹ q ⊂ r (should fail without specific conditions)")

    assertion_print("Passed!")
    
    assertion_print("\n=== COMPLEX imp TESTS ===")
    # Test 16: ⊃R with identity
    test_derivable((top(), p_imp_p), True, "Test 16: ⊤ ⟹ p ⊃ p")
    
    # Test 17: ⊃L application
    p_imp_q_and_p = and_formula(p_imp_q, p)
    test_derivable((p_imp_q_and_p, q), False, "Test 17: (p ⊃ q) ∧ p ⟹ q (should fail in this logic)")

    assertion_print("Passed!")
    
    assertion_print("\n=== COMPLEX coimp TESTS ===")
    # Test 18: ⊂R construction
    test_derivable((p, coimp_formula(p, bot())), True, "Test 18: p ⟹ p ⊂ ⊥")
    
    # Test 19: ⊂L elimination with contradiction
    p_coimp_p = coimp_formula(p, p)
    test_derivable((p_coimp_p, bot()), True, "Test 19: p ⊂ p ⟹ ⊥")

    assertion_print("Passed!")
    
    assertion_print("\n=== INTERACTION TESTS ===")
    # Test 20: imp and conjunction
    p_and_q_imp_p = imp_formula(pq, p)
    test_derivable((top(), p_and_q_imp_p), True, "Test 20: ⊤ ⟹ (p ∧ q) ⊃ p")
    
    # Test 21: Disjunction and imp
    p_imp_p_or_q = imp_formula(p, pq_or)
    test_derivable((top(), p_imp_p_or_q), True, "Test 21: ⊤ ⟹ p ⊃ (p ∨ q)")
    
    # Test 22: coimp and disjunction
    p_or_q_coimp_q = coimp_formula(pq_or, q)
    test_derivable((p, p_or_q_coimp_q), False, "Test 22: p ⟹ (p ∨ q) ⊂ q (should fail)")

    assertion_print("Passed!")
    
    assertion_print("\n=== WEAKENING INTERACTION TESTS ===")
    # Test 23: Weakening with imp
    test_derivable((p_imp_q, r), False, "Test 23: p ⊃ q ⟹   r (should fail without additional conditions)")
    
    # Test 24: Weakening with coimp
    test_derivable((r, p_coimp_q), False, "Test 24: r ⟹  p ⊂ q (should fail without specific conditions)")

    assertion_print("Passed!")
    
    assertion_print("\n=== NESTED CONNECTIVE TESTS ===")
    # Test 25: Nested imps
    q_imp_r = imp_formula(q, r)
    p_imp_q_imp_r = imp_formula(p, q_imp_r)
    pq_imp_r = imp_formula(pq, r)
    test_derivable((top(), imp_formula(p_imp_q_imp_r, pq_imp_r)), False, "Test 25: ⊤ ⟹ (p ⊃ (q ⊃ r)) ⊃ ((p ∧ q) ⊃ r)")
    
    # Test 26: Nested coimps
    q_coimp_r = coimp_formula(q, r)
    p_coimp_q_coimp_r = coimp_formula(p, q_coimp_r)
    test_derivable((p_coimp_q_coimp_r, bot()), False, "Test 26: p ⊂ (q ⊂ r) ⟹  ⊥")
    
    # Test 27: Mixed nesting
    p_imp_q_and_r = imp_formula(p, and_formula(q, r))
    p_imp_q_imp_r = imp_formula(p, imp_formula(q, r))
    test_derivable((top(), imp_formula(p_imp_q_and_r, p_imp_q_imp_r)), False, "Test 27: ⊤ ⟹ (p ⊃ (q ∧ r)) ⊃ (p ⊃ (q ⊃ r))")

    assertion_print("Passed!")
    
    assertion_print("\n=== CONSISTENCY TESTS ===")
    # Test 28: No contradiction from atoms
    test_derivable((p, bot()), False, "Test 28: p ⟹  ⊥ (should fail)")
    
    # Test 29: Top is not everything
    test_derivable((top(), p), False, "Test 29: ⊤ ⟹  p (should fail)")
    
    # Test 30: Double negation via subset
    p_coimp_bot = coimp_formula(p, bot())
    p_coimp_bot_coimp_bot = coimp_formula(p_coimp_bot, bot())
    test_derivable((p_coimp_bot_coimp_bot, p), False, "Test 30: ((p ⊂ ⊥) ⊂ ⊥) ⟹  p (should fail - no double negation)")
    assertion_print("Passed!")

    if PRODUCE_PROOFS:
        with open("proofs_nl.tex", "w") as f:
            template_data = ""
            with open("a.template", "r") as g:
                template_data = g.read()
                final = template_data + proof_data + "\n\\end{document}"
                f.write(final)
            # f.write(proof_data)

        subprocess.run(["pdflatex", "proofs_nl.tex"], check=True)
        subprocess.run(["rm", "proofs_nl.aux", "proofs_nl.log", "proofs_nl.out"], check=True)


