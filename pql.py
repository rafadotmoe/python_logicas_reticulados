from dataclasses import dataclass
from typing import Union, Tuple, List, Optional
from enum import Enum
import subprocess

PRODUCE_PROOFS = True
PERFORM_ASSERTION = True
PRINT_MARKERS = False

proof_data = ""

class ConnectiveType(Enum):
    AND = "∧"
    OR = "∨"
    NOT = "~"

@dataclass(frozen=True)
class Atom:
    name: str
    
    def __str__(self):
        return self.name

@dataclass(frozen=True)
class UnaryCompound:
    connective: ConnectiveType
    operand: Union['Atom', 'BinaryCompound', 'UnaryCompound']
    
    def __str__(self):
        return f"{self.connective.value}{self.operand}"

@dataclass(frozen=True)
class BinaryCompound:
    connective: ConnectiveType
    left: Union['Atom', 'UnaryCompound', 'BinaryCompound']
    right: Union['Atom', 'UnaryCompound', 'BinaryCompound']
    
    def __str__(self):
        return f"({self.left} {self.connective.value} {self.right})"

Formula = Union[Atom, UnaryCompound, BinaryCompound]

@dataclass
class ProofNode:
    sequent: Tuple[Formula, Formula]
    rule: str
    premises: List['ProofNode']
    
    def __str__(self):
        return f"{self.sequent[0]} ⟹  {self.sequent[1]}"

def is_atom(formula: Formula) -> bool:
    return isinstance(formula, Atom)


def is_conjunction(formula: Formula) -> bool:
    return isinstance(formula, BinaryCompound) and formula.connective == ConnectiveType.AND

def is_disjunction(formula: Formula) -> bool:
    return isinstance(formula, BinaryCompound) and formula.connective == ConnectiveType.OR

def is_negation(formula: Formula) -> bool:
    return isinstance(formula, UnaryCompound) and formula.connective == ConnectiveType.NOT

def is_double_negation(formula: Formula) -> bool:
    return is_negation(formula) and is_negation(formula.operand)

def is_neg_conjunction(formula: Formula) -> bool:
    return is_negation(formula) and is_conjunction(formula.operand)

def is_neg_disjunction(formula: Formula) -> bool:
    return is_negation(formula) and is_disjunction(formula.operand)

def is_neg_atom(formula: Formula) -> bool:
    return is_negation(formula) and is_atom(formula.operand)

def get_neg(formula: Formula) -> Formula:
    assert is_negation(formula)
    return formula.operand

def get_conjuncts(formula: Formula) -> Tuple[Formula, Formula]:
    assert is_conjunction(formula)
    return formula.left, formula.right

def get_disjuncts(formula: Formula) -> Tuple[Formula, Formula]:
    assert is_disjunction(formula)
    return formula.left, formula.right

def get_neg_conjuncts(formula: Formula) -> Tuple[Formula, Formula]:
    assert is_neg_conjunction(formula)
    return not_formula(get_conjuncts(formula.operand)[0]), not_formula(get_conjuncts(formula.operand)[1])

def get_neg_disjuncts(formula: Formula) -> Tuple[Formula, Formula]:
    assert is_neg_disjunction(formula)
    return not_formula(get_disjuncts(formula.operand)[0]), not_formula(get_disjuncts(formula.operand)[1])

def assertion_print(msg: str):
    if PERFORM_ASSERTION and PRINT_MARKERS:
        print(msg)

def test_derivable(sequent: tuple[Formula, Formula], expected: bool, test_str: str):
    global proof_data
    
    if PERFORM_ASSERTION:
        result = is_derivable(sequent)
        assert result == expected, f"{test_str}"
    
    if expected and PRODUCE_PROOFS:

        status_text = "Sequente derivável"
        formula_left = lift_formula_to_latex_string(sequent[0])
        formula_right = lift_formula_to_latex_string(sequent[1])

        proof_data += ("\\paragraph{" + test_str[:test_str.index(":")+1].replace("failed", "") + " " + f"${formula_left} \\Rightarrow  {formula_right}$ \\\\\n""}"  + "\\leavevmode"+"\n\n"+
                      f"\\text{{{status_text}}}\n" +
                      "\\hfill\n\\break\n"*2+ 
            lift_object_to_bussproofs(derive_proof(sequent)) + "\\hfill\n\\break\n"*2)

    else:
        formula_left = lift_formula_to_latex_string(sequent[0])
        formula_right = lift_formula_to_latex_string(sequent[1])
        if expected:
            # This case happens when expected is True but PRODUCE_PROOFS is False
            status_text = "Derivable (proof generation disabled)"
        else:
            # This case happens when expected is False
            status_text = "Sequente não derivável"
        
        proof_data += ("\\paragraph{" + test_str[:test_str.index(":")+1].replace("failed", "") + " " +f"${formula_left} \\Rightarrow  {formula_right}$ \\\\\n""}"  + "\\leavevmode"+"\n\n"+
                      f"\\text{{{status_text}}}\n" +
                      "\\hfill\n\\break\n"*2)


def derive_proof(sequent: Tuple[Formula, Formula]) -> Optional[ProofNode]:
    alpha, beta = sequent
    
    # A (Axiom)
    if is_atom(alpha) and is_atom(beta) and alpha == beta:
        return ProofNode(sequent, "A", [])

    # ~A (Axiom)
    if is_neg_atom(alpha) and is_neg_atom(beta) and alpha == beta:
        return ProofNode(sequent, "~A", [])

    #### Left operations!
    # ~~L
    if is_double_negation(alpha):
        sub_proof = derive_proof((get_neg(get_neg(alpha)), beta))
        if sub_proof:
            return ProofNode(sequent, "~~L", [sub_proof])

    # ∧L
    if is_conjunction(alpha):
        for i, ai in enumerate(get_conjuncts(alpha)):
            sub_proof = derive_proof((ai, beta))
            if sub_proof:
                return ProofNode(sequent, f"∧L{i+1}", [sub_proof])

    # ~∨L
    if is_neg_disjunction(alpha):
        for i, ai in enumerate(get_neg_disjuncts(alpha)):
            sub_proof = derive_proof((ai, beta))
            if sub_proof:
                return ProofNode(sequent, f"~∨L{i+1}", [sub_proof])
    
    # ∨L
    if is_disjunction(alpha):
        a1, a2 = get_disjuncts(alpha)
        sub_proof_l = derive_proof((a1, beta))
        sub_proof_r = derive_proof((a2, beta))
        
        if sub_proof_l and sub_proof_r:
            return ProofNode(sequent, "∨L", [sub_proof_l, sub_proof_r])

    # ~∧L
    if is_neg_conjunction(alpha):
        a1, a2 = get_neg_conjuncts(alpha)
        sub_proof_l = derive_proof((a1, beta))
        sub_proof_r = derive_proof((a2, beta))
        
        if sub_proof_l and sub_proof_r:
            return ProofNode(sequent, "~∧L", [sub_proof_l, sub_proof_r])

    #### Right operations!
    # ~~R
    if is_double_negation(beta):
        sub_proof = derive_proof((alpha, get_neg(get_neg(beta))))
        if sub_proof:
            return ProofNode(sequent, "~~R", [sub_proof])

    # ∧R
    if is_conjunction(beta):
        b1, b2 = get_conjuncts(beta)
        sub_proof_l = derive_proof((alpha, b1))
        sub_proof_r = derive_proof((alpha, b2))
        
        if sub_proof_l and sub_proof_r:
            return ProofNode(sequent, "∧R", [sub_proof_l, sub_proof_r])

    # ~∨R
    if is_neg_disjunction(beta):
        b1, b2 = get_neg_disjuncts(beta)
        sub_proof_l = derive_proof((alpha, b1))
        sub_proof_r = derive_proof((alpha, b2))

        if sub_proof_l and sub_proof_r:
            return ProofNode(sequent, "~∨R", [sub_proof_l, sub_proof_r])

    # ∨R
    if is_disjunction(beta):
        for i, bi in enumerate(get_disjuncts(beta)):
            sub_proof = derive_proof((alpha, bi))
            if sub_proof:
                return ProofNode(sequent, f"∨R{i+1}", [sub_proof])

    # ~∧R
    if is_neg_conjunction(beta):
        for i, bi in enumerate(get_neg_conjuncts(beta)):
            sub_proof = derive_proof((alpha, bi))
            if sub_proof:
                return ProofNode(sequent, f"~∧R{i+1}", [sub_proof])
    
    return None

def is_derivable(sequent: Tuple[Formula, Formula]) -> bool:
    return derive_proof(sequent) is not None

def lift_formula_to_latex_string(formula: Formula) -> str:
    if is_atom(formula):
        return formula.name
    elif is_conjunction(formula):
        left = lift_formula_to_latex_string(formula.left)
        right = lift_formula_to_latex_string(formula.right)
        return f"({left} \\land {right})"
    elif is_disjunction(formula):
        left = lift_formula_to_latex_string(formula.left)
        right = lift_formula_to_latex_string(formula.right)
        return f"({left} \\lor {right})"
    elif is_neg_atom(formula):
        return f"\\sim {formula.operand.name}"
    elif is_neg_conjunction(formula):
        left, right = get_conjuncts(formula.operand)
        return f"\\sim ({lift_formula_to_latex_string(left)} \\land {lift_formula_to_latex_string(right)})"
    elif is_neg_disjunction(formula):
        left, right = get_disjuncts(formula.operand)
        return f"\\sim ({lift_formula_to_latex_string(left)} \\lor {lift_formula_to_latex_string(right)})"
    elif is_double_negation(formula):
        return f"\\sim \\sim {lift_formula_to_latex_string(get_neg(get_neg(formula)))}"
    else:
        return str(formula)

def lift_proof_to_bussproofs(proof: ProofNode) -> str:
    if not proof.premises:
        if proof.rule not in ["A", "~A"]:
            raise ValueError(f"Premises are empty, but rule is not A: {proof.rule}.")

        alpha_latex = lift_formula_to_latex_string(proof.sequent[0])
        beta_latex = lift_formula_to_latex_string(proof.sequent[1])

        return "\\AxiomC{}\n\\RightLabel{$" + ("\\sim " if proof.rule == "~A" else "") \
        + f"A$}}\n\\UnaryInfC{{${alpha_latex} \\Rightarrow {beta_latex}$}}"
    
    premises_latex = []
    for premise in proof.premises:
        premises_latex.append(lift_proof_to_bussproofs(premise))
    
    alpha_latex = lift_formula_to_latex_string(proof.sequent[0])
    beta_latex = lift_formula_to_latex_string(proof.sequent[1])

    rulestr = ""
    if proof.rule.startswith("∧L"):
        rulestr = f"\\RightLabel{{$\\land_{{{proof.rule[1:]}}}$}}"
    elif proof.rule.startswith("∨L"):
        rulestr = f"\\RightLabel{{$\\lor_{{L}}$}}"
    elif proof.rule.startswith("∧R"):
        rulestr = f"\\RightLabel{{$\\land_{{R}}$}}"
    elif proof.rule.startswith("∨R"):
        rulestr = f"\\RightLabel{{$\\lor_{{{proof.rule[1:]}}}$}}"
    elif proof.rule == "~~L":
        rulestr = "\\RightLabel{$\\sim \\sim_{L}$}"
    elif proof.rule == "~~R":
        rulestr = "\\RightLabel{$\\sim \\sim_{R}$}"
    elif proof.rule == "~∧L":
        rulestr = "\\RightLabel{$\\sim \\land_{L}$}"
    elif proof.rule == "~∨R":
        rulestr = "\\RightLabel{$\\sim \\lor_{R}$}"
    elif proof.rule.startswith("~∧R"):
        rulestr = f"\\RightLabel{{$\\sim \\land_{{{proof.rule[2:]}}}$}}"
    elif proof.rule.startswith("~∨L"):
        rulestr = f"\\RightLabel{{$\\sim \\lor_{{{proof.rule[2:]}}}$}}"
    elif proof.rule in ["A", "~A"]:
        rulestr = f"\\RightLabel{{${proof.rule}$}}"
    else:
        raise ValueError(f"Unknown rule: {proof.rule}")
    
    if len(proof.premises) == 1:
        return f"{premises_latex[0]}\n{rulestr}\n\\UnaryInfC{{${alpha_latex} \\Rightarrow {beta_latex}$}}"
    elif len(proof.premises) == 2:
        return f"{premises_latex[0]}\n{premises_latex[1]}\n{rulestr}\n\\BinaryInfC{{${alpha_latex} \\Rightarrow {beta_latex}$}}"
    else:
        raise ValueError("More than 2 premises in a proof node, which is not supported in monosequents.")

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

def and_formula(left: Formula, right: Formula) -> BinaryCompound:
    return BinaryCompound(ConnectiveType.AND, left, right)

def or_formula(left: Formula, right: Formula) -> BinaryCompound:
    return BinaryCompound(ConnectiveType.OR, left, right)

def not_formula(operand: Formula) -> UnaryCompound:
    return UnaryCompound(ConnectiveType.NOT, operand)

# Test cases
if __name__ == "__main__":
    p = atom("p")
    q = atom("q")
    r = atom("r")
    s = atom("s")

    assertion_print("\n=== RUNNING ORIGINAL TESTS ===")
    
    assertion_print("\n=== ATOM TESTS ===")
    # Test 1: Identity
    test_derivable((p, p), True, "Test 1 failed: p ⟹  p")
    # Test 2: Different atoms
    test_derivable((p, q), False, "Test 2 failed: p ⟹  q should be False")
    assertion_print("Passed!")
    
    assertion_print("\n=== CONJUNCTION TESTS ===")
    # Test 3: Conjunction elimination (∧L1)
    pq = and_formula(p, q)
    test_derivable((pq, p), True, "Test 3 failed: p ∧ q ⟹  p")
    # Test 4: Conjunction elimination (∧L2)
    test_derivable((pq, q), True, "Test 4 failed: p ∧ q ⟹  q")
    # Test 5: Conjunction introduction (∧R)
    test_derivable((p, and_formula(p, p)), True, "Test 5 failed: p ⟹  p ∧ p")
    # Test 6: Invalid conjunction introduction
    test_derivable((p, pq), False, "Test 6 failed: p ⟹  p ∧ q should be False")
    # Test 7: Conjunction commutativity
    qp = and_formula(q, p)
    test_derivable((pq, qp), True, "Test 7 failed: p ∧ q ⟹  q ∧ p")
    assertion_print("Passed!")
    
    assertion_print("\n=== DISJUNCTION TESTS ===")
    pq_or = or_formula(p, q)
    # Test 8: Disjunction introduction (∨R1)
    test_derivable((p, pq_or), True, "Test 8 failed: p ⟹  p ∨ q")
    # Test 9: Disjunction introduction (∨R2)
    test_derivable((q, pq_or), True, "Test 9 failed: q ⟹  p ∨ q")
    # Test 10: Disjunction elimination (∨L) - both cases must lead to conclusion
    test_derivable((pq_or, pq_or), True, "Test 10 failed: p ∨ q ⟹  p ∨ q")
    # Test 11: Invalid disjunction elimination
    test_derivable((pq_or, p), False, "Test 11 failed: p ∨ q ⟹  p should be False")
    # Test 12: Disjunction commutativity
    qp_or = or_formula(q, p)
    test_derivable((pq_or, qp_or), True, "Test 12 failed: p ∨ q ⟹  q ∨ p")
    assertion_print("Passed!")
    
    assertion_print("\n=== COMPLEX TESTS ===")
    # Test 13: Distributivity: p ∧ (q ∨ r) ⟹  (p ∧ q) ∨ (p ∧ r)
    qr_or = or_formula(q, r)
    qr_and = and_formula(q, r)
    p_and_qr_or = and_formula(p, qr_or)
    p_or_qr_and = or_formula(p, qr_and)
    pq_and = and_formula(p, q)
    pq_or = or_formula(p, q)
    pr_and = and_formula(p, r)
    pr_or = or_formula(p, r)
    pq_or_pr = or_formula(pq_and, pr_and)
    pq_and_pr = and_formula(pq_or, pr_or)
    test_derivable((p_and_qr_or, pq_or_pr), False, "Test 13a failed: p ∧ (q ∨ r) ⟹  (p ∧ q) ∨ (p ∧ r)")
    test_derivable((p_or_qr_and, pq_and_pr), True, "Test 13b failed: p ∨ (q ∧ r) ⟹  (p ∨ q) ∧ (p ∨ r)")
    # Test 14: Reverse distributivity
    test_derivable((pq_or_pr, p_and_qr_or), True, "Test 14a failed: (p ∧ q) ∨ (p ∧ r) ⟹  p ∧ (q ∨ r)")
    test_derivable((pq_and_pr, p_or_qr_and), False, "Test 14b failed: (p ∨ q) ∧ (p ∨ r) ⟹  p ∨ (q ∧ r)")


    # Test 15: Associativity: (p ∧ q) ∧ r ⟹  p ∧ (q ∧ r)
    pq_and_r = and_formula(pq, r)
    qr_and = and_formula(q, r)
    p_and_qr = and_formula(p, qr_and)
    test_derivable((pq_and_r, p_and_qr), True, "Test 15 failed: (p ∧ q) ∧ r ⟹  p ∧ (q ∧ r)")
    # Test 16: Disjunction associativity: (p ∨ q) ∨ r ⟹  p ∨ (q ∨ r)
    pq_or_r = or_formula(pq_or, r)
    p_or_qr = or_formula(p, qr_or)
    test_derivable((pq_or_r, p_or_qr), True, "Test 16 failed: (p ∨ q) ∨ r ⟹  p ∨ (q ∨ r)")
    # Test 17: Absorption: p ∧ (p ∨ q) ⟹  p
    p_and_p_or_q = and_formula(p, pq_or)
    test_derivable((p_and_p_or_q, p), True, "Test 17 failed: p ∧ (p ∨ q) ⟹  p")
    # Test 18: Reverse absorption: p ⟹  p ∧ (p ∨ q)
    test_derivable((p, p_and_p_or_q), True, "Test 18 failed: p ⟹  p ∧ (p ∨ q)")
    # Test 19: More complex formula
    rs_and = and_formula(r, s)
    pq_or_rs = or_formula(pq, rs_and)
    pr_or = or_formula(p, r)
    qs_or = or_formula(q, s)
    pr_and_qs = and_formula(pr_or, qs_or)
    test_derivable((pq_or_rs, pr_and_qs), True, "Test 19 failed: (p ∧ q) ∨ (r ∧ s) ⟹  (p ∨ r) ∧ (q ∨ s)")
    # Test 20: The reverse (should be False)
    test_derivable((pr_and_qs, pq_or_rs), False, "Test 20 failed: (p ∨ r) ∧ (q ∨ s) ⟹  (p ∧ q) ∨ (r ∧ s) should be False")
    assertion_print("Passed!")
    assertion_print("\n=== NEGATION TESTS ===")
    # Test 21: Negated atom identity
    not_p = not_formula(p)
    test_derivable((not_p, not_p), True, "Test 21 failed: ~p ⟹  ~p")
    
    # Test 22: Double negation elimination (~~L)
    not_not_p = not_formula(not_p)
    test_derivable((not_not_p, p), True, "Test 22 failed: ~~p ⟹  p")
    
    # Test 23: Double negation introduction (~~R)
    test_derivable((p, not_not_p), True, "Test 23 failed: p ⟹  ~~p")
    
    # Test 24: De Morgan's law: ~(p ∧ q) ⟹  ~p ∨ ~q
    not_pq_and = not_formula(pq)
    not_p_or_not_q = or_formula(not_p, not_formula(q))
    test_derivable((not_pq_and, not_p_or_not_q), True, "Test 24 failed: ~(p ∧ q) ⟹  ~p ∨ ~q")
    
    # Test 25: De Morgan's law: ~p ∨ ~q ⟹  ~(p ∧ q)
    test_derivable((not_p_or_not_q, not_pq_and), True, "Test 25 failed: ~p ∨ ~q ⟹  ~(p ∧ q)")
    
    # Test 26: De Morgan's law: ~(p ∨ q) ⟹  ~p ∧ ~q
    not_pq_or = not_formula(pq_or)
    not_p_and_not_q = and_formula(not_p, not_formula(q))
    test_derivable((not_pq_or, not_p_and_not_q), True, "Test 26 failed: ~(p ∨ q) ⟹  ~p ∧ ~q")
    
    # Test 27: De Morgan's law: ~p ∧ ~q ⟹  ~(p ∨ q)
    test_derivable((not_p_and_not_q, not_pq_or), True, "Test 27 failed: ~p ∧ ~q ⟹  ~(p ∨ q)")
    
    # Test 28: Triple negation: ~~~p ⟹  ~p
    not_not_not_p = not_formula(not_not_p)
    test_derivable((not_not_not_p, not_p), True, "Test 28 failed: ~~~p ⟹  ~p")
    
    # Test 29: Contradiction (should fail)
    test_derivable((p, not_p), False, "Test 29 failed: p ⟹  ~p should be False")
    
    # Test 30: Contradiction reverse (should fail)
    test_derivable((not_p, p), False, "Test 30 failed: ~p ⟹  p should be False")
    assertion_print("Passed!")
    
    assertion_print("\n=== COMPLEX NEGATION TESTS ===")
    # Test 31: ~(p ∧ ~q) ⟹  ~p ∨ q
    not_q = not_formula(q)
    p_and_not_q = and_formula(p, not_q)
    not_p_and_not_q = not_formula(p_and_not_q)
    not_p_or_q = or_formula(not_p, q)
    test_derivable((not_p_and_not_q, not_p_or_q), True, "Test 31 failed: ~(p ∧ ~q) ⟹  ~p ∨ q")
    
    # Test 32: ~(~p ∨ q) ⟹  p ∧ ~q
    not_p_or_q_formula = or_formula(not_p, q)
    not_not_p_or_q = not_formula(not_p_or_q_formula)
    p_and_not_q_result = and_formula(p, not_q)
    test_derivable((not_not_p_or_q, p_and_not_q_result), True, "Test 32 failed: ~(~p ∨ q) ⟹  p ∧ ~q")
    
    # Test 33: Double De Morgan: ~(~p ∧ ~q) ⟹  p ∨ q
    not_not_p_and_not_q = not_formula(not_p_and_not_q)
    test_derivable((not_not_p_and_not_q, pq_or), True, "Test 33 failed: ~(~p ∧ ~q) ⟹  p ∨ q")
    
    # Test 34: Nested negation: ~(p ∨ ~(q ∧ r)) ⟹  ~p ∧ (q ∧ r)
    qr_and = and_formula(q, r)
    not_qr_and = not_formula(qr_and)
    p_or_not_qr = or_formula(p, not_qr_and)
    not_p_or_not_qr = not_formula(p_or_not_qr)
    not_p_and_qr = and_formula(not_p, qr_and)
    test_derivable((not_p_or_not_qr, not_p_and_qr), True, "Test 34 failed: ~(p ∨ ~(q ∧ r)) ⟹  ~p ∧ (q ∧ r)")
    
    # Test 35: Complex mixed formula: (p ∧ ~q) ∨ (~p ∧ q) ⟹  ~(p ∧ q) ∨ ~(~p ∧ ~q)
    p_and_not_q = and_formula(p, not_q)
    not_p_and_q = and_formula(not_p, q)
    mixed_or = or_formula(p_and_not_q, not_p_and_q)
    not_pq_and = not_formula(pq)
    not_not_p_and_not_q = not_formula(not_p_and_not_q)
    result_or = or_formula(not_pq_and, not_not_p_and_not_q)
    test_derivable((mixed_or, result_or), True, "Test 35 failed: (p ∧ ~q) ∨ (~p ∧ q) ⟹  ~(p ∧ q) ∨ ~(~p ∧ ~q)")
    assertion_print("Passed!")
    
    if PRODUCE_PROOFS:
        with open("proofs_pql.tex", "w") as f:
            template_data = ""
            with open("a.template", "r") as g:
                template_data = g.read()
                final = template_data + proof_data + "\n\\end{document}"
                f.write(final)

        subprocess.run(["pdflatex", "proofs_pql.tex"], check=True)
        subprocess.run(["rm", "proofs_pql.aux", "proofs_pql.log", "proofs_pql.out"], check=True)



