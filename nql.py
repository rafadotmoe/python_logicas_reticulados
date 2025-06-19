from dataclasses import dataclass
from typing import Union, Tuple, List, Optional
from enum import Enum

class ConnectiveType(Enum):
    AND = "∧"
    OR = "∨"
    IMP = "⊃"
    COIMP = "⊂"
    NOT = "~"

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
class UnaryCompound:
    connective: ConnectiveType
    operand: Union['Atom', 'Compound', 'UnaryCompound', 'Bot', 'Top']

    def __str__(self):
        return f"{self.connective.value}{self.operand}"

@dataclass(frozen=True)
class Compound:
    connective: ConnectiveType
    left: Union['Atom', 'Compound', 'UnaryCompound', 'Bot', 'Top']
    right: Union['Atom', 'Compound', 'UnaryCompound', 'Bot', 'Top']
    
    def __str__(self):
        return f"({self.left} {self.connective.value} {self.right})"

Formula = Union[Atom, UnaryCompound, Compound, Bot, Top]

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


def is_negation(formula: Formula) -> bool:
    return isinstance(formula, UnaryCompound) and formula.connective == ConnectiveType.NOT

def is_double_negation(formula: Formula) -> bool:
    return is_negation(formula) and is_negation(formula.operand)

def is_neg_conjunction(formula: Formula) -> bool:
    return is_negation(formula) and is_conjunction(formula.operand)

def is_neg_disjunction(formula: Formula) -> bool:
    return is_negation(formula) and is_disjunction(formula.operand)

def is_neg_imp(formula: Formula) -> bool:
    return is_negation(formula) and is_imp(formula.operand)

def is_neg_coimp(formula: Formula) -> bool:
    return is_negation(formula) and is_coimp(formula.operand)

def is_neg_atom(formula: Formula) -> bool:
    return is_negation(formula) and is_atom(formula.operand)

def is_neg_bot(formula: Formula) -> bool:
    return is_negation(formula) and is_bot(formula.operand)

def is_neg_top(formula: Formula) -> bool:
    return is_negation(formula) and is_top(formula.operand)

def get_neg(formula: Formula) -> Formula:
    assert is_negation(formula)
    return formula.operand

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

def get_neg_conjuncts(formula: Formula) -> Tuple[Formula, Formula]:
    assert is_neg_conjunction(formula)
    return not_formula(get_conjuncts(formula.operand)[0]), not_formula(get_conjuncts(formula.operand)[1])

def get_neg_disjuncts(formula: Formula) -> Tuple[Formula, Formula]:
    assert is_neg_disjunction(formula)
    return not_formula(get_disjuncts(formula.operand)[0]), not_formula(get_disjuncts(formula.operand)[1])

def get_neg_imp_parts(formula: Formula) -> Tuple[Formula, Formula]:
    assert is_neg_imp(formula)
    alpha, beta = get_imp_parts(formula.operand)
    return alpha, not_formula(beta)

def get_neg_coimp_parts(formula: Formula) -> Tuple[Formula, Formula]:
    assert is_neg_coimp(formula)
    alpha, beta = get_coimp_parts(formula.operand)
    return not_formula(alpha), beta

def test_derivable(sequent: tuple[Formula, Formula], expected: bool, test_str: str, assertion: bool, proofs: bool):
    global proof_data
    
    if assertion:
        result = is_derivable(sequent)
        assert result == expected, f"{test_str}"
    
    if expected and proofs:

        status_text = "Sequente derivável"
        formula_left = lift_formula_to_latex_string(sequent[0])
        formula_right = lift_formula_to_latex_string(sequent[1])

        return ("\\paragraph{" + test_str[:test_str.index(":")+1].replace("failed", "") + " " + f"${formula_left} \\Rightarrow  {formula_right}$ \\\\\n""}"  + "\\leavevmode"+"\n\n"+
                      f"\\text{{{status_text}}}\n" +
                      "\\hfill\n\\break\n"*2+ 
            lift_object_to_bussproofs(derive_proof(sequent)) + "\\hfill\n\\break\n"*2)

    formula_left = lift_formula_to_latex_string(sequent[0])
    formula_right = lift_formula_to_latex_string(sequent[1])
    if expected:
        # This case happens when expected is True but PRODUCE_PROOFS is False
        status_text = "Derivable (proof generation disabled)"
    else:
        # This case happens when expected is False
        status_text = "Sequente não derivável"
    
    return ("\\paragraph{" + test_str[:test_str.index(":")+1].replace("failed", "") + " " +f"${formula_left} \\Rightarrow  {formula_right}$ \\\\\n""}"  + "\\leavevmode"+"\n\n"+
                    f"\\text{{{status_text}}}\n" +
                    "\\hfill\n\\break\n"*2)


cache = {}
weaks = []

def derive_proof(sequent: Tuple[Formula, Formula]) -> Optional[ProofNode]:
    global cache, weaks
    cache = {}
    weaks = []
    return derive_proof_inner(sequent)

def derive_proof_inner(sequent: Tuple[Formula, Formula]) -> Optional[ProofNode]:
    global cache, weaks

    if sequent in cache:
        return cache[sequent]

    alpha, beta = sequent
    
    # A (Axiom)
    if is_atom(alpha) and is_atom(beta) and alpha.name == beta.name:
        result = ProofNode(sequent, "A", [])
        cache[sequent] = result
        return result

    # ~A (Axiom)
    if is_neg_atom(alpha) and is_neg_atom(beta) and alpha == beta:
        result = ProofNode(sequent, "~A", [])
        cache[sequent] = result
        return result
    
    # ⊥ rule: ⊥ ⟹   α
    if is_bot(alpha):
        result = ProofNode(sequent, "⊥", [])
        cache[sequent] = result
        return result

    # ~⊥ rule: α ⟹  ~⊥
    if is_neg_bot(beta):
        result = ProofNode(sequent, "~⊥", [])
        cache[sequent] = result
        return result
    
    # ⊤ rule: α ⟹   ⊤
    if is_top(beta):
        result = ProofNode(sequent, "⊤", [])
        cache[sequent] = result
        return result

    # ~⊤ rule: ~⊤ ⟹  α
    if is_neg_top(alpha):
        result = ProofNode(sequent, "~⊤", [])
        cache[sequent] = result
        return result

    # Weakening rules

    # we_L: if ⊤ ⟹   β then α ⟹   β
    if not is_top(alpha) and weaks.count(not_formula(Bot())) <= 2:
        weaks.append(Top())
        top_to_beta = derive_proof_inner((Top(), beta))
        if top_to_beta:
            result = ProofNode(sequent, "we_L", [top_to_beta])
            cache[sequent] = result
            return result
    
    # we_R: if α ⟹   ⊥ then α ⟹   β
    if not is_bot(beta) and weaks.count(not_formula(Top())) <= 2:
        weaks.append(Bot())
        alpha_to_bot = derive_proof_inner((alpha, Bot()))
        if alpha_to_bot:
            result = ProofNode(sequent, "we_R", [alpha_to_bot])
            cache[sequent] = result
            return result

    # ~we_L: if ~⊥ ⟹  α then β ⟹  α
    if not is_neg_bot(alpha) and weaks.count(Top()) <= 2:
        weaks.append(not_formula(Bot()))
        neg_bot_to_alpha = derive_proof_inner((not_formula(Bot()), beta))
        if neg_bot_to_alpha:
            result = ProofNode(sequent, "~we_L", [neg_bot_to_alpha])
            cache[sequent] = result
            return result

    # ~we_R: if α ⟹  ~⊤ then α ⟹  β
    if not is_neg_top(beta) and weaks.count(Bot()) <= 2:
        weaks.append(not_formula(Top()))
        alpha_to_neg_top = derive_proof_inner((alpha, not_formula(Top())))
        if alpha_to_neg_top:
            result = ProofNode(sequent, "~we_R", [alpha_to_neg_top])
            cache[sequent] = result
            return result

    #### Left operations!
    # ~~L
    if is_double_negation(alpha):
        sub_proof = derive_proof_inner((get_neg(get_neg(alpha)), beta))
        if sub_proof:
            result = ProofNode(sequent, "~~L", [sub_proof])
            cache[sequent] = result
            return result

    # ∧L
    if is_conjunction(alpha):
        for i, ai in enumerate(get_conjuncts(alpha)):
            sub_proof = derive_proof_inner((ai, beta))
            if sub_proof:
                result = ProofNode(sequent, f"∧L{i+1}", [sub_proof])
                cache[sequent] = result
                return result

    # ~∧L
    if is_neg_conjunction(alpha):
        a1, a2 = get_neg_conjuncts(alpha)
        sub_proof_l = derive_proof_inner((a1, beta))
        sub_proof_r = derive_proof_inner((a2, beta))
        
        if sub_proof_l and sub_proof_r:
            result = ProofNode(sequent, "~∧L", [sub_proof_l, sub_proof_r])
            cache[sequent] = result
            return result

    # ∨L
    if is_disjunction(alpha):
        a1, a2 = get_disjuncts(alpha)
        sub_proof_l = derive_proof_inner((a1, beta))
        sub_proof_r = derive_proof_inner((a2, beta))
        
        if sub_proof_l and sub_proof_r:
            result = ProofNode(sequent, "∨L", [sub_proof_l, sub_proof_r])
            cache[sequent] = result
            return result

    # ~∨L
    if is_neg_disjunction(alpha):
        for i, ai in enumerate(get_neg_disjuncts(alpha)):
            sub_proof = derive_proof_inner((ai, beta))
            if sub_proof:
                result = ProofNode(sequent, f"~∨L{i+1}", [sub_proof])
                cache[sequent] = result
                return result

    # ⊃L
    if is_imp(alpha):
        a1, a2 = get_imp_parts(alpha)
        top_to_a1 = derive_proof_inner((Top(), a1))
        a2_to_beta = derive_proof_inner((a2, beta))
        
        if top_to_a1 and a2_to_beta:
            result = ProofNode(sequent, "⊃L", [top_to_a1, a2_to_beta])
            cache[sequent] = result
            return result

    # ~⊃L
    if is_neg_imp(alpha):
        a1, neg_a2 = get_neg_imp_parts(alpha)
        
        # Try ~⊃L1: from α ⟹  δ derive ~(α ⊃ β) ⟹  δ
        sub_proof = derive_proof_inner((a1, beta))
        if sub_proof:
            result = ProofNode(sequent, "~⊃L1", [sub_proof])
            cache[sequent] = result
            return result
            
        # Try ~⊃L2: from ~β ⟹  δ derive ~(α ⊃ β) ⟹  δ
        sub_proof = derive_proof_inner((neg_a2, beta))
        if sub_proof:
            result = ProofNode(sequent, "~⊃L2", [sub_proof])
            cache[sequent] = result
            return result

    # ⊂L
    if is_coimp(alpha) and is_bot(beta):
        a1, a2 = get_coimp_parts(alpha)
        a1_to_a2 = derive_proof_inner((a1, a2))
        if a1_to_a2:
            result = ProofNode(sequent, "⊂L", [a1_to_a2])
            cache[sequent] = result
            return result

    # ~⊂L
    if is_neg_coimp(alpha):
        neg_a1, a2 = get_neg_coimp_parts(alpha)
        sub_proof_l = derive_proof_inner((neg_a1, beta))
        sub_proof_r = derive_proof_inner((a2, beta))
        
        if sub_proof_l and sub_proof_r:
            result = ProofNode(sequent, "~⊂L", [sub_proof_l, sub_proof_r])
            cache[sequent] = result
            return result

    #### Right operations
    # ~~R
    if is_double_negation(beta):
        sub_proof = derive_proof_inner((alpha, get_neg(get_neg(beta))))
        if sub_proof:
            result = ProofNode(sequent, "~~R", [sub_proof])
            cache[sequent] = result
            return result

    # ∧R
    if is_conjunction(beta):
        b1, b2 = get_conjuncts(beta)
        sub_proof_l = derive_proof_inner((alpha, b1))
        sub_proof_r = derive_proof_inner((alpha, b2))
        
        if sub_proof_l and sub_proof_r:
            result = ProofNode(sequent, "∧R", [sub_proof_l, sub_proof_r])
            cache[sequent] = result
            return result

    # ~∧R
    if is_neg_conjunction(beta):
        for i, bi in enumerate(get_neg_conjuncts(beta)):
            sub_proof = derive_proof_inner((alpha, bi))
            if sub_proof:
                result = ProofNode(sequent, f"~∧R{i+1}", [sub_proof])
                cache[sequent] = result
                return result

    # ∨R
    if is_disjunction(beta):
        for i, bi in enumerate(get_disjuncts(beta)):
            sub_proof = derive_proof_inner((alpha, bi))
            if sub_proof:
                result = ProofNode(sequent, f"∨R{i+1}", [sub_proof])
                cache[sequent] = result
                return result
    
    # ~∨R
    if is_neg_disjunction(beta):
        b1, b2 = get_neg_disjuncts(beta)
        sub_proof_l = derive_proof_inner((alpha, b1))
        sub_proof_r = derive_proof_inner((alpha, b2))

        if sub_proof_l and sub_proof_r:
            result = ProofNode(sequent, "~∨R", [sub_proof_l, sub_proof_r])
            cache[sequent] = result
            return result

    # ⊃R
    if is_imp(beta) and is_top(alpha):
        b1, b2 = get_imp_parts(beta)
        b1_to_b2 = derive_proof_inner((b1, b2))
        if b1_to_b2:
            result = ProofNode(sequent, "⊃R", [b1_to_b2])
            cache[sequent] = result
            return result

    # ~⊃R
    if is_neg_imp(beta):
        b1, neg_b2 = get_neg_imp_parts(beta)
        alpha_to_b1 = derive_proof_inner((alpha, b1))
        alpha_to_neg_b2 = derive_proof_inner((alpha, neg_b2))
        
        if alpha_to_b1 and alpha_to_neg_b2:
            result = ProofNode(sequent, "~⊃R", [alpha_to_b1, alpha_to_neg_b2])
            cache[sequent] = result
            return result

    # ⊂R
    if is_coimp(beta):
        b1, b2 = get_coimp_parts(beta)
        alpha_to_b1 = derive_proof_inner((alpha, b1))
        b2_to_bot = derive_proof_inner((b2, Bot()))
        
        if alpha_to_b1 and b2_to_bot:
            result = ProofNode(sequent, "⊂R", [alpha_to_b1, b2_to_bot])
            cache[sequent] = result
            return result

    # ~⊂R
    if is_neg_coimp(beta):
        neg_b1, b2 = get_neg_coimp_parts(beta)
        
        # Try ~⊂R1: from α ⟹  ~β₁ derive α ⟹  ~(β₁ ⊂ β₂)
        sub_proof = derive_proof_inner((alpha, neg_b1))
        if sub_proof:
            result = ProofNode(sequent, "~⊂R1", [sub_proof])
            cache[sequent] = result
            return result
            
        # Try ~⊂R2: from α ⟹  β₂ derive α ⟹  ~(β₁ ⊂ β₂)
        sub_proof = derive_proof_inner((alpha, b2))
        if sub_proof:
            result = ProofNode(sequent, "~⊂R2", [sub_proof])
            cache[sequent] = result
            return result

    #### Order operations
    # ⊃_order
    if is_imp(alpha) and is_imp(beta):
        a1, a2 = get_imp_parts(alpha)
        b1, b2 = get_imp_parts(beta)
        
        b1_to_a1 = derive_proof_inner((b1, a1))
        a2_to_b2 = derive_proof_inner((a2, b2))
        
        if b1_to_a1 and a2_to_b2:
            result = ProofNode(sequent, "⊃order", [b1_to_a1, a2_to_b2])
            cache[sequent] = result
            return result

    # ⊂_order
    if is_coimp(alpha) and is_coimp(beta):
        a1, a2 = get_coimp_parts(alpha)
        b1, b2 = get_coimp_parts(beta)
        
        a1_to_b1 = derive_proof_inner((a1, b1))
        b2_to_a2 = derive_proof_inner((b2, a2))
        
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
    elif is_neg_atom(formula):
        return f"\\sim {formula.operand.name}"
    elif is_neg_bot(formula):
        return "\\sim \\bot"
    elif is_neg_top(formula):
        return "\\sim \\top"
    elif is_neg_conjunction(formula):
        left, right = get_conjuncts(formula.operand)
        return f"\\sim ({lift_formula_to_latex_string(left)} \\land {lift_formula_to_latex_string(right)})"
    elif is_neg_disjunction(formula):
        left, right = get_disjuncts(formula.operand)
        return f"\\sim ({lift_formula_to_latex_string(left)} \\lor {lift_formula_to_latex_string(right)})"
    elif is_neg_imp(formula):
        left, right = get_imp_parts(formula.operand)
        return f"\\sim ({lift_formula_to_latex_string(left)} \\supset {lift_formula_to_latex_string(right)})"
    elif is_neg_coimp(formula):
        left, right = get_coimp_parts(formula.operand)
        return f"\\sim ({lift_formula_to_latex_string(left)} \\subset {lift_formula_to_latex_string(right)})"
    elif is_double_negation(formula):
        return f"\\sim \\sim {lift_formula_to_latex_string(get_neg(get_neg(formula)))}"
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
        elif proof.rule == "~A":
            rule_latex = "\\RightLabel{$\\sim A$}"
        elif proof.rule == "⊥":
            rule_latex = "\\RightLabel{$\\bot$}"
        elif proof.rule == "~⊥":
            rule_latex = "\\RightLabel{$\\sim\\bot$}"
        elif proof.rule == "⊤":
            rule_latex = "\\RightLabel{$\\top$}"
        elif proof.rule == "~⊤":
            rule_latex = "\\RightLabel{$\\sim\\top$}"
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
    elif proof.rule == "~we_L":
        rulestr = "\\RightLabel{$\\sim we_L$}"
    elif proof.rule == "~we_R":
        rulestr = "\\RightLabel{$\\sim we_R$}"
    elif proof.rule in ["∧L1", "∧L2"]:
        rulestr = f"\\RightLabel{{$\\land_{{{proof.rule[1:]}}}$}}"
    elif proof.rule == "∧R":
        rulestr = "\\RightLabel{$\\land_R$}"
    elif proof.rule == "~∧L":
        rulestr = "\\RightLabel{$\\sim \\land_{L}$}"
    elif proof.rule in ["~∧R1", "~∧R2"]:
        rulestr = f"\\RightLabel{{$\\sim \\land_{{{proof.rule[2:]}}}$}}"
    elif proof.rule == "∨L":
        rulestr = "\\RightLabel{$\\lor_L$}"
    elif proof.rule in ["∨R1", "∨R2"]:
        rulestr = f"\\RightLabel{{$\\lor_{{{proof.rule[1:]}}}$}}"
    elif proof.rule in ["~∨L1", "~∨L2"]:
        rulestr = f"\\RightLabel{{$\\sim \\lor_{{{proof.rule[2:]}}}$}}"
    elif proof.rule == "~∨R":
        rulestr = "\\RightLabel{$\\sim \\lor_{R}$}"
    elif proof.rule == "⊃L":
        rulestr = "\\RightLabel{$\\supset_L$}"
    elif proof.rule == "⊃R":
        rulestr = "\\RightLabel{$\\supset_R$}"
    elif proof.rule in ["~⊃L1", "~⊃L2"]:
        rulestr = f"\\RightLabel{{$\\sim \\supset_{{{proof.rule[3:]}}}$}}"
    elif proof.rule == "~⊃R":
        rulestr = "\\RightLabel{$\\sim \\supset_R$}"
    elif proof.rule == "⊂L":
        rulestr = "\\RightLabel{$\\subset_L$}"
    elif proof.rule == "⊂R":
        rulestr = "\\RightLabel{$\\subset_R$}"
    elif proof.rule == "~⊂L":
        rulestr = "\\RightLabel{$\\sim\\subset_{L}$}"
    elif proof.rule in ["~⊂R1", "~⊂R2"]:
        rulestr = f"\\RightLabel{{$\\sim\\subset_{{{proof.rule[3:]}}}$}}"
    elif proof.rule == "⊃order":
        rulestr = "\\RightLabel{$\\supset_{order}$}"
    elif proof.rule == "⊂order":
        rulestr = "\\RightLabel{$\\subset_{order}$}"
    elif proof.rule == "~~L":
        rulestr = "\\RightLabel{$\\sim \\sim_{L}$}"
    elif proof.rule == "~~R":
        rulestr = "\\RightLabel{$\\sim \\sim_{R}$}"
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

def not_formula(operand: Formula) -> UnaryCompound:
    return UnaryCompound(ConnectiveType.NOT, operand)

