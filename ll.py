from dataclasses import dataclass
from typing import Union, Tuple, List, Optional
from enum import Enum

class ConnectiveType(Enum):
    AND = "∧"
    OR = "∨"

@dataclass(frozen=True)
class Atom:
    name: str
    
    def __str__(self):
        return self.name

@dataclass(frozen=True)
class Compound:
    connective: ConnectiveType
    left: Union['Atom', 'Compound']
    right: Union['Atom', 'Compound']
    
    def __str__(self):
        return f"({self.left} {self.connective.value} {self.right})"

Formula = Union[Atom, Compound]

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
    return isinstance(formula, Compound) and formula.connective == ConnectiveType.AND

def is_disjunction(formula: Formula) -> bool:
    return isinstance(formula, Compound) and formula.connective == ConnectiveType.OR

def get_conjuncts(formula: Formula) -> Tuple[Formula, Formula]:
    assert is_conjunction(formula)
    return formula.left, formula.right

def get_disjuncts(formula: Formula) -> Tuple[Formula, Formula]:
    assert is_disjunction(formula)
    return formula.left, formula.right

def test_derivable(sequent: tuple[Formula, Formula], expected: bool, test_str: str, assertion: bool, proofs: bool):
    # print left and right pretty
    print(f"{str(sequent[0])} ⟹   {str(sequent[1])}")
    
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

def derive_proof(sequent: Tuple[Formula, Formula]) -> Optional[ProofNode]:
    alpha, beta = sequent
    
    # A (Axiom)
    if is_atom(alpha) and is_atom(beta) and alpha == beta:
        return ProofNode(sequent, "A", [])

    #### Left operations!
    # ∧L
    if is_conjunction(alpha):
        for i, ai in enumerate(get_conjuncts(alpha)):
            sub_proof = derive_proof((ai, beta))
            if sub_proof:
                return ProofNode(sequent, f"∧L{i+1}", [sub_proof])
    
    # ∨L
    if is_disjunction(alpha):
        a1, a2 = get_disjuncts(alpha)
        sub_proof_l = derive_proof((a1, beta))
        sub_proof_r = derive_proof((a2, beta))
        
        if sub_proof_l and sub_proof_r:
            return ProofNode(sequent, "∨L", [sub_proof_l, sub_proof_r])

    #### Right operations!
    # ∧R
    if is_conjunction(beta):
        b1, b2 = get_conjuncts(beta)
        sub_proof_l = derive_proof((alpha, b1))
        sub_proof_r = derive_proof((alpha, b2))
        
        if sub_proof_l and sub_proof_r:
            return ProofNode(sequent, "∧R", [sub_proof_l, sub_proof_r])

    # ∨R
    if is_disjunction(beta):
        for i, bi in enumerate(get_disjuncts(beta)):
            sub_proof = derive_proof((alpha, bi))
            if sub_proof:
                return ProofNode(sequent, f"∨R{i+1}", [sub_proof])
    
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
    else:
        return str(formula)

def lift_proof_to_bussproofs(proof: ProofNode) -> str:
    if not proof.premises:
        if proof.rule != "A":
            raise ValueError(f"Premises are empty, but rule is not A: {proof.rule}.")

        alpha_latex = lift_formula_to_latex_string(proof.sequent[0])
        beta_latex = lift_formula_to_latex_string(proof.sequent[1])

        return f"\\AxiomC{{}}\n\\RightLabel{{$A$}}\n\\UnaryInfC{{${alpha_latex} \\Rightarrow {beta_latex}$}}"
    
    premises_latex = []
    for premise in proof.premises:
        premises_latex.append(lift_proof_to_bussproofs(premise))
    
    alpha_latex = lift_formula_to_latex_string(proof.sequent[0])
    beta_latex = lift_formula_to_latex_string(proof.sequent[1])

    rulestr = ""
    if proof.rule[0] == "∧":
        rulestr = f"\\RightLabel{{$\\land_{{{proof.rule[1:]}}}$}}"
    elif proof.rule[0] == "∨":
        rulestr = f"\\RightLabel{{$\\lor_{{{proof.rule[1:]}}}$}}"
    elif proof.rule == "A":
        rulestr = "\\RightLabel{$A$}"
    else:
        raise ValueError(f"Unknown rule: {proof.rule}")
    
    if len(proof.premises) == 1:
        return f"{premises_latex[0]}\n{rulestr}\n\\UnaryInfC{{${alpha_latex} \\Rightarrow {beta_latex}$}}"
    elif len(proof.premises) == 2:
        return f"{premises_latex[0]}\n{premises_latex[1]}\n{rulestr}\n\\BinaryInfC{{${alpha_latex} \\Rightarrow  {beta_latex}$}}"
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

def and_formula(left: Formula, right: Formula) -> Compound:
    return Compound(ConnectiveType.AND, left, right)

def or_formula(left: Formula, right: Formula) -> Compound:
    return Compound(ConnectiveType.OR, left, right)
