from dataclasses import dataclass
from typing import Union, Tuple, List, Optional
from enum import Enum
import os
import subprocess

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

def to_latex_weak(proofs: List[Tuple[ProofNode, tuple[Formula, Formula]]], ext: str):
    if not ext:
        return False

    output_dir = "proofs_output"
    if os.path.exists(output_dir):
        for file in os.listdir(output_dir):
            if file.startswith(ext):
                os.remove(os.path.join(output_dir, file))
    else:
        os.makedirs(output_dir)

    template_dest = os.path.join(output_dir, "../a.template")
    tex_file = os.path.join(output_dir, f"{ext}.tex")

    with open(tex_file, 'w') as f:
        final = ""
        for proof, seq in proofs:
            formula_left = lift_formula_to_latex_string(seq[0])
            formula_right = lift_formula_to_latex_string(seq[1])

            if proof is None:
                status_text = "Sequente não derivável"
                init_data = "\\paragraph{" + f"${formula_left} \\Rightarrow  {formula_right}$ \\\\\n""}" + "\\leavevmode"+"\n\n" \
                + f"\\text{{{status_text}}}\n" \
                + "\\hfill\n\\break\n"*2

                proof_data = ""
            else:
                status_text = "Sequente derivável"
                init_data = "\\paragraph{" + f"${formula_left} \\Rightarrow  {formula_right}$ \\\\\n""}" + "\\leavevmode"+"\n\n" \
                + f"\\text{{{status_text}}}\n" \
                + "\\hfill\n\\break\n"*2

                proof_data = lift_object_to_bussproofs(proof)
                proof_data += "\\hfill\n\\break\n"*2


            proof_data = init_data + proof_data

            final += proof_data


        with open(template_dest, 'r') as g:
            template_data = g.read()
            f.write(template_data + final + "\n\\end{document}")


    original_cwd = os.getcwd()
    try:
        os.chdir(output_dir)
        subprocess.run(["pdflatex", ext + ".tex"], check=True)
        
        aux_files = [ext + ".aux", ext + ".log", ext + ".out"]
        for aux_file in aux_files:
            if os.path.exists(aux_file):
                os.remove(aux_file)
                
    finally:
        os.chdir(original_cwd)
    
    print(f"PDF generated successfully in {output_dir}/" + ext + ".pdf")

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

