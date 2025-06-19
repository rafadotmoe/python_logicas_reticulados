import ply.lex as lex
import ply.yacc as yacc
import os
import time
import subprocess

import nql

tokens = (
    'ATOM',
    'AND',
    'OR',
    'IMP',
    'COIMP',
    'NOT',
    'BOT',
    'TOP',
    'LPAREN',
    'RPAREN',
    'SEQ'
)

t_AND = r'and'
t_OR = r'or'
t_IMP = r'imp'
t_COIMP = r'coimp'
t_NOT = r'not'
t_BOT = r'bot'
t_TOP = r'top'
t_LPAREN = r'\('
t_RPAREN = r'\)'
t_SEQ = r'=>'
t_ignore = ' \t'

reserved = {
    'and': 'AND',
    'or': 'OR',
    'imp': 'IMP',
    'coimp': 'COIMP',
    'not': 'NOT',
    'bot': 'BOT',
    'top': 'TOP',
}

def error_out(msg):
    print("Error:")
    print(msg)
    exit(1)

def t_ATOM(t):
    r'[a-zA-Z][a-zA-Z0-9_]*'

    t.type = reserved.get(t.value, 'ATOM')

    return t

def t_newline(t):
    r'\n+'

    t.lexer.lineno += len(t.value)

def t_error(t):
    error_out(f"Illegal character '{t.value[0]}' at line {t.lineno}")

precedence = (
    ('left', 'OR'),
    ('left', 'AND'),
    ('left', 'IMP', 'COIMP'),
    ('right', 'NOT')
)

def p_sequent(p):
    '''sequent : expression SEQ expression'''
    p[0] = (p[1], p[3])

def p_expression_atom(p):
    '''expression : ATOM'''
    p[0] = nql.atom(p[1])

def p_expression_bot(p):
    '''expression : BOT'''
    p[0] = nql.bot()

def p_expression_top(p):
    '''expression : TOP'''
    p[0] = nql.top()

def p_expression_not(p):
    '''expression : NOT expression'''
    p[0] = nql.not_formula(p[2])

def p_expression_and(p):
    '''expression : expression AND expression'''
    p[0] = nql.and_formula(p[1], p[3])

def p_expression_or(p):
    '''expression : expression OR expression'''
    p[0] = nql.or_formula(p[1], p[3])

def p_expression_imp(p):
    '''expression : expression IMP expression'''
    p[0] = nql.imp_formula(p[1], p[3])

def p_expression_coimp(p):
    '''expression : expression COIMP expression'''
    p[0] = nql.coimp_formula(p[1], p[3])

def p_expression_group(p):
    '''expression : LPAREN expression RPAREN'''
    p[0] = p[2]

def p_error(p):
    if p:
        error_out(f"Syntax error at '{p.value}' on line {p.lineno}")
    error_out("Syntax error at EOF")


class Parser:
    def __init__(self):
        self.lexer = lex.lex()
        self.parser = yacc.yacc()

    def parse(self, s):
        try:
            result = self.parser.parse(s, lexer=self.lexer)
            return result
        except Exception as e:
            error_out(f"Parsing error: {e}")

    def parse_sequent(self, s):
        try:
            result = self.parser.parse(s, lexer=self.lexer)
            if isinstance(result, tuple) and len(result) == 2:
                return result
            else:
                error_out("Sequent must be of the form 'A => B'")
        except Exception as e:
            error_out(f"Parsing error: {e}")

    def is_sequent_symbol(self, s):
        return '=>' in s

parser = Parser()

def output_latex(proof, seq):
    if not proof:
        error_out("No proof to output")

    ext = input("Enter the name of the LaTeX document (without .tex): ")

    if not ext:
        ext = "proof"+time.strftime("%Y%m%d_%H%M%S")

    output_dir = "proofs_output"
    if os.path.exists(output_dir):
        for file in os.listdir(output_dir):
            if file.startswith(ext):
                os.remove(os.path.join(output_dir, file))
    else:
        os.makedirs(output_dir)

    template_dest = os.path.join(output_dir, "../a.template")

    proof_data = nql.lift_object_to_bussproofs(proof)
    formula_left = nql.lift_formula_to_latex_string(seq[0])
    formula_right = nql.lift_formula_to_latex_string(seq[1])
    proof_data = "\\paragraph{" + f"${formula_left} \\Rightarrow  {formula_right}$ \\\\\n""}" + "\\leavevmode"+"\n\n" \
    + "\\hfill\n\\break\n"*2 + proof_data + "\\hfill\n\\break\n"*2

    tex_file = os.path.join(output_dir, f"{ext}.tex")
    with open(tex_file, 'w') as f:
        template_data = ""
        with open(template_dest, 'r') as g:
            template_data = g.read()
            final = template_data + proof_data + "\n\\end{document}"
            f.write(final)

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


while True:
    try:
        s = input('nql> ')
    except EOFError:
        break
    if not s.strip():
        continue

    if s.lower() == 'q' or s.lower() == 'quit':
        break

    if not parser.is_sequent_symbol(s):
        error_out("Input must be a sequent of the form 'A => B'")

    seq = parser.parse_sequent(s)

    proof = nql.derive_proof(seq)

    if proof is not None:
        print("Proof found!")
        output_latex(proof, seq)
    else:
        print("No proof found!")
        continue
