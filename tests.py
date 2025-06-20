import subprocess
import os

import ll
import pql
import nl
import nql

PRODUCE_PROOFS = True
PERFORM_ASSERTION = True
PRINT_MARKERS = True

proof_data = ""

def generate_latex_output(pref):
    global proof_data
    if PRODUCE_PROOFS:
        output_dir = "proofs_output"
        ext = "proofs_" + pref
        if os.path.exists(output_dir):
            for file in os.listdir(output_dir):
                if file.startswith(ext):
                    os.remove(os.path.join(output_dir, file))
        else:
            os.makedirs(output_dir)

        template_dest = os.path.join(output_dir, "../a.template")
        
        tex_file = os.path.join(output_dir, ext + ".tex")
        with open(tex_file, "w") as f:
            template_data = ""
            with open(template_dest, "r") as g:
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

def assertion_print(msg: str):
    if PERFORM_ASSERTION and PRINT_MARKERS:
        print(msg)

def ll_tests():
    global proof_data
    proof_data = ""

    p = ll.atom("p")
    q = ll.atom("q")
    r = ll.atom("r")
    s = ll.atom("s")

    assertion_print("\n=== RUNNING ORIGINAL TESTS ===")
    
    assertion_print("\n=== ATOM TESTS ===")
    # Test 1: Identity
    proof_data += ll.test_derivable((p, p), True, "Test 1 failed: p ⟹  p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 2: Different atoms
    proof_data += ll.test_derivable((p, q), False, "Test 2 failed: p ⟹  q should be False", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")
    
    assertion_print("\n=== CONJUNCTION TESTS ===")
    # Test 3: Conjunction elimination (∧L1)
    pq = ll.and_formula(p, q)
    proof_data += ll.test_derivable((pq, p), True, "Test 3 failed: p ∧ q ⟹  p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 4: Conjunction elimination (∧L2)
    proof_data += ll.test_derivable((pq, q), True, "Test 4 failed: p ∧ q ⟹  q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 5: Conjunction introduction (∧R)
    proof_data += ll.test_derivable((p, ll.and_formula(p, p)), True, "Test 5 failed: p ⟹  p ∧ p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 6: Invalid conjunction introduction
    proof_data += ll.test_derivable((p, pq), False, "Test 6 failed: p ⟹  p ∧ q should be False", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 7: Conjunction commutativity
    qp = ll.and_formula(q, p)
    proof_data += ll.test_derivable((pq, qp), True, "Test 7 failed: p ∧ q ⟹  q ∧ p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")
    
    assertion_print("\n=== DISJUNCTION TESTS ===")
    pq_or = ll.or_formula(p, q)
    # Test 8: Disjunction introduction (∨R1)
    proof_data += ll.test_derivable((p, pq_or), True, "Test 8 failed: p ⟹  p ∨ q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 9: Disjunction introduction (∨R2)
    proof_data += ll.test_derivable((q, pq_or), True, "Test 9 failed: q ⟹  p ∨ q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 10: Disjunction elimination (∨L) - both cases must lead to conclusion
    proof_data += ll.test_derivable((pq_or, pq_or), True, "Test 10 failed: p ∨ q ⟹  p ∨ q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 11: Invalid disjunction elimination
    proof_data += ll.test_derivable((pq_or, p), False, "Test 11 failed: p ∨ q ⟹  p should be False", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 12: Disjunction commutativity
    qp_or = ll.or_formula(q, p)
    proof_data += ll.test_derivable((pq_or, qp_or), True, "Test 12 failed: p ∨ q ⟹  q ∨ p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")
    
    assertion_print("\n=== COMPLEX TESTS ===")
    # Test 13: Distributivity: p ∧ (q ∨ r) ⟹  (p ∧ q) ∨ (p ∧ r)
    qr_or = ll.or_formula(q, r)
    qr_and = ll.and_formula(q, r)
    p_and_qr_or = ll.and_formula(p, qr_or)
    p_or_qr_and = ll.or_formula(p, qr_and)
    pq_and = ll.and_formula(p, q)
    pq_or = ll.or_formula(p, q)
    pr_and = ll.and_formula(p, r)
    pr_or = ll.or_formula(p, r)
    pq_or_pr = ll.or_formula(pq_and, pr_and)
    pq_and_pr = ll.and_formula(pq_or, pr_or)
    proof_data += ll.test_derivable((p_and_qr_or, pq_or_pr), False, "Test 13a failed: p ∧ (q ∨ r) ⟹  (p ∧ q) ∨ (p ∧ r)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    proof_data += ll.test_derivable((p_or_qr_and, pq_and_pr), True, "Test 13b failed: p ∨ (q ∧ r) ⟹  (p ∨ q) ∧ (p ∨ r)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 14: Reverse distributivity
    proof_data += ll.test_derivable((pq_or_pr, p_and_qr_or), True, "Test 14a failed: (p ∧ q) ∨ (p ∧ r) ⟹  p ∧ (q ∨ r)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    proof_data += ll.test_derivable((pq_and_pr, p_or_qr_and), False, "Test 14b failed: (p ∨ q) ∧ (p ∨ r) ⟹  p ∨ (q ∧ r)", PERFORM_ASSERTION, PRODUCE_PROOFS)


    # Test 15: Associativity: (p ∧ q) ∧ r ⟹  p ∧ (q ∧ r)
    pq_and_r = ll.and_formula(pq, r)
    qr_and = ll.and_formula(q, r)
    p_and_qr = ll.and_formula(p, qr_and)
    proof_data += ll.test_derivable((pq_and_r, p_and_qr), True, "Test 15 failed: (p ∧ q) ∧ r ⟹  p ∧ (q ∧ r)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 16: Disjunction associativity: (p ∨ q) ∨ r ⟹  p ∨ (q ∨ r)
    pq_or_r = ll.or_formula(pq_or, r)
    p_or_qr = ll.or_formula(p, qr_or)
    proof_data += ll.test_derivable((pq_or_r, p_or_qr), True, "Test 16 failed: (p ∨ q) ∨ r ⟹  p ∨ (q ∨ r)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 17: Absorption: p ∧ (p ∨ q) ⟹  p
    p_and_p_or_q = ll.and_formula(p, pq_or)
    proof_data += ll.test_derivable((p_and_p_or_q, p), True, "Test 17 failed: p ∧ (p ∨ q) ⟹  p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 18: Reverse absorption: p ⟹  p ∧ (p ∨ q)
    proof_data += ll.test_derivable((p, p_and_p_or_q), True, "Test 18 failed: p ⟹  p ∧ (p ∨ q)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 19: More complex formula
    rs_and = ll.and_formula(r, s)
    pq_or_rs = ll.or_formula(pq, rs_and)
    pr_or = ll.or_formula(p, r)
    qs_or = ll.or_formula(q, s)
    pr_and_qs = ll.and_formula(pr_or, qs_or)
    proof_data += ll.test_derivable((pq_or_rs, pr_and_qs), True, "Test 19 failed: (p ∧ q) ∨ (r ∧ s) ⟹  (p ∨ r) ∧ (q ∨ s)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 20: The reverse (should be False)
    proof_data += ll.test_derivable((pr_and_qs, pq_or_rs), False, "Test 20 failed: (p ∨ r) ∧ (q ∨ s) ⟹  (p ∧ q) ∨ (r ∧ s) should be False", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")
    
    generate_latex_output("ll")

    proof_data = ""

def nl_tests():
    global proof_data
    proof_data = ""
    p = nl.atom("p")
    q = nl.atom("q")
    r = nl.atom("r")

    assertion_print("\n=== RUNNING NEW LOGIC TESTS ===")
    
    assertion_print("\n=== BASIC AXIOM TESTS ===")
    # Test 1: Identity
    proof_data += nl.test_derivable((p, p), True, "Test 1: p ⟹  p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 2: Bot elimination
    proof_data += nl.test_derivable((nl.bot(), p), True, "Test 2: ⊥ ⟹  p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 3: Top introduction
    proof_data += nl.test_derivable((p, nl.top()), True, "Test 3: p ⟹  ⊤", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")
    
    assertion_print("\n=== CONJUNCTION TESTS ===")
    pq = nl.and_formula(p, q)
    # Test 4: ∧L1
    proof_data += nl.test_derivable((pq, p), True, "Test 4: p ∧ q ⟹  p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 5: ∧L2
    proof_data += nl.test_derivable((pq, q), True, "Test 5: p ∧ q ⟹  q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 6: ∧R
    proof_data += nl.test_derivable((p, nl.and_formula(p, p)), True, "Test 6: p ⟹  p ∧ p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")
    
    assertion_print("\n=== DISJUNCTION TESTS ===")
    pq_or = nl.or_formula(p, q)
    # Test 7: ∨R1
    proof_data += nl.test_derivable((p, pq_or), True, "Test 7: p ⟹  p ∨ q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 8: ∨R2
    proof_data += nl.test_derivable((q, pq_or), True, "Test 8: q ⟹  p ∨ q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 9: ∨L
    proof_data += nl.test_derivable((pq_or, pq_or), True, "Test 9: p ∨ q ⟹  p ∨ q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")
    
    assertion_print("\n=== IMP TESTS ===")
    # Test 10: ⊃R
    p_imp_p = nl.imp_formula(p, p)
    proof_data += nl.test_derivable((nl.top(), p_imp_p), True, "Test 10: ⊤ ⟹  p ⊃ p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")
    
    assertion_print("\n=== COIMP TESTS ===")
    # Test 11: ⊂L
    p_coimp_q = nl.coimp_formula(p, q)
    proof_data += nl.test_derivable((p_coimp_q, nl.bot()), False, "Test 11: p ⊂ q ⟹  ⊥ (when p ⟹  q is not derivable)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")
    
    assertion_print("\n=== WEAKENING TESTS ===")
    # Test 12: Weakening left
    proof_data += nl.test_derivable((p, nl.top()), True, "Test 12: p ⟹  ⊤ (should work via ⊤ rule)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 13: Weakening right  
    proof_data += nl.test_derivable((nl.bot(), q), True, "Test 13: ⊥ ⟹  q (should work via ⊥ rule)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")

    assertion_print("\n=== ORDER RULE TESTS ===")
    # Test 14: ⊃ order rule - contravariant in first argument, covariant in second
    p_imp_q = nl.imp_formula(p, q)
    q_imp_r = nl.imp_formula(q, r)
    p_imp_r = nl.imp_formula(p, r)
    proof_data += nl.test_derivable((q_imp_r, p_imp_r), False, "Test 14a: q ⊃ r ⟹ p ⊃ r (should fail without p ⟹ q)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 15: ⊂ order rule - covariant in first argument, contravariant in second
    p_coimp_q = nl.coimp_formula(p, q)
    q_coimp_r = nl.coimp_formula(q, r)
    p_coimp_r = nl.coimp_formula(p, r)
    proof_data += nl.test_derivable((p_coimp_r, q_coimp_r), False, "Test 15a: p ⊂ r ⟹ q ⊂ r (should fail without specific conditions)", PERFORM_ASSERTION, PRODUCE_PROOFS)

    assertion_print("Passed!")
    
    assertion_print("\n=== COMPLEX imp TESTS ===")
    # Test 16: ⊃R with identity
    proof_data += nl.test_derivable((nl.top(), p_imp_p), True, "Test 16: ⊤ ⟹ p ⊃ p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 17: ⊃L application
    p_imp_q_and_p = nl.and_formula(p_imp_q, p)
    proof_data += nl.test_derivable((p_imp_q_and_p, q), False, "Test 17: (p ⊃ q) ∧ p ⟹ q (should fail in this logic)", PERFORM_ASSERTION, PRODUCE_PROOFS)

    assertion_print("Passed!")
    
    assertion_print("\n=== COMPLEX coimp TESTS ===")
    # Test 18: ⊂R construction
    proof_data += nl.test_derivable((p, nl.coimp_formula(p, nl.bot())), True, "Test 18: p ⟹ p ⊂ ⊥", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 19: ⊂L elimination with contradiction
    p_coimp_p = nl.coimp_formula(p, p)
    proof_data += nl.test_derivable((p_coimp_p, nl.bot()), True, "Test 19: p ⊂ p ⟹ ⊥", PERFORM_ASSERTION, PRODUCE_PROOFS)

    assertion_print("Passed!")
    
    assertion_print("\n=== INTERACTION TESTS ===")
    # Test 20: imp and conjunction
    p_and_q_imp_p = nl.imp_formula(pq, p)
    proof_data += nl.test_derivable((nl.top(), p_and_q_imp_p), True, "Test 20: ⊤ ⟹ (p ∧ q) ⊃ p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 21: Disjunction and imp
    p_imp_p_or_q = nl.imp_formula(p, pq_or)
    proof_data += nl.test_derivable((nl.top(), p_imp_p_or_q), True, "Test 21: ⊤ ⟹ p ⊃ (p ∨ q)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 22: coimp and disjunction
    p_or_q_coimp_q = nl.coimp_formula(pq_or, q)
    proof_data += nl.test_derivable((p, p_or_q_coimp_q), False, "Test 22: p ⟹ (p ∨ q) ⊂ q (should fail)", PERFORM_ASSERTION, PRODUCE_PROOFS)

    assertion_print("Passed!")
    
    assertion_print("\n=== WEAKENING INTERACTION TESTS ===")
    # Test 23: Weakening with imp
    proof_data += nl.test_derivable((p_imp_q, r), False, "Test 23: p ⊃ q ⟹   r (should fail without additional conditions)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 24: Weakening with coimp
    proof_data += nl.test_derivable((r, p_coimp_q), False, "Test 24: r ⟹  p ⊂ q (should fail without specific conditions)", PERFORM_ASSERTION, PRODUCE_PROOFS)

    assertion_print("Passed!")
    
    assertion_print("\n=== NESTED CONNECTIVE TESTS ===")
    # Test 25: Nested imps
    q_imp_r = nl.imp_formula(q, r)
    p_imp_q_imp_r = nl.imp_formula(p, q_imp_r)
    pq_imp_r = nl.imp_formula(pq, r)
    proof_data += nl.test_derivable((nl.top(), nl.imp_formula(p_imp_q_imp_r, pq_imp_r)), False, "Test 25: ⊤ ⟹ (p ⊃ (q ⊃ r)) ⊃ ((p ∧ q) ⊃ r)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 26: Nested coimps
    q_coimp_r = nl.coimp_formula(q, r)
    p_coimp_q_coimp_r = nl.coimp_formula(p, q_coimp_r)
    proof_data += nl.test_derivable((p_coimp_q_coimp_r, nl.bot()), False, "Test 26: p ⊂ (q ⊂ r) ⟹  ⊥", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 27: Mixed nesting
    p_imp_q_and_r = nl.imp_formula(p, nl.and_formula(q, r))
    p_imp_q_imp_r = nl.imp_formula(p, nl.imp_formula(q, r))
    proof_data += nl.test_derivable((nl.top(), nl.imp_formula(p_imp_q_and_r, p_imp_q_imp_r)), False, "Test 27: ⊤ ⟹ (p ⊃ (q ∧ r)) ⊃ (p ⊃ (q ⊃ r))", PERFORM_ASSERTION, PRODUCE_PROOFS)

    assertion_print("Passed!")
    
    assertion_print("\n=== CONSISTENCY TESTS ===")
    # Test 28: No contradiction from nl.atoms
    proof_data += nl.test_derivable((p, nl.bot()), False, "Test 28: p ⟹  ⊥ (should fail)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 29: Top is not everything
    proof_data += nl.test_derivable((nl.top(), p), False, "Test 29: ⊤ ⟹  p (should fail)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 30: Double negation via subset
    p_coimp_bot = nl.coimp_formula(p, nl.bot())
    p_coimp_bot_coimp_bot = nl.coimp_formula(p_coimp_bot, nl.bot())
    proof_data += nl.test_derivable((p_coimp_bot_coimp_bot, p), False, "Test 30: ((p ⊂ ⊥) ⊂ ⊥) ⟹  p (should fail - no double negation)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")

    # Test 31: (p coimp (r or s)) => ((p or q) coimp (r and s))
    r = nl.atom('r')
    s = nl.atom('s')
    p = nl.atom('p')

    r_or_s = nl.or_formula(r, s)
    p_coimp_r_or_s = nl.coimp_formula(p, r_or_s)
    p_or_q = nl.or_formula(p, q)
    r_and_s = nl.and_formula(r, s)
    p_or_q_coimp_r_and_s = nl.coimp_formula(p_or_q, r_and_s)

    proof_data += nl.test_derivable((p_coimp_r_or_s, p_or_q_coimp_r_and_s), True, "Test 31: (p ⊂ (r ∨ s)) ⟹  ((p ∨ q) ⊂ (r ∧ s)) should be True", PERFORM_ASSERTION, PRODUCE_PROOFS)

    generate_latex_output("nl")

    proof_data = ""

def pql_tests():
    global proof_data
    p = pql.atom("p")
    q = pql.atom("q")
    r = pql.atom("r")
    s = pql.atom("s")

    assertion_print("\n=== RUNNING ORIGINAL TESTS ===")
    
    assertion_print("\n=== ATOM TESTS ===")
    # Test 1: Identity
    proof_data += pql.test_derivable((p, p), True, "Test 1 failed: p ⟹  p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 2: Different atoms
    proof_data += pql.test_derivable((p, q), False, "Test 2 failed: p ⟹  q should be False", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")
    
    assertion_print("\n=== CONJUNCTION TESTS ===")
    # Test 3: Conjunction elimination (∧L1)
    pq = pql.and_formula(p, q)
    proof_data += pql.test_derivable((pq, p), True, "Test 3 failed: p ∧ q ⟹  p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 4: Conjunction elimination (∧L2)
    proof_data += pql.test_derivable((pq, q), True, "Test 4 failed: p ∧ q ⟹  q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 5: Conjunction introduction (∧R)
    proof_data += pql.test_derivable((p, pql.and_formula(p, p)), True, "Test 5 failed: p ⟹  p ∧ p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 6: Invalid conjunction introduction
    proof_data += pql.test_derivable((p, pq), False, "Test 6 failed: p ⟹  p ∧ q should be False", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 7: Conjunction commutativity
    qp = pql.and_formula(q, p)
    proof_data += pql.test_derivable((pq, qp), True, "Test 7 failed: p ∧ q ⟹  q ∧ p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")
    
    assertion_print("\n=== DISJUNCTION TESTS ===")
    pq_or = pql.or_formula(p, q)
    # Test 8: Disjunction introduction (∨R1)
    proof_data += pql.test_derivable((p, pq_or), True, "Test 8 failed: p ⟹  p ∨ q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 9: Disjunction introduction (∨R2)
    proof_data += pql.test_derivable((q, pq_or), True, "Test 9 failed: q ⟹  p ∨ q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 10: Disjunction elimination (∨L) - both cases must lead to conclusion
    proof_data += pql.test_derivable((pq_or, pq_or), True, "Test 10 failed: p ∨ q ⟹  p ∨ q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 11: Invalid disjunction elimination
    proof_data += pql.test_derivable((pq_or, p), False, "Test 11 failed: p ∨ q ⟹  p should be False", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 12: Disjunction commutativity
    qp_or = pql.or_formula(q, p)
    proof_data += pql.test_derivable((pq_or, qp_or), True, "Test 12 failed: p ∨ q ⟹  q ∨ p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")
    
    assertion_print("\n=== COMPLEX TESTS ===")
    # Test 13: Distributivity: p ∧ (q ∨ r) ⟹  (p ∧ q) ∨ (p ∧ r)
    qr_or = pql.or_formula(q, r)
    qr_and = pql.and_formula(q, r)
    p_and_qr_or = pql.and_formula(p, qr_or)
    p_or_qr_and = pql.or_formula(p, qr_and)
    pq_and = pql.and_formula(p, q)
    pq_or = pql.or_formula(p, q)
    pr_and = pql.and_formula(p, r)
    pr_or = pql.or_formula(p, r)
    pq_or_pr = pql.or_formula(pq_and, pr_and)
    pq_and_pr = pql.and_formula(pq_or, pr_or)
    proof_data += pql.test_derivable((p_and_qr_or, pq_or_pr), False, "Test 13a failed: p ∧ (q ∨ r) ⟹  (p ∧ q) ∨ (p ∧ r)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    proof_data += pql.test_derivable((p_or_qr_and, pq_and_pr), True, "Test 13b failed: p ∨ (q ∧ r) ⟹  (p ∨ q) ∧ (p ∨ r)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 14: Reverse distributivity
    proof_data += pql.test_derivable((pq_or_pr, p_and_qr_or), True, "Test 14a failed: (p ∧ q) ∨ (p ∧ r) ⟹  p ∧ (q ∨ r)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    proof_data += pql.test_derivable((pq_and_pr, p_or_qr_and), False, "Test 14b failed: (p ∨ q) ∧ (p ∨ r) ⟹  p ∨ (q ∧ r)", PERFORM_ASSERTION, PRODUCE_PROOFS)


    # Test 15: Associativity: (p ∧ q) ∧ r ⟹  p ∧ (q ∧ r)
    pq_and_r = pql.and_formula(pq, r)
    qr_and = pql.and_formula(q, r)
    p_and_qr = pql.and_formula(p, qr_and)
    proof_data += pql.test_derivable((pq_and_r, p_and_qr), True, "Test 15 failed: (p ∧ q) ∧ r ⟹  p ∧ (q ∧ r)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 16: Disjunction associativity: (p ∨ q) ∨ r ⟹  p ∨ (q ∨ r)
    pq_or_r = pql.or_formula(pq_or, r)
    p_or_qr = pql.or_formula(p, qr_or)
    proof_data += pql.test_derivable((pq_or_r, p_or_qr), True, "Test 16 failed: (p ∨ q) ∨ r ⟹  p ∨ (q ∨ r)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 17: Absorption: p ∧ (p ∨ q) ⟹  p
    p_and_p_or_q = pql.and_formula(p, pq_or)
    proof_data += pql.test_derivable((p_and_p_or_q, p), True, "Test 17 failed: p ∧ (p ∨ q) ⟹  p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 18: Reverse absorption: p ⟹  p ∧ (p ∨ q)
    proof_data += pql.test_derivable((p, p_and_p_or_q), True, "Test 18 failed: p ⟹  p ∧ (p ∨ q)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 19: More complex formula
    rs_and = pql.and_formula(r, s)
    pq_or_rs = pql.or_formula(pq, rs_and)
    pr_or = pql.or_formula(p, r)
    qs_or = pql.or_formula(q, s)
    pr_and_qs = pql.and_formula(pr_or, qs_or)
    proof_data += pql.test_derivable((pq_or_rs, pr_and_qs), True, "Test 19 failed: (p ∧ q) ∨ (r ∧ s) ⟹  (p ∨ r) ∧ (q ∨ s)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 20: The reverse (should be False)
    proof_data += pql.test_derivable((pr_and_qs, pq_or_rs), False, "Test 20 failed: (p ∨ r) ∧ (q ∨ s) ⟹  (p ∧ q) ∨ (r ∧ s) should be False", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")
    assertion_print("\n=== NEGATION TESTS ===")
    # Test 21: Negated atom identity
    not_p = pql.not_formula(p)
    proof_data += pql.test_derivable((not_p, not_p), True, "Test 21 failed: ~p ⟹  ~p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 22: Double negation elimination (~~L)
    not_not_p = pql.not_formula(not_p)
    proof_data += pql.test_derivable((not_not_p, p), True, "Test 22 failed: ~~p ⟹  p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 23: Double negation introduction (~~R)
    proof_data += pql.test_derivable((p, not_not_p), True, "Test 23 failed: p ⟹  ~~p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 24: De Morgan's law: ~(p ∧ q) ⟹  ~p ∨ ~q
    not_pq_and = pql.not_formula(pq)
    not_p_or_not_q = pql.or_formula(not_p, pql.not_formula(q))
    proof_data += pql.test_derivable((not_pq_and, not_p_or_not_q), True, "Test 24 failed: ~(p ∧ q) ⟹  ~p ∨ ~q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 25: De Morgan's law: ~p ∨ ~q ⟹  ~(p ∧ q)
    proof_data += pql.test_derivable((not_p_or_not_q, not_pq_and), True, "Test 25 failed: ~p ∨ ~q ⟹  ~(p ∧ q)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 26: De Morgan's law: ~(p ∨ q) ⟹  ~p ∧ ~q
    not_pq_or = pql.not_formula(pq_or)
    not_p_and_not_q = pql.and_formula(not_p, pql.not_formula(q))
    proof_data += pql.test_derivable((not_pq_or, not_p_and_not_q), True, "Test 26 failed: ~(p ∨ q) ⟹  ~p ∧ ~q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 27: De Morgan's law: ~p ∧ ~q ⟹  ~(p ∨ q)
    proof_data += pql.test_derivable((not_p_and_not_q, not_pq_or), True, "Test 27 failed: ~p ∧ ~q ⟹  ~(p ∨ q)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 28: Triple negation: ~~~p ⟹  ~p
    not_not_not_p = pql.not_formula(not_not_p)
    proof_data += pql.test_derivable((not_not_not_p, not_p), True, "Test 28 failed: ~~~p ⟹  ~p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 29: Contradiction (should fail)
    proof_data += pql.test_derivable((p, not_p), False, "Test 29 failed: p ⟹  ~p should be False", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 30: Contradiction reverse (should fail)
    proof_data += pql.test_derivable((not_p, p), False, "Test 30 failed: ~p ⟹  p should be False", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")
    
    assertion_print("\n=== COMPLEX NEGATION TESTS ===")
    # Test 31: ~(p ∧ ~q) ⟹  ~p ∨ q
    not_q = pql.not_formula(q)
    p_and_not_q = pql.and_formula(p, not_q)
    not_p_and_not_q = pql.not_formula(p_and_not_q)
    not_p_or_q = pql.or_formula(not_p, q)
    proof_data += pql.test_derivable((not_p_and_not_q, not_p_or_q), True, "Test 31 failed: ~(p ∧ ~q) ⟹  ~p ∨ q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 32: ~(~p ∨ q) ⟹  p ∧ ~q
    not_p_or_q_formula = pql.or_formula(not_p, q)
    not_not_p_or_q = pql.not_formula(not_p_or_q_formula)
    p_and_not_q_result = pql.and_formula(p, not_q)
    proof_data += pql.test_derivable((not_not_p_or_q, p_and_not_q_result), True, "Test 32 failed: ~(~p ∨ q) ⟹  p ∧ ~q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 33: Double De Morgan: ~(~p ∧ ~q) ⟹  p ∨ q
    not_not_p_and_not_q = pql.not_formula(not_p_and_not_q)
    proof_data += pql.test_derivable((not_not_p_and_not_q, pq_or), True, "Test 33 failed: ~(~p ∧ ~q) ⟹  p ∨ q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 34: Nested negation: ~(p ∨ ~(q ∧ r)) ⟹  ~p ∧ (q ∧ r)
    qr_and = pql.and_formula(q, r)
    not_qr_and = pql.not_formula(qr_and)
    p_or_not_qr = pql.or_formula(p, not_qr_and)
    not_p_or_not_qr = pql.not_formula(p_or_not_qr)
    not_p_and_qr = pql.and_formula(not_p, qr_and)
    proof_data += pql.test_derivable((not_p_or_not_qr, not_p_and_qr), True, "Test 34 failed: ~(p ∨ ~(q ∧ r)) ⟹  ~p ∧ (q ∧ r)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 35: Complex mixed formula: (p ∧ ~q) ∨ (~p ∧ q) ⟹  ~(p ∧ q) ∨ ~(~p ∧ ~q)
    p_and_not_q = pql.and_formula(p, not_q)
    not_p_and_q = pql.and_formula(not_p, q)
    mixed_or = pql.or_formula(p_and_not_q, not_p_and_q)
    not_pq_and = pql.not_formula(pq)
    not_not_p_and_not_q = pql.not_formula(not_p_and_not_q)
    result_or = pql.or_formula(not_pq_and, not_not_p_and_not_q)
    proof_data += pql.test_derivable((mixed_or, result_or), True, "Test 35 failed: (p ∧ ~q) ∨ (~p ∧ q) ⟹  ~(p ∧ q) ∨ ~(~p ∧ ~q)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")

    generate_latex_output("pql")

    proof_data = ""

def nql_tests():
    global proof_data
    proof_data = ""

    p = nql.atom("p")
    q = nql.atom("q")
    r = nql.atom("r")

    assertion_print("\n=== RUNNING NEW LOGIC TESTS ===")
    
    assertion_print("\n=== BASIC AXIOM TESTS ===")

    # Test failed
    proof_data += nql.test_derivable((p, nql.not_formula(nql.top())), False, "Test 0: p ⟹  ~⊤", PERFORM_ASSERTION, PRODUCE_PROOFS)

    # Test 1: Identity
    proof_data += nql.test_derivable((p, p), True, "Test 1: p ⟹  p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 2: Bot elimination
    proof_data += nql.test_derivable((nql.bot(), p), True, "Test 2: ⊥ ⟹  p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 3: Top introduction
    proof_data += nql.test_derivable((p, nql.top()), True, "Test 3: p ⟹  ⊤", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")
    
    assertion_print("\n=== NEGATION AXIOM TESTS ===")
    # Test 4: Negated atom identity
    not_p = nql.not_formula(p)
    proof_data += nql.test_derivable((not_p, not_p), True, "Test 4: ~p ⟹  ~p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 5: ~⊥ introduction
    proof_data += nql.test_derivable((p, nql.not_formula(nql.bot())), True, "Test 5: p ⟹  ~⊥", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 6: ~⊤ elimination
    proof_data += nql.test_derivable((nql.not_formula(nql.top()), p), True, "Test 6: ~⊤ ⟹  p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")
    
    assertion_print("\n=== DOUBLE NEGATION TESTS ===")
    # Test 7: Double negation elimination (~~L)
    not_not_p = nql.not_formula(not_p)
    proof_data += nql.test_derivable((not_not_p, p), True, "Test 7: ~~p ⟹  p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 8: Double negation introduction (~~R)
    proof_data += nql.test_derivable((p, not_not_p), True, "Test 8: p ⟹  ~~p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")
    
    assertion_print("\n=== NEGATED CONJUNCTION TESTS ===")
    pq = nql.and_formula(p, q)
    not_pq = nql.not_formula(pq)
    not_p_or_not_q = nql.or_formula(not_p, nql.not_formula(q))
    # Test 9: De Morgan's law: ~(p ∧ q) ⟹  ~p ∨ ~q
    proof_data += nql.test_derivable((not_pq, not_p_or_not_q), True, "Test 9: ~(p ∧ q) ⟹  ~p ∨ ~q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 10: De Morgan's law: ~p ∨ ~q ⟹  ~(p ∧ q)
    proof_data += nql.test_derivable((not_p_or_not_q, not_pq), True, "Test 10: ~p ∨ ~q ⟹  ~(p ∧ q)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")
    
    assertion_print("\n=== NEGATED DISJUNCTION TESTS ===")
    pq_or = nql.or_formula(p, q)
    not_pq_or = nql.not_formula(pq_or)
    not_p_and_not_q = nql.and_formula(not_p, nql.not_formula(q))
    # Test 11: De Morgan's law: ~(p ∨ q) ⟹  ~p ∧ ~q
    proof_data += nql.test_derivable((not_pq_or, not_p_and_not_q), True, "Test 11: ~(p ∨ q) ⟹  ~p ∧ ~q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 12: De Morgan's law: ~p ∧ ~q ⟹  ~(p ∨ q)
    proof_data += nql.test_derivable((not_p_and_not_q, not_pq_or), True, "Test 12: ~p ∧ ~q ⟹  ~(p ∨ q)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")
    
    assertion_print("\n=== NEGATED IMPLICATION TESTS ===")
    p_imp_q = nql.imp_formula(p, q)
    not_p_imp_q = nql.not_formula(p_imp_q)
    # Test 13: ~⊃L1: from p ⟹  δ derive ~(p ⊃ q) ⟹  δ
    proof_data += nql.test_derivable((not_p_imp_q, p), True, "Test 13: ~(p ⊃ q) ⟹  p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 14: ~⊃L2: from ~q ⟹  δ derive ~(p ⊃ q) ⟹  δ
    proof_data += nql.test_derivable((not_p_imp_q, nql.not_formula(q)), True, "Test 14: ~(p ⊃ q) ⟹  ~q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 15: ~⊃R: from γ ⟹  p and γ ⟹  ~q derive γ ⟹  ~(p ⊃ q)
    proof_data += nql.test_derivable((nql.and_formula(p, nql.not_formula(q)), not_p_imp_q), True, "Test 15: p ∧ ~q ⟹  ~(p ⊃ q)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")
    
    assertion_print("\n=== NEGATED SUBSET TESTS ===")
    p_coimp_q = nql.coimp_formula(p, q)
    not_p_coimp_q = nql.not_formula(p_coimp_q)
    # Test 16: ~⊂L: from ~p ⟹  β and q ⟹  β derive ~(p ⊂ q) ⟹  β
    proof_data += nql.test_derivable((not_p_coimp_q, nql.or_formula(not_p, q)), True, "Test 16: ~(p ⊂ q) ⟹  ~p ∨ q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 17: ~⊂R1: from α ⟹  ~p derive α ⟹  ~(p ⊂ q)
    proof_data += nql.test_derivable((not_p, not_p_coimp_q), True, "Test 17: ~p ⟹  ~(p ⊂ q)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 18: ~⊂R2: from α ⟹  q derive α ⟹  ~(p ⊂ q)
    proof_data += nql.test_derivable((q, not_p_coimp_q), True, "Test 18: q ⟹  ~(p ⊂ q)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")
    
    assertion_print("\n=== NEGATED WEAKENING TESTS ===")
    # Test 19: ~we_L: if ~⊥ ⟹  α then β ⟹  α
    proof_data += nql.test_derivable((p, nql.top()), True, "Test 19: p ⟹  ⊤ (weakening test)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    # Test 20: ~we_R: if α ⟹  ~⊤ then α ⟹  β
    proof_data += nql.test_derivable((nql.not_formula(nql.top()), q), True, "Test 20: ~⊤ ⟹  q (weakening test)", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")
    
    assertion_print("\n=== COMPLEX NEGATION TESTS ===")
    # Test 21: Triple negation: ~~~p ⟹  ~p
    not_not_not_p = nql.not_formula(not_not_p)
    proof_data += nql.test_derivable((not_not_not_p, not_p), True, "Test 21: ~~~p ⟹  ~p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 22: ~(p ∧ ~q) ⟹  ~p ∨ q
    not_q = nql.not_formula(q)
    p_and_not_q = nql.and_formula(p, not_q)
    not_p_and_not_q = nql.not_formula(p_and_not_q)
    not_p_or_q = nql.or_formula(not_p, q)
    proof_data += nql.test_derivable((not_p_and_not_q, not_p_or_q), True, "Test 22: ~(p ∧ ~q) ⟹  ~p ∨ q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 23: ~(~p ∨ q) ⟹  p ∧ ~q
    not_p_or_q_formula = nql.or_formula(not_p, q)
    not_not_p_or_q = nql.not_formula(not_p_or_q_formula)
    p_and_not_q_result = nql.and_formula(p, not_q)
    proof_data += nql.test_derivable((not_not_p_or_q, p_and_not_q_result), True, "Test 23: ~(~p ∨ q) ⟹  p ∧ ~q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Test 24: Double De Morgan: ~(~p ∧ ~q) ⟹  p ∨ q
    not_not_p_and_not_q = nql.not_formula(not_p_and_not_q)
    proof_data += nql.test_derivable((not_not_p_and_not_q, pq_or), True, "Test 24: ~(~p ∧ ~q) ⟹  p ∨ q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")


    assertion_print("\n=== ORIGINAL TESTS (should still work) ===")
    # Original conjunction tests
    proof_data += nql.test_derivable((pq, p), True, "Original Test: p ∧ q ⟹  p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    proof_data += nql.test_derivable((pq, q), True, "Original Test: p ∧ q ⟹  q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    proof_data += nql.test_derivable((p, nql.and_formula(p, p)), True, "Original Test: p ⟹  p ∧ p", PERFORM_ASSERTION, PRODUCE_PROOFS)
    
    # Original disjunction tests
    proof_data += nql.test_derivable((p, pq_or), True, "Original Test: p ⟹  p ∨ q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    proof_data += nql.test_derivable((q, pq_or), True, "Original Test: q ⟹  p ∨ q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    proof_data += nql.test_derivable((pq_or, pq_or), True, "Original Test: p ∨ q ⟹  p ∨ q", PERFORM_ASSERTION, PRODUCE_PROOFS)
    assertion_print("Passed!")

    generate_latex_output("nql")

    proof_data = ""

# Test cases
if __name__ == "__main__":
    ll_tests()
    pql_tests()
    nl_tests()
    nql_tests()

