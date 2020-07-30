import sys

from formula_helper import parser
import cdcl_solver

if __name__ == '__main__':
    # user specifications
    # supported heuristic: | random | order | twoclause | vsids |
    input_file = "..\\CNF\\uuf150-01.cnf"
    heuristic = "vsids"
    generate_proof = False  # toggle this for stage 2

    # default setting for best performance
    eliminate_pure_literal = False
    random_restart = False
    if random_restart and generate_proof:
        sys.exit("Solver does not support random restart for unsat proof yet...")

    output_file = input_file.replace("CNF", "OUTPUT")

    formula, num_literals = parser.Parser.parse_dimacs(input_file)
    solver = cdcl_solver.CDCLSolver(formula, num_literals, heuristic, generate_proof, eliminate_pure_literal,
                                    random_restart)
    solver.solve(input_file, output_file)
