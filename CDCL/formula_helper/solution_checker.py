"""
solution checker for input CNF and its solution.txt
"""


class SolutionChecker:
    def __init__(self, formula, solution):
        self.formula = formula
        self.solution = solution

    def parse_solution(self, filename):
        with open(filename) as file:
            solution = file.read()
            if solution.split()[0] == 'SATISFIABLE':
                return map(int, solution.split()[1:-1])
            else:
                return []

    def parse_formula(self, filename):
        clauses = []
        for line in open(filename):
            if line.startswith('c'):
                continue
            if line.startswith('p'):
                continue
            clause = [int(x) for x in line[:-2].split()]
            clauses.append(clause)
        return clauses

    def check_solution(self, formula, solution):
        solution = set(solution)
        for clause in formula:
            # check if this clause literals and its assignments are disjoint
            # if disjoint, this clause cannot be satisfied with the given assignments
            if set(clause).isdisjoint(solution):
                print('Not valid Solution')
                return False
        print('Valid Solution')
        return True

    def main(self):
        solution = self.parse_solution(self.solution)
        if solution:
            formula = self.parse_formula(self.formula)
            return self.check_solution(formula, solution)
        else:
            print('Not able to validate UNSATISFIABLE solution')
            return False


if __name__ == '__main__':
    formula_file = "..\\..\\CNF\\uf200-01.cnf"
    solution_file = "..\\..\\OUTPUT\\uf200-01_sol.txt"
    SolutionChecker(formula_file, solution_file).main()
