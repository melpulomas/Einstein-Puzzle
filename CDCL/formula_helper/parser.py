"""
Parse the input formula in dimacs format
"""


class Parser:

    def parse_dimacs(input_file):
        formula = []
        with open(input_file) as file:
            for line in file:
                if line.startswith('c'):
                    continue
                if line.startswith('p'):
                    num_literals = int(line.split()[2])
                    continue
                # convert to integer clause
                clause = [int(x) for x in line[:-2].split()]
                formula.append(clause)
            file.close()
        return formula, num_literals
