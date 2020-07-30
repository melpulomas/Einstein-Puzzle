"""
unsat prover for the input CNF
"""


class UnsatProver:
    def __init__(self, formula, clauseid_to_parents):
        self.formula = formula
        self.clauseid_to_parents = clauseid_to_parents
        self.given_formula_size = None

    def main(self, output_file):
        self.given_formula_size = len(self.formula)
        needed_clauses = self.find_all_needed_clauses()
        self.expand_to_two_parents(needed_clauses)
        new_formula, new_clauseid_to_parents = self.renumber_clause(needed_clauses)
        self.write_proof(output_file, new_formula, new_clauseid_to_parents)

    def expand_to_two_parents(self, needed_clauses):
        """
        Expand out the resolutions from n-parents to 2-parents
        """
        for current_id in needed_clauses:
            # skip if this is an original clause
            if not self.clauseid_to_parents.get(current_id):
                continue

            # get the parents
            parents = self.clauseid_to_parents.get(current_id)

            # at least 3 parents
            if len(parents) > 2:
                # keep the last_parent to resolve back to this clause at the end
                last_id = parents.pop()

                new_clause = None
                prev_index = -1

                for index in parents:
                    if new_clause is None:
                        prev_index = index
                        new_clause = self.formula[index]
                        continue

                    # resolve and add this to the end of the formula
                    new_clause = self.resolve(new_clause, self.formula[index])
                    self.formula.append(new_clause)
                    self.clauseid_to_parents[len(self.formula) - 1] = [prev_index, index]

                    prev_index = len(self.formula) - 1

                # add back to this clause
                self.clauseid_to_parents[current_id] = [prev_index, last_id]

            else:
                pass

    def write_proof(self, output_file, new_formula, new_clauseid_to_parents):
        """
        Write the proof to an output file
        """
        print("=== writing proof to file ===")
        # proof_file = output_file.replace(".cnf", "_indexed_proof.txt")
        # with open(proof_file, 'w') as proof:
        #     proof.write("v " + str(len(new_formula)) + "\n")
        #     proof.write("\nList of Clauses\n")
        #     for index, clause in enumerate(new_formula):
        #         proof.write(str(index + 1) + " : ")
        #         proof.write(' '.join([str(elem) for elem in clause]))
        #         proof.write("\n")
        #     proof.write("\nResolution Proof\n")
        #     for clausedid, parent in new_clauseid_to_parents.items():
        #         proof.write(' '.join([str(elem) for elem in parent]))
        #         proof.write(" : ")
        #         proof.write(str(clausedid))
        #         proof.write("\n")
        #     proof.close()

        proof_file = output_file.replace(".cnf", "_proof.txt")
        with open(proof_file, 'w') as proof:
            proof.write("v " + str(len(new_formula)) + "\n")
            for index, clause in enumerate(new_formula):
                proof.write(' '.join([str(elem) for elem in clause]))
                proof.write("\n")
            for clausedid, parent in new_clauseid_to_parents.items():
                proof.write(' '.join([str(elem) for elem in parent]))
                proof.write(" ")
                proof.write(str(clausedid))
                proof.write("\n")
            proof.close()

    def renumber_clause(self, needed_clauses):
        """
        Remove clauses not needed in resolution, add clauses from 2-parents expansion
        Renumber the clauses to newid
        """
        needed_set = set(needed_clauses)
        map_oldid_newid = {}  # this will map from id in the old_formula to id in the new_formula
        new_needed_set = set()  # this will include all the needed clauses from 2-parents
        new_formula = []
        new_clauseid_to_parents = {}

        for index, clause in enumerate(self.formula):
            # take note of the special empty clause
            if clause == [0]:
                continue
            # exclude clauses not needed in resolution
            # learnt clauses need to be included
            if index not in needed_set and index < self.given_formula_size:
                continue

            new_formula.append(clause)
            new_needed_set.add(index)
            map_oldid_newid[index] = len(new_formula)

        # create the new clauseid_to_parents with updated id
        for id, parents in self.clauseid_to_parents.items():
            if id in new_needed_set:
                new_clauseid_to_parents[map_oldid_newid[id]] = sorted([map_oldid_newid[p] for p in parents])

        # add the special empty clause (-1)
        new_clauseid_to_parents[-1] = sorted([map_oldid_newid[p] for p in self.clauseid_to_parents[
            self.given_formula_size - 1]])

        return new_formula, new_clauseid_to_parents

    def resolve(self, clause_one, clause_two):
        """
        Return the resolution of the two input clauses
        """
        new_clause = set(clause_one)
        for lit in clause_two:
            if -lit in new_clause:
                new_clause.remove(-lit)
            else:
                new_clause.add(lit)
        return list(new_clause)

    def find_all_needed_clauses(self):
        """
        Perform BFS from the empty clause and find all clauses that led to it
        """
        last_empty_clauseid = len(self.formula) - 1
        visited_clauseid = set()
        visited_clauseid.add(last_empty_clauseid)

        queue = []
        queue.extend(self.clauseid_to_parents.get(last_empty_clauseid))

        while queue:
            current_clauseid = queue.pop(0)

            if current_clauseid in visited_clauseid:
                continue
            visited_clauseid.add(current_clauseid)

            current_parents = self.clauseid_to_parents.get(current_clauseid)
            if not current_parents:
                continue

            queue.extend([p for p in current_parents if p not in visited_clauseid])

        return sorted(visited_clauseid)
