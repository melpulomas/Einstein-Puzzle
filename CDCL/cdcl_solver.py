"""
This implementation is based on the Handbook of Satisfiability - Chapter 4 CDCL Solvers
"""
import random
import sys
import time
from collections import defaultdict
from heapq import heapify, heappop, heappush, heapreplace
from formula_helper import solution_checker, unsat_prover


class CDCLSolver:
    def __init__(self, formula, num_literals, heuristic, generate_proof, eliminate_pure_literal, random_restart):
        self.heuristic_dict = {'random': self.random_selection, 'order': self.ordered_selection,
                               'twoclause': self.two_clause_selection, 'vsids': self.vsids_selection}
        self.formula = formula
        self.num_literals = num_literals
        self.heuristic = heuristic
        self.selection = self.heuristic_dict[heuristic]

        self.assigned_lits = set()

        # ignore index 0
        self.value = [0] * (num_literals + 1)  # assigned value of the literal. 1 or -1. default 0.
        self.antecedent = [-1] * (num_literals + 1)  # the clause_id that implies this literal. default -1.
        self.decision_level = [-1] * (num_literals + 1)  # the decision level of the implied literal. default -1.

        # statistics
        self.pick_branching_count = 0

        # one UID implementation
        self.assignment_history = {}  # format = decision_level: [assignment_sequence]
        self.sorted_original_formula_set = set()
        self.sorted_new_clause_set = set()

        # pure literal elimination
        self.eliminate_pure_literal = eliminate_pure_literal
        self.pure_literal_count = 0

        # two-clause heuristic
        self.two_clause_dict = defaultdict(int)

        # vsids heuristic
        self.vsids_activity = defaultdict(int)
        self.prev_chosen_literal = 0

        # tracing
        self.generate_proof = generate_proof
        self.kappa_conflict_clause = None
        self.clauseid_to_parents = {}

        # restart and forget
        self.random_restart = random_restart
        self.new_clause_limit = int(len(self.formula) / 5)
        self.random_restart_count = 0

    def assign_value(self, lit, lit_antecedent, decision_lvl):
        """
        Assign value to the literal.
        Update value, antecedent and decision_level
        """
        index = abs(lit)
        self.value[index] = int(lit / index)
        self.antecedent[index] = lit_antecedent
        self.decision_level[index] = decision_lvl
        self.assigned_lits.add(index)

    def check_clause_status(self, clause):
        """
        Check the clause if it is (1) satisfied, (2) conflict or (3) unit clause.
        :return SAT, UNSAT or undetermined:
        """
        unit_lit = 0
        num_unassigned = 0
        num_false_lit = 0
        for lit in clause:
            # lit is true, clause is satisfied
            if lit < 0 and self.value[abs(lit)] == -1 or lit > 0 and self.value[abs(lit)] == 1:
                return 'SAT'
            # lit is false:
            elif lit < 0 and self.value[abs(lit)] == 1 or lit > 0 and self.value[abs(lit)] == -1:
                num_false_lit += 1
            # lit not assigned
            elif self.value[abs(lit)] == 0:
                unit_lit = lit
                num_unassigned += 1
        # UNSAT clause - conflict
        if len(clause) == num_false_lit:
            return 'UNSAT'
        # unit clause
        elif num_unassigned == 1:
            return unit_lit
        return 'undetermined'

    def unit_propagation(self, decision_lvl):
        """
        Recursively checks for unit clauses and assign that literal value.
        Must go through every clause in the formula to ensure no conflict.
        If an unsatisfied clause is identified, then a conflict indication is returned.
        unit - the conflict lit
        index - id of the clause that is supposed to be assigned but fail
        :return conflict_clause_id (UNSAT) / -111 (SAT)
        """

        def find_unit_clauses():
            """
            Loop through the formula to find unit clauses.
            :return unit_clauses, unit_antecedent, unit_clause_set:
            """
            unit_clauses = []
            unit_antecedent = []
            unit_clause_set = set()
            for index, clause in enumerate(self.formula):
                feedback = self.check_clause_status(clause)
                # if feedback is a unit clause
                if isinstance(feedback, int) and feedback not in unit_clause_set:
                    unit_clauses.append(feedback)
                    unit_antecedent.append(index)
                    unit_clause_set.add(feedback)
            return unit_clauses, unit_antecedent, unit_clause_set

        unit_clauses, unit_antecedents, unit_clause_set = find_unit_clauses()
        while unit_clauses:
            unit = unit_clauses.pop()
            unit_antecedent = unit_antecedents.pop()
            unit_clause_set.remove(unit)
            self.assign_value(unit, unit_antecedent, decision_lvl)
            self.assignment_history[decision_lvl].extend([unit])

            # check for UNSAT after assigning the above unit clause
            for index, clause in enumerate(self.formula):
                feedback = self.check_clause_status(clause)
                if feedback == 'SAT' or feedback == 'undetermined':
                    continue
                # found a new unit clause
                elif isinstance(feedback, int) and feedback not in unit_clause_set:
                    unit_clauses.append(feedback)
                    unit_antecedents.append(index)
                    unit_clause_set.add(feedback)
                # found a conflict clause
                elif feedback == 'UNSAT':
                    # record this conflict clause for tracing
                    if self.generate_proof:
                        self.kappa_conflict_clause = index
                    return index
        return -111

    def pure_literal_elimination(self):
        """
        Check and assign every pure literal.
        Pure literal definition: p is pure if ~p does not appear anywhere on the formula_helper.
        """
        literal_set = set()
        for clause in self.formula:
            for lit in clause:
                literal_set.add(lit)

        pure_literal_set = set()
        for clause in self.formula:
            for lit in clause:
                if -lit not in literal_set:
                    pure_literal_set.add(lit)

        # update formula by assigning values to pure literals.
        # -999 is a permanent dummy value. -999 decision level will never be backtracked to.
        for lit in pure_literal_set:
            self.assign_value(lit, -1, -999)

        self.pure_literal_count = len(pure_literal_set)

    def all_variables_assigned(self):
        """
        Check if all variables are assigned
        """
        # print("Number of unassigned variables: " + str(len(self.assigned_lits))
        if len(self.assigned_lits) == self.num_literals:
            return True
        return False

    def conflict_analysis(self, conflict_clause_id, conflict_decision_lvl):
        """
        Analyse the most recent conflict and learn a new clause from the conflict.
        """

        def find_one_uip_cut(conflict_clause):
            """
            Find the one-uip-cut of the propagation graph.
            Makes use of the assignment_history and keeps propagating backwards until the one-uip.
            :return learnt_clause, parents:
            """

            def find_latest_assignment():
                """
                Find the latest assigned (unit propagated) lit in the conflict_decision_lvl
                """
                assignment_sequence = reversed(self.assignment_history[conflict_decision_lvl])
                for lit in assignment_sequence:
                    if self.antecedent[abs(lit)] != -1 and (lit in learnt_clause or -lit in learnt_clause):
                        return lit

            def resolve(clause_one, clause_two):
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

            # tracing
            parents = [self.kappa_conflict_clause]

            learnt_clause = set(conflict_clause)
            prev_learnt_clause = set()

            # keep recursing backwards until one uip is reached
            while learnt_clause != prev_learnt_clause:
                num_current_lvl_lits = 0
                for lit in learnt_clause:
                    if self.decision_level[abs(lit)] == conflict_decision_lvl:
                        num_current_lvl_lits += 1

                latest_assigned_lit = find_latest_assignment()

                # found the uip
                if not latest_assigned_lit:
                    break
                # no more clause to resolve
                elif num_current_lvl_lits == 1 and conflict_decision_lvl != 0:
                    break
                else:
                    prev_learnt_clause = learnt_clause
                    learnt_clause = resolve(learnt_clause, self.formula[self.antecedent[abs(latest_assigned_lit)]])

                    # tracing
                    if (self.generate_proof):
                        parents.append(self.antecedent[abs(latest_assigned_lit)])

            return learnt_clause, parents

        conflict_clause = self.formula[conflict_clause_id]
        new_clause, parents = find_one_uip_cut(conflict_clause)

        # unsat
        if not new_clause:
            # append the empty clause [0] to the formula
            if self.generate_proof:
                self.formula.append([0])
                self.clauseid_to_parents[len(self.formula) - 1] = parents
            return -1

        # learn and add new_clause to formula
        sorted_new_clause = frozenset(sorted(new_clause))
        if new_clause and sorted_new_clause not in self.sorted_original_formula_set.union(self.sorted_new_clause_set):
            self.formula.append(list(new_clause))
            self.sorted_new_clause_set.add(sorted_new_clause)

            if self.generate_proof:
                self.clauseid_to_parents[len(self.formula) - 1] = parents

            if self.heuristic == "twoclause" and len(new_clause) == 2:
                self.update_two_clause(new_clause)  # two-clause update

            for lit in new_clause:
                self.vsids_activity[lit] += 1  # vsids - additive bump
                self.vsids_multiplicative_boost(lit)  # vsids - multiplicative boost

        backtrack_lvl = 0
        if new_clause:
            # backtrack to the highest decision level before the current conflict_decision_lvl
            # default backtrack to 0
            for lit in new_clause:
                if self.decision_level[abs(lit)] < conflict_decision_lvl:
                    backtrack_lvl = max(self.decision_level[abs(lit)], backtrack_lvl)
        return backtrack_lvl

    def backtrack(self, backtrack_decision_level):
        """
        Remove previously assigned values down to and excluding backtrack_decision_level.
        :param backtrack_decision_level:
        """
        for lit in range(1, self.num_literals + 1):
            if self.decision_level[lit] > backtrack_decision_level:
                self.value[lit] = 0
                self.decision_level[lit] = -1
                self.antecedent[lit] = -1
                self.assigned_lits.remove(lit)
        levels = list(self.assignment_history.keys())
        for lvl in levels:
            if lvl > backtrack_decision_level:
                del self.assignment_history[lvl]
        self.kappa_conflict_clause = None

    def cdcl(self):
        """
        Main solver: loop unit propagation and backtracking until SAT or UNSAT.
        :return True (SAT) or False (UNSAT):
        """
        current_dec_lvl = 0
        self.assignment_history[current_dec_lvl] = []

        if self.eliminate_pure_literal:
            self.pure_literal_elimination()

        while not self.all_variables_assigned():
            # Restart and Forget
            if self.random_restart:
                num_new_clauses = len(self.sorted_new_clause_set)
                if num_new_clauses > self.new_clause_limit:
                    self.restart_and_forget()
                    current_dec_lvl = 0
                    self.random_restart_count += 1

            # always unit propagate first
            conflict_clause_id = self.unit_propagation(current_dec_lvl)

            if conflict_clause_id >= 0:
                backtrack_decision_level = self.conflict_analysis(conflict_clause_id, current_dec_lvl)

                if backtrack_decision_level < 0:
                    return False

                self.backtrack(backtrack_decision_level)
                current_dec_lvl = backtrack_decision_level
            elif self.all_variables_assigned():
                break
            else:
                current_dec_lvl += 1
                picked_variable = self.selection()
                self.prev_chosen_literal = picked_variable
                self.pick_branching_count += 1
                self.assignment_history[current_dec_lvl] = [picked_variable]
                self.assign_value(picked_variable, -1, current_dec_lvl)
                self.vsids_activity[picked_variable] += 1  # vsids - additive bump
                self.vsids_multiplicative_boost(picked_variable)  # vsids - multiplicative boost

        return True

    def solve(self, input_file, output_file):
        """
        First, it will run the cdcl to see if there a satisfiable solution
        If satisfiable: it will run the SolutionChecker to check if the solution is valid
        Elseif unsatisfiable (and if proof activated): it will call the UnsatProver to generate an unsat proof
        """
        print("START - Running Time")
        start_time = time.time()  # start time

        # pre-processing
        for clause in self.formula:
            sorted_clause = sorted(clause)
            self.sorted_original_formula_set.add(frozenset(sorted_clause))

        if self.heuristic == "twoclause":
            self.pre_process_two_clause()
        elif self.heuristic == "vsids":
            self.pre_process_vsids()

        satisfiable = self.cdcl()
        time_taken = time.time() - start_time  # stop time
        print("END - Running Time")

        print("\nSatisfiable: " + str(satisfiable))
        print("Total time taken (seconds): " + str(time_taken))

        if satisfiable:
            print("=== checking solution ===")
            # record the solution
            solution = [(lit * value) for lit, value in enumerate(self.value)][1:]
            final_solution = 'SATISFIABLE ' + ' '.join([str(lit) for lit in solution]) + ' 0'

            sol_file = output_file.replace(".cnf", "_sol.txt")
            with open(sol_file, 'w') as sol:
                sol.write(final_solution)
                sol.close()

            valid_solution = solution_checker.SolutionChecker(input_file, sol_file).main()

            if not valid_solution:
                sys.exit("=== BUGGY - not valid solution ===")
        else:
            if self.generate_proof:
                unsat_prover.UnsatProver(self.formula, self.clauseid_to_parents).main(output_file)

        print("=== writing statistics to file ===")
        stats_file = output_file.replace(".cnf", "_stats.txt")
        with open(stats_file, 'w') as stats:
            stats.write(str(input_file) + "\n")
            stats.write(self.heuristic)
            stats.write("\n\n")
            stats.write("Total number of clauses: " + str(len(self.formula)) + "\n")
            stats.write("Total number of new clauses: " + str(len(self.sorted_new_clause_set)) + "\n")
            stats.write("Number of pure literals: " + str(self.pure_literal_count) + "\n")
            stats.write("Number of picked branching: " + str(self.pick_branching_count) + "\n")
            stats.write("Number of random restarts: " + str(self.random_restart_count) + "\n")
            stats.write("Total time taken (seconds): " + str(time_taken) + "\n")
            stats.write("\nAssignment History\n")
            for index, assignment in self.assignment_history.items():
                stats.write(str(index) + " : ")
                stats.write(' '.join([str(lit) for lit in assignment]))
                stats.write("\n")
            stats.close()

        print("=== THE END - successful run ===")

    ### Methods for selection heuristics ###
    def ordered_selection(self):
        """
        Select a literal in ascending order of literals index
        """
        for lit in range(1, self.num_literals + 1):
            if self.value[lit] == 0:
                return random.choice([lit, -lit])

    def random_selection(self):
        """
        Select a literal randomly
        """
        unassigned_lits = []
        for lit in range(1, self.num_literals + 1):
            if self.value[lit] == 0:
                unassigned_lits.append(lit)
        choice = random.choice(unassigned_lits)
        return random.choice([choice, -choice])

    def pre_process_two_clause(self):
        """
        Count and store the two_clause_dict
        """
        two_clause_count = defaultdict(int)
        for clause in self.formula:
            if len(clause) == 2:
                for lit in clause:
                    two_clause_count[abs(lit)] += 1
        for lit, count in enumerate(two_clause_count):
            self.two_clause_dict[abs(lit)] = count

    def update_two_clause(self, two_clause):
        """
        Update the two_clause_dict
        """
        for lit in two_clause:
            self.two_clause_dict[abs(lit)] += 1

    def two_clause_selection(self):
        """
        Select a literal based on two-clause heuristic
        """
        # sort by decreasing count
        two_clause_list_sorted = [k for k, v in sorted(self.two_clause_dict.items(), key=lambda item: item[1])]
        for lit in two_clause_list_sorted:
            if self.value[lit] == 0:
                return random.choice([lit, -lit])
        # no more unassigned two-clause lit
        return self.random_selection()

    def pre_process_vsids(self):
        """
        Preprocess for visds by initialising all the literals in a clause += 1
        """
        for clause in self.formula:
            for lit in clause:
                self.vsids_activity[lit] += 1

    def vsids_multiplicative_boost(self, lit):
        """
        Multiplicative boost for vsids.
        Decay all the literals' activity by a random decay_constant.
        TA suggestion: to make this O(1) instead of O(num_literals). Only the relative value matters.
        We will do multiplicative boost instead.
        """
        decay_constant = random.uniform(0.000001, 1)  # (0,1)
        boost_constant = 1 + decay_constant
        self.vsids_activity[lit] *= boost_constant
        # # original decay method
        # self.vsids_activity.update(
        #     (lit, activity * decay_constant) for lit, activity in self.vsids_activity.items())

    def vsids_selection(self):
        """
        Select a literal based on vsids.
        TA suggestion: use a max heap O(n) vs O(nlogn) where n is the num_unassigned_lit
        """
        max_heap = []
        for lit in range(1, self.num_literals + 1):
            if self.value[lit] == 0:
                # use negative to implement max heap
                max_heap.append((-self.vsids_activity[lit], lit))
                max_heap.append((-self.vsids_activity[-lit], -lit))
        heapify(max_heap)
        while max_heap:
            choice = heappop(max_heap)[1]
            if self.prev_chosen_literal != choice:
                return choice
        return self.random_selection()

    ### Methods for selection heuristics ###

    def restart_and_forget(self):
        """
        If c clauses are learned, then they are sorted with respect to an activity score.
        The c/2 clauses with lowest score are thrown away, c is increased by a constant
        and a Restart is performed
        """
        # increase c by a constant
        self.new_clause_limit *= 1.5

        max_heap = []
        num_new_clause = len(self.sorted_new_clause_set)
        num_new_clause_to_keep = int(num_new_clause / 2)  # keep only the top c/2 most active clause
        new_clause_activity = defaultdict(float)

        start_index_new_clause = len(self.sorted_original_formula_set)
        for clause in self.formula[start_index_new_clause:]:
            sorted_new_clause = frozenset(sorted(clause))
            new_clause_activity[sorted_new_clause] = sum([self.vsids_activity[lit] for lit in clause]) / len(
                clause)

        for clause, activity_level in new_clause_activity.items():  # cost = O(c + c/2logc/2)
            if len(max_heap) < num_new_clause_to_keep:
                heappush(max_heap, (-activity_level, clause))
            else:
                max_item = max_heap[0]
                if activity_level < -max_item[0]:
                    heapreplace(max_heap, (-activity_level, clause))
        # cost = O(c/2)
        to_be_removed_clauses = set([frozenset(sorted(clause)) for neg_activity_level, clause in max_heap])
        # cost = O(c)
        new_formula = [clause for clause in self.formula if frozenset(sorted(clause)) not in to_be_removed_clauses]
        self.formula = new_formula
        new_set = self.sorted_new_clause_set.difference(to_be_removed_clauses)
        self.sorted_new_clause_set = new_set

        # backtrack to level 0
        self.backtrack(0)

        del new_formula
        del new_set
