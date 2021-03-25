# Look for #IMPLEMENT tags in this file. These tags indicate what has
# to be implemented to complete the warehouse domain.

"""
Construct and return Tenner Grid CSP models.
"""

from cspbase import *
import itertools


def tenner_csp_model_1(initial_tenner_board):
    """Return a CSP object representing a Tenner Grid CSP problem along
       with an array of variables for the problem. That is return

       tenner_csp, variable_array

       where tenner_csp is a csp representing tenner grid using model_1
       and variable_array is a list of lists

       [ [  ]
         [  ]
         .
         .
         .
         [  ] ]

       such that variable_array[i][j] is the Variable (object) that
       you built to represent the value to be placed in cell i,j of
       the Tenner Grid (only including the first n rows, indexed from
       (0,0) to (n,9)) where n can be 3 to 7.


       The input board is specified as a pair (n_grid, last_row).
       The first element in the pair is a list of n length-10 lists.
       Each of the n lists represents a row of the grid.
       If a -1 is in the list it represents an empty cell.
       Otherwise if a number between 0--9 is in the list then this represents a
       pre-set board position. E.g., the board

       ---------------------
       |6| |1|5|7| | | |3| |
       | |9|7| | |2|1| | | |
       | | | | | |0| | | |1|
       | |9| |0|7| |3|5|4| |
       |6| | |5| |0| | | | |
       ---------------------
       would be represented by the list of lists

       [[6, -1, 1, 5, 7, -1, -1, -1, 3, -1],
        [-1, 9, 7, -1, -1, 2, 1, -1, -1, -1],
        [-1, -1, -1, -1, -1, 0, -1, -1, -1, 1],
        [-1, 9, -1, 0, 7, -1, 3, 5, 4, -1],
        [6, -1, -1, 5, -1, 0, -1, -1, -1,-1]]


       This routine returns model_1 which consists of a variable for
       each cell of the board, with domain equal to {0-9} if the board
       has a 0 at that position, and domain equal {i} if the board has
       a fixed number i at that cell.

       model_1 contains BINARY CONSTRAINTS OF NOT-EQUAL between
       all relevant variables (e.g., all pairs of variables in the
       same row, etc.).
       model_1 also constains n-nary constraints of sum constraints for each
       column.
    """
    n_grid, last_row = initial_tenner_board[0], initial_tenner_board[1]
    n = len(n_grid)
    domain = [num for num in range(10)]

    csp = CSP("tenner_csp")

    var_array = []
    for i in range(n):
        vars_i = []
        for j in range(10):
            cell = n_grid[i][j]
            name = str(i) + str(j)
            if cell != -1:
                var = Variable(name, [cell])
            else:
                var = Variable(name, domain)
            vars_i.append(var)
            csp.add_var(var)
        var_array.append(vars_i)

    # binary non-equal constraints
    for row in var_array:
        for i in range(10):
            var1 = row[i]
            for var2 in row[i + 1:]:
                name = str(var_array.index(row)) + " - " + str(i) + \
                       str(row.index(var2))
                scope = [var1, var2]
                cons = Constraint(name, scope)
                tuples = []
                for val1 in var1.cur_domain():
                    for val2 in var2.cur_domain():
                        if val1 != val2:
                            tuples.append((val1, val2))
                cons.add_satisfying_tuples(tuples)
                csp.add_constraint(cons)

    # binary contiguous constraints
    for i in range(9):
        for j in range(n):
            if j < n - 1:  # rows 0 to n-2
                var = var_array[j][i]
                var_right = var_array[j][i + 1]
                var_down = var_array[j + 1][i]
                var_diag = var_array[j + 1][i + 1]
                cons_right = Constraint("right", [var, var_right])
                cons_down = Constraint("down", [var, var_down])
                cons_diag = Constraint("diagonal", [var, var_diag])
                all_tuples = []
                for var2 in [var_right, var_down, var_diag]:
                    tuples = []
                    for val1 in var.cur_domain():
                        for val2 in var2.cur_domain():
                            if val1 != val2:
                                tuples.append((val1, val2))
                    all_tuples.append(tuples)
                cons_right.add_satisfying_tuples(all_tuples[0])
                cons_down.add_satisfying_tuples(all_tuples[1])
                cons_diag.add_satisfying_tuples(all_tuples[2])
                for cons in [cons_right, cons_down, cons_diag]:
                    csp.add_constraint(cons)

            else:  # row n-1 (last row)
                var = var_array[j][i]
                var_right = var_array[j][i + 1]
                cons_right = Constraint("right", [var, var_right])
                tuples = []
                for val1 in var.cur_domain():
                    for val2 in var_right.cur_domain():
                        if val1 != val2:
                            tuples.append((val1, val2))
                cons_right.add_satisfying_tuples(tuples)
                csp.add_constraint(cons_right)

    # n-nary sum constraints
    for i in range(10):
        target = last_row[i]
        name = str(i) + ": " + str(target)
        scope = []
        domains = []
        for j in range(n):
            var = var_array[j][i]
            scope.append(var)
            domains.append(var.cur_domain())
        cons = Constraint(name, scope)
        tuples = []
        pad_num = (8 - len(domains)) * [[0]]
        domains.extend(pad_num)  # pad curr_domain to 8 (maximum n = 8)
        for tuple in list(itertools.product(domains[0], domains[1], domains[2],
                                            domains[3], domains[4], domains[5],
                                            domains[6], domains[7])):
            if sum(tuple) == target:
                tuples.append(tuple[:n])
        cons.add_satisfying_tuples(tuples)
        csp.add_constraint(cons)

    return csp, var_array


##############################

def tenner_csp_model_2(initial_tenner_board):
    """Return a CSP object representing a Tenner Grid CSP problem along
       with an array of variables for the problem. That is return

       tenner_csp, variable_array

       where tenner_csp is a csp representing tenner using model_1
       and variable_array is a list of lists

       [ [  ]
         [  ]
         .
         .
         .
         [  ] ]

       such that variable_array[i][j] is the Variable (object) that
       you built to represent the value to be placed in cell i,j of
       the Tenner Grid (only including the first n rows, indexed from
       (0,0) to (n,9)) where n can be 3 to 7.

       The input board takes the same input format (a list of n length-10 lists
       specifying the board as tenner_csp_model_1.

       The variables of model_2 are the same as for model_1: a variable
       for each cell of the board, with domain equal to {0-9} if the
       board has a -1 at that position, and domain equal {i} if the board
       has a fixed number i at that cell.

       However, model_2 has different constraints. In particular, instead
       of binary non-equals constraints model_2 has a combination of n-nary
       all-different constraints: all-different constraints for the variables in
       each row, and sum constraints for each column. You may use binary
       constraints to encode contiguous cells (including diagonally contiguous
       cells), however. Each -ary constraint is over more
       than two variables (some of these variables will have
       a single value in their domain). model_2 should create these
       all-different constraints between the relevant variables.
    """
    n_grid, last_row = initial_tenner_board[0], initial_tenner_board[1]
    n = len(n_grid)
    domain = [num for num in range(10)]

    csp = CSP("tenner_csp")

    var_array = []
    for i in range(n):
        vars_i = []
        for j in range(10):
            cell = n_grid[i][j]
            name = str(i) + str(j)
            if cell != -1:
                var = Variable(name, [cell])
            else:
                var = Variable(name, domain)
            vars_i.append(var)
            csp.add_var(var)
        var_array.append(vars_i)

    # n-nary non-equal constraints
    for i in range(n):
        scope = []
        set_values = {}  # dictionary of index, value pairs
        for j in range(10):
            value = n_grid[i][j]
            scope.append(var_array[i][j])
            if value != -1:  # value is pre-set
                set_values[j] = value
        cons = Constraint("row" + str(n), scope)
        tuples = []
        for tuple in list(itertools.permutations(range(10))):
            sarisfied = True
            for index in set_values:
                if tuple[index] != set_values[index]:
                    sarisfied = False
                    break
            if sarisfied:
                tuples.append(tuple)
        cons.add_satisfying_tuples(tuples)
        csp.add_constraint(cons)

    # binary contiguous constraints
    for i in range(9):
        for j in range(n):
            if j < n - 1:  # rows 0 to n-2
                var = var_array[j][i]
                var_right = var_array[j][i + 1]
                var_down = var_array[j + 1][i]
                var_diag = var_array[j + 1][i + 1]
                cons_right = Constraint("right", [var, var_right])
                cons_down = Constraint("down", [var, var_down])
                cons_diag = Constraint("diagonal", [var, var_diag])
                all_tuples = []
                for var2 in [var_right, var_down, var_diag]:
                    tuples = []
                    for val1 in var.cur_domain():
                        for val2 in var2.cur_domain():
                            if val1 != val2:
                                tuples.append((val1, val2))
                    all_tuples.append(tuples)
                cons_right.add_satisfying_tuples(all_tuples[0])
                cons_down.add_satisfying_tuples(all_tuples[1])
                cons_diag.add_satisfying_tuples(all_tuples[2])
                for cons in [cons_right, cons_down, cons_diag]:
                    csp.add_constraint(cons)

            else:  # row n-1 (last row)
                var = var_array[j][i]
                var_right = var_array[j][i + 1]
                cons_right = Constraint("right", [var, var_right])
                tuples = []
                for val1 in var.cur_domain():
                    for val2 in var_right.cur_domain():
                        if val1 != val2:
                            tuples.append((val1, val2))
                cons_right.add_satisfying_tuples(tuples)
                csp.add_constraint(cons_right)

    # n-nary sum constraints
    for i in range(10):
        target = last_row[i]
        name = str(i) + ": " + str(target)
        scope = []
        domains = []
        for j in range(n):
            var = var_array[j][i]
            scope.append(var)
            domains.append(var.cur_domain())
        cons = Constraint(name, scope)
        tuples = []
        pad_num = (8 - len(domains)) * [[0]]
        domains.extend(pad_num)  # pad curr_domain to 8 (maximum n = 8)
        for tuple in list(itertools.product(domains[0], domains[1], domains[2],
                                            domains[3], domains[4], domains[5],
                                            domains[6], domains[7])):
            if sum(tuple) == target:
                tuples.append(tuple[:n])
        cons.add_satisfying_tuples(tuples)
        csp.add_constraint(cons)

    return csp, var_array
