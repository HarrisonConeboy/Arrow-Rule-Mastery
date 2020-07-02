class Node:
    def __init__(self, parents, node, children):
        self.node = node

        if isinstance(parents, set):
            self.parents = parents
        else:
            self.parents = set()
            self.parents.add(parents)

        if isinstance(children, set):
            self.children = children
        else:
            self.children = set()
            self.children.add(children)

    def __str__(self):
        return f'{self.parents} -> {self.node} -> {self.children}'

    def add_parent(self, parent):
        self.parents.add(parent)

    def add_child(self, child):
        self.children.add(child)

    def literals(self):
        output = set()
        output.add(self.node)
        for child in self.children:
            output.add(child)
        for parent in self.parents:
            output.add(parent)
        return output


# Method for NOT operation on literals
def not_literal(literal):
    if literal[0] == '!':
        return literal[1:]
    else:
        return f'!{literal}'


# Method for producing a contra-positive on implications
def contra_positive(implication):
    temp_one = not_literal(implication[1])
    temp_two = not_literal(implication[0])
    output = (temp_one, temp_two)
    return output


# Method for creating nodes given a list of implications
def create_nodes(implication_list):
    nodes = {}
    for imp in implication_list:
        # Normal
        if imp[0] not in nodes.keys():
            nodes[imp[0]] = Node(set(), imp[0], imp[1])
        else:
            nodes[imp[0]].add_child(imp[1])
        if imp[1] not in nodes.keys():
            nodes[imp[1]] = Node(imp[0], imp[1], set())
        else:
            nodes[imp[1]].add_parent(imp[0])

        # Contra-positive
        contra = contra_positive(imp)
        if contra[0] not in nodes.keys():
            nodes[contra[0]] = Node(set(), contra[0], contra[1])
        else:
            nodes[contra[0]].add_child(contra[1])
        if contra[1] not in nodes.keys():
            nodes[contra[1]] = Node(contra[0], contra[1], set())
        else:
            nodes[contra[1]].add_parent(contra[0])

    return nodes


# Method for grouping nodes
def join_nodes(nodes_set):
    output = []
    while len(nodes_set) != 0:
        temp_tree = set()
        nodes_added = set()
        nodes_to_check = set()

        temp_node = nodes_set.popitem()[1]
        temp_tree.add(temp_node)
        nodes_added.add(temp_node.node)
        for child in temp_node.children:
            nodes_to_check.add(child)
        for parent in temp_node.parents:
            nodes_to_check.add(parent)

        while len(nodes_to_check) != 0:
            temp_node = nodes_to_check.pop()
            for child in nodes_set[temp_node].children:
                if not (child in nodes_added):
                    nodes_to_check.add(child)

            for parent in nodes_set[temp_node].parents:
                if not (parent in nodes_added):
                    nodes_to_check.add(parent)

            nodes_added.add(temp_node)
            temp_tree.add(nodes_set.pop(temp_node))

        output.append(temp_tree)

    return output


def combine_tree_pairs(tree_list):
    temp_tree = tree_list.pop(0)
    nodes_in_each = [set()]
    for node in temp_tree:
        nodes_in_each[0] = nodes_in_each[0].union(node.literals())
    output = [[temp_tree]]

    for tree in range(len(tree_list)):
        to_add = True
        temp_tree = tree_list[tree]
        copy = temp_tree.copy()
        temp_node = copy.pop()
        literal = not_literal(temp_node.node)
        for nodes in range(len(nodes_in_each)):
            if literal in nodes_in_each[nodes]:
                output[nodes].append(temp_tree)
                to_add = False
                for node in temp_tree:
                    nodes_in_each[nodes] = nodes_in_each[nodes].union(node.literals())
                break
            elif not_literal(literal) in nodes_in_each[nodes]:
                to_add = False
                break
        if to_add:
            output.append([temp_tree])
            temp_set = set()
            for node in temp_tree:
                temp_set = temp_set.union(node.literals())
            nodes_in_each.append(temp_set)
    return output


def produce_valid_trees(tree_list, output=[]):
    if len(output) == 0:
        for w in tree_list.pop(0):
            w = frozenset(w)
            temp_set = set()
            temp_set.add(w)
            output.append(w)
    if len(tree_list) == 0:
        return output
    else:
        new_output = []
        for w in tree_list.pop(0):
            w = frozenset(w)
            set_w = set()
            set_w.add(w)
            for out in output:
                temp_set = out | w
                new_output.append(temp_set)
        return produce_valid_trees(tree_list, new_output)


def produce_truth_table(literals_set):
    length_down = 2 ** len(literals_set) + 1
    length_across = len(literals_set)
    top_labels = []
    for literal in literals_set:
        top_labels.append(literal)
    top_labels.sort()

    truth_table = [[0 for x in range(length_across)] for y in range(length_down)]
    truth_table[0] = top_labels

    for lit_num in range(0, length_across):
        num = 1
        counter = 0
        change_over = (2 ** (lit_num + 1)) - 1
        for change in range(change_over + 1):
            for number_down in range(2 ** (length_across - lit_num - 1)):
                truth_table[number_down + change*(2 ** (length_across - lit_num - 1)) + 1][lit_num] = num
            counter += 1
            if num == 1:
                num = 0
            else:
                num = 1

    return truth_table


def alter_table(truth_table, implication_list):
    temp = [[] for y in range(len(truth_table[1:]))]
    for imp in implication_list:
        pred_negated = False
        cons_negated = False
        if len(imp[0]) > 1:
            pred_negated = True
            pred = truth_table[0].index(not_literal(imp[0]))
        else:
            pred = truth_table[0].index(imp[0])
        if len(imp[1]) > 1:
            cons_negated = True
            cons = truth_table[0].index(not_literal(imp[1]))
        else:
            cons = truth_table[0].index(imp[1])
        for i,row in enumerate(truth_table[1:]):
            if pred_negated and cons_negated:
                if row[pred] == 1:
                    temp[i].append(True)
                elif row[cons] == 1:
                    temp[i].append(False)
                else:
                    temp[i].append(True)
            elif pred_negated:
                if row[pred] == 1:
                    temp[i].append(True)
                elif row[cons] == 0:
                    temp[i].append(False)
                else:
                    temp[i].append(True)
            elif cons_negated:
                if row[pred] == 0:
                    temp[i].append(True)
                elif row[cons] == 1:
                    temp[i].append(False)
                else:
                    temp[i].append(True)
            else:
                if row[pred] == 0:
                    temp[i].append(True)
                elif row[cons] == 0:
                    temp[i].append(False)
                else:
                    temp[i].append(True)
    output = []
    for row in temp:
        out = True
        for bool in row:
            out = out and bool
        output.append(out)
    for i,row in enumerate(truth_table[1:]):
        truth_table[i + 1].append(output[i])
    return truth_table


def create_complete_truth_table(implication_list):
    literals = set()
    for imp in implication_list:
        if len(imp[0]) > 1:
            literals.add(not_literal(imp[0]))
        else:
            literals.add(imp[0])
        if len(imp[1]) > 1:
            literals.add(not_literal(imp[1]))
        else:
            literals.add(imp[1])
    return alter_table(produce_truth_table(literals), implication_list)


def main():
    set_one = [('A', 'B'), ('B', 'C'), ('C', 'D'), ('!A', 'D')]
    print(len(join_nodes(create_nodes(set_one))))
    # print('What would you like to do?')
    # user_input = None
    # while user_input != 'end':
    #
    #     user_input = input('Produce Disjoint Trees (DT)? Produce Valid Combinations (VC)? Produce Truth Table (TT)?\n')
    #     set_one = [('A', 'B'), ('B', 'C'), ('!D', '!C'), ('!A', 'B'), ('H', 'G')]
    #
    #     if user_input == 'DT':
    #         out = join_nodes(create_nodes(set_one))
    #         for node in out:
    #             print('DISJOINT TREE')
    #             for n in node:
    #                 print(n)
    #             print('====================')
    #
    #     elif user_input == 'VC':
    #         out = produce_valid_trees(combine_tree_pairs(join_nodes(create_nodes(set_one))))
    #         for valid_combination in out:
    #             print('VALID COMBINATION OF NODES')
    #             for tree in valid_combination:
    #                 print(tree)
    #             print('====================')
    #
    #     elif user_input == 'TT':
    #         for row in create_complete_truth_table(set_one):
    #             print(row)
    #     elif user_input == 'end':
    #         print('Ending')
    #     else:
    #         print('Invalid answer')


if __name__ == '__main__':
    main()
