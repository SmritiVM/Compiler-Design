#PREDICTIVE PARSING

#STEP 0
#General representation of Grammar
grammar = open("Grammar.txt")

V = set()
T =  set()
P_LHS = []
P_RHS = []
S = grammar.read(1)
grammar.seek(0)

for production in grammar:
    lhs, rhs = production.split()

    #adding the production
    P_LHS.append(lhs)
    P_RHS.append(rhs)

    #adding the variables
    V.add(lhs)

    #adding terminals
    for char in rhs:
        T.add(char)
T = T - V

def print_productions(P_LHS, P_RHS):
    for i in range(len(P_LHS)):
        print(P_LHS[i] , '-->', P_RHS[i])
        
print("GRAMMAR")
print("V: ", V)
print("T: ", T)
print_productions(P_LHS, P_RHS)
print("S: ", S)


#STEP 1
#Removing left recursion
new_state = 90
def add_new_production(new_P_LHS, new_P_RHS, lhs, rhs):
    global new_state
    non_terminal = chr(new_state)
    new_state -= 1
    rule = rhs[1:] + non_terminal
    
    new_P_LHS.append(non_terminal)
    new_P_RHS.append(rule)
    new_P_LHS.append(non_terminal)
    new_P_RHS.append('epsilon')

    return non_terminal

def modify_productions(P_LHS, P_RHS, lhs, new_P_LHS, new_P_RHS, non_terminal):
    alt_pdtn_present = 0
    for i in range(len(P_LHS)):
        if P_LHS[i] == lhs and P_RHS[i][0] != lhs:
            alt_pdtn_present = 1
            new_P_LHS.append(lhs)
            new_P_RHS.append(P_RHS[i] + non_terminal)

    if not alt_pdtn_present:
        new_P_LHS.append(lhs)
        new_P_RHS.append(non_terminal)
            
def remove_left_recursion(P_LHS, P_RHS):
    n = len(P_LHS)
    new_P_LHS = []
    new_P_RHS = []
    left_recursive_nts = []
    for i in range(n):
        lhs = P_LHS[i]
        rhs = P_RHS[i]
        if rhs[0] == lhs:
            left_recursive_nts.append(lhs)
            new_non_terminal = add_new_production(new_P_LHS, new_P_RHS, lhs, rhs)
            modify_productions(P_LHS, P_RHS, lhs, new_P_LHS, new_P_RHS, new_non_terminal)

        if lhs not in left_recursive_nts:
            new_P_LHS.append(P_LHS[i])
            new_P_RHS.append(P_RHS[i])

    return new_P_LHS, new_P_RHS

P_LHS, P_RHS = remove_left_recursion(P_LHS, P_RHS)
print("\nGrammar after removing left recursion: ")
print_productions(P_LHS, P_RHS)

#Modifying Variables list
V = V.union(set(P_LHS))


#STEP 2
#Removing left factoring
def longest_common_prefix(strs):
    prefix = ""
    if not strs:
        return prefix
            
    for index in range(len(strs[0])):
        for s in strs[1:]:
            if index == len(s) or s[index] != strs[0][index]:
                return prefix
            
        prefix += strs[0][index]
        
    return prefix

def generate_pdtn_dictionary(P_LHS, P_RHS):
    productions = {}
    for i in range(len(P_LHS)):
        lhs = P_LHS[i]
        rhs = P_RHS[i]
        if lhs not in productions:
            productions[lhs] = [rhs]
        else:
            productions[lhs].append(rhs)
    return productions


def remove_left_factoring(P_LHS, P_RHS):
    global new_state
    productions = generate_pdtn_dictionary(P_LHS, P_RHS)
    
    for variable in productions.copy():
        rules = productions[variable]
        if len(rules) == 1:
            continue
        lcs = longest_common_prefix(rules)
        length_lcs = len(lcs)
        if length_lcs < 1:
            continue
        new_rules = []
        for rule in rules:
            rhs = rule[length_lcs:]
            if len(rhs) == 0:
                rhs = 'epsilon'
            new_rules.append(rhs)

        non_terminal = chr(new_state)
        productions.update({variable : [lcs + non_terminal]})
        productions[non_terminal] = new_rules

        new_state -= 1
    
    return productions
    
    

productions = remove_left_factoring(P_LHS, P_RHS)
V = V.union(set(productions.keys()))

def print_productions(productions):
    for variable in productions:
        for rule in productions[variable]:
            print(variable, '-->', rule)

print("\nGrammar after removing left factoring: ")
print_productions(productions)


#STEP 3.1
#Computing first
def find_first(variable, productions, first, wait):
    if variable not in first:
        first[variable] = []
    for rule in productions[variable]:
        if rule == 'epsilon':
            next_symbol = 'epsilon'
        else:
            next_symbol = rule[0]
        if next_symbol in T or next_symbol == 'epsilon':
            first[variable].append(next_symbol)
            

        else:
            if next_symbol in first:
                first[variable].extend(first[next_symbol])

            else:
                wait.append(variable)
    return wait

def empty_waitlist(wait, productions, first):
    while wait:
        variable = wait.pop()
        wait = find_first(variable, productions, first, wait)
        

def compute_firsts(productions):
    wait = []
    first = {}
    for variable in productions:
        find_first(variable, productions, first, wait)
    empty_waitlist(wait, productions, first)

    print("\nFirsts: ")
    for variable in first:
        print(variable, first[variable])

    return first

first = compute_firsts(productions)

#STEP 3.2
##Computing follow
def get_key(val, my_dict):
    for key, value in my_dict.items():
        if val == value:
            return key

def find_follow_for_epsilon(variable, productions, rules, follow, wait):
    parent = get_key(rules, productions)
    if parent in follow:
        follow[variable] = follow[variable].union(follow[parent])
        
    else:
        wait.append(variable)
    return follow, wait
        
def find_follow(variable, productions, follow, wait, first):
    if variable not in follow:
        follow[variable] = set()
    if variable == S:
        follow[variable].add('$')

    P_RHS = productions.values()
    
    for rules in P_RHS:
        for rule in rules:
            index = rule.find(variable)
            if index == -1:
                continue
        
            if index == len(rule) - 1:
                follow, wait = find_follow_for_epsilon(variable, productions, rules, follow, wait)

            elif rule[index + 1] in T:
                follow[variable].add(rule[index + 1])

            elif rule[index + 1] in V:
                next_symbol = rule[index + 1]
                parent_first = first[next_symbol]
                if 'epsilon' in parent_first:
                    follow, wait = find_follow_for_epsilon(variable, productions, rules, follow, wait)
                for symbol in parent_first:
                    if symbol != 'epsilon':
                        follow[variable].add(symbol)
                
    
    return wait

def empty_waitlist(wait, productions, follow, first):
    while wait:
        variable = wait.pop()
        print(variable, "wait")
        wait = find_follow(variable, productions, follow, wait, first)

def compute_follows(productions, first):
    follow = {}
    wait = []
    for variable in productions:
        find_follow(variable, productions, follow, wait, first)
    empty_waitlist(wait, productions, follow, first)

    print("\nFollows: ")
    for variable in follow:
        print(variable, follow[variable])
    
    return follow

follow = compute_follows(productions, first)
            

#STEP 4 & 5
#Parsing table
#Constructing table
T.add('$')
row_count = len(V)
column_count = len(T)
table = [['blank' for i in range(column_count + 1)] for _ in range(row_count + 1)]

V = sorted(V)
T = sorted(T)
table[0][0] = ' '
table[0][1:] = list(T)


for i in range(1, row_count + 1):
    table[i][0] = V[i - 1]


def print_table(table):
    print("\n\nParsing table\n")
    print('_' * 112)
    for row in table:
        for entry in row:
            print(f'|{entry:15}', end = '')
        print(f'|')
        print('_' * 112)
    
#print_table(table)

def add_production(row, symbol, T, variable, rule, table):
    column = T.index(symbol)
    if table[row + 1][column + 1] != 'blank':
        return False
    table[row + 1][column + 1] = variable + '-->' + rule
    return True

def fill_table(table, V, T, productions, first, follow):
    for variable in productions:
        row = V.index(variable)
        for rule in productions[variable]:
            if rule == 'epsilon':
                next_symbol = 'epsilon'
            else:
                next_symbol = rule[0]

            if next_symbol == 'epsilon':
                symbols = follow[variable]
                for symbol in symbols:
                    check = add_production(row, symbol, T, variable, rule, table)
                    if not check:
                        return False

            elif next_symbol in V:
                symbols = first[next_symbol]
                for symbol in symbols:
                    check = add_production(row, symbol, T, variable, rule, table)
                    if not check:
                        return False
            
            else:
                check = add_production(row, next_symbol, T,variable, rule, table)
                if not check:
                    return False
    
    return True, table

fill, table = fill_table(table, V, T, productions, first, follow)
if fill:
    print_table(table)
else:
    print("Not LL Grammar")


#STEP 6
#Parsing and acceptance
test_input = input("Enter string to be tested: ")
stack = ['$', S]
ip_buffer = list(test_input) + ['$']

print('\nSTACK\tBUFFER\tACTION')

while stack[-1] != '$':
    print(''.join(stack), ''.join(ip_buffer), sep = '\t', end = '\t')
    top = stack.pop()
    front = ip_buffer[0]
    
    action_flag = 1

    if top in T:
        if top != front:
            print("Input Rejected")
            exit()
        else:
            ip_buffer.pop(0)

        if top == front:
            print("Remove",top)
            action_flag = 0
        

    
    else:
        row = V.index(top)
        column = T.index(front)
        state = table[row + 1][column + 1]
        if state == 'blank':
            print("\nInput Rejected")
            exit()
        
        if action_flag:
            print(state)

        production = state.split('>')[1]
        if production == 'epsilon':
            continue
        symbols = list(production)
        stack.extend(symbols[::-1])

print("\nInput Accepted")
