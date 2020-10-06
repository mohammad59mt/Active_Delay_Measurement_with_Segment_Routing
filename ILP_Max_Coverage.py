import numpy as np, datetime
from pulp import *
import pulp

class monitoring:
    """F: Number of flows,  N: Number of nodes, L: Maximum length of monitoring routes
        x: x monitoring flows will cross each link, src: Sources of each flow,  dst: Destination of each flow
        A: Link adjacency matrix (0, 1),   B: Capacity matrix,  mu: Monitoring traffic ratio to total traffic
        R: Routing Matrix  ---> BLP Variable"""
    def __init__(self, in_topo=None, active_optional_constraint=False,min_num_monitoring_flows=None, number_of_monitoring_flows=None):
        self.L = 6  # Maximum length of monitoring routes
        self.x = 1  # x monitoring flows will cross each link
        self.mu = 0.01  # max ratio of monitoring traffic to link capacity
        self.__convert_topo_to_desigred_format(in_topo) # N, number_of_hosts, A, map_switch_to_MAC, possible_sources, map_sourceSwitch_to_host
        self.B = 10000000 * self.A  # links are considered to be 10Mb
        self.E = int(sum(sum(self.A))) # number of links
        ''' flows adjustment'''
        # if min_num_monitoring_flows is not defined, choose the number of links as min number of monitoring flows (n-equation, n-unknown)
        self.min_num_monitoring_flows = min_num_monitoring_flows if min_num_monitoring_flows is not None else self.number_of_links_between_switches*self.x

        num_monitoring_nodes = len(self.possible_sources)
        # self.F =  num_monitoring_nodes * (num_monitoring_nodes) # Number of Flows: From any source to any destination including nod_i --> nod_i
        # self.src = []
        # for f in range(num_monitoring_nodes):
        #     for f_prime in range(num_monitoring_nodes):
        #         self.src.append(self.possible_sources[f])
        # self.dst = []
        # for f in range(num_monitoring_nodes):
        #     for f_prime in range(num_monitoring_nodes):
        #         self.dst.append(self.possible_sources[f_prime])

        # self.F = num_monitoring_nodes * self.E
        # self.src = [self.possible_sources[i] for i in range(num_monitoring_nodes) for j in range(self.E)]
        # self.dst = [self.possible_sources[i] for i in range(num_monitoring_nodes) for j in range(self.E)]

        # import math
        # self.F = num_monitoring_nodes * math.ceil(self.E/num_monitoring_nodes)
        # self.src = [self.possible_sources[i] for i in range(num_monitoring_nodes) for j in range(math.ceil(self.E/num_monitoring_nodes))]
        # self.dst = [self.possible_sources[i] for i in range(num_monitoring_nodes) for j in range(math.ceil(self.E/num_monitoring_nodes))]

        import math
        if number_of_monitoring_flows is None: number_of_monitoring_flows = num_monitoring_nodes * math.ceil(self.E/num_monitoring_nodes)
        self.F = self.E
        self.src = [self.possible_sources[i] for i in range(num_monitoring_nodes) for j in range(math.ceil(number_of_monitoring_flows/num_monitoring_nodes))][:self.E]
        self.dst = [self.possible_sources[i] for i in range(num_monitoring_nodes) for j in range(math.ceil(number_of_monitoring_flows/num_monitoring_nodes))][:self.E]

        self.flow_rate = 80  # monitoring flows are considered to be 80bps
        self.__forwarding_table_entries = None
        self.monitoring_lp_problem = None
        self.routing_matrix = [[[0 for f in range(self.F)] for j in range(self.N)] for i in range(self.N)]
        self.big_number = 51*(self.N*self.N)-150*self.N+100
        self.active_optional_constraint = active_optional_constraint
    def __convert_topo_to_desigred_format(self, topo):
        """ """
        if topo is None: topo = {('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:01', 's'): 0, ('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:02', 's'): 1, ('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:03', 's'): 1, ('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:01', 's'): 1, ('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:02', 's'): 0, ('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:03', 's'): 1, ('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:01', 's'): 1, ('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:02', 's'): 1, ('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:03', 's'): 0, ('7a:1b:c3:65:e5:4a', '00:00:00:00:00:00:00:02', 'h'): 1, ('96:47:ee:7d:c4:3e', '00:00:00:00:00:00:00:01', 'h'): 1, ('ce:74:73:a5:e7:53', '00:00:00:00:00:00:00:03', 'h'): 1}
        '''Find the set of switches and hosts'''
        set_of_switchs, set_of_hosts = set(), set()
        def is_MAC(input):
            if len(input.split(':')) == 8: return True
            else: return False
        for element in topo:
            # each "element" is either (MAC, MAC, 's') OR (IP, MAC, 'h')
            for i in range(0,2):
                if is_MAC(element[i]): set_of_switchs.add(element[i])
                else: set_of_hosts.add(element[i])
        ''' Set parameters --> N: number of nodes (switches),  H: number of hosts, A: adjacency matrix'''
        number_of_links_between_switches = 0
        A = np.zeros((len(set_of_switchs), len(set_of_switchs)))
        # A = [[0 for j in range(len(set_of_switchs))] for i in range(len(set_of_switchs))]
        map_MAC_to_switch = {}
        tN, number_of_hosts = 0, 0  # tN: number of different IPs viewed till now
        possible_sources = set()  # s: set of switches with possibility to be a source (connected to a host)
        map_sourceSwitch_to_host = {}
        for element in topo:
            value = topo[element]
            ''' if both nodes are switch'''
            if element[2] == 's':
                # each "element" is either (MAC, MAC, 's') OR (IP, MAC, 'h')
                for i in range(0, 2):
                    if element[i] not in map_MAC_to_switch:
                        map_MAC_to_switch[element[i]] = tN
                        tN += 1
                if int(value) == 1:
                    # A[map_MAC_to_switch[element[0]], map_MAC_to_switch[element[1]]] = 1
                    A[map_MAC_to_switch[element[0]]][map_MAC_to_switch[element[1]]] = 1
                    number_of_links_between_switches += 1
            # ''' if one node is a switch and another one is a host '''
            elif element[2] == 'h':
                number_of_hosts += 1
                switch = element[1] if is_MAC(element[1]) else element[0]
                host = element[0] if is_MAC(element[1]) else element[1]
                ''' if the connected switch doesn't have a mapping number (from IP to switch number) then assign one'''
                if switch not in map_MAC_to_switch:
                    map_MAC_to_switch[switch] = tN
                    tN += 1
                ''' add the switch number to set of possible sources'''
                possible_sources.add(map_MAC_to_switch[switch])
                ''' map the host to to a source switch'''
                if switch in map_sourceSwitch_to_host:
                    map_sourceSwitch_to_host[switch].append(host)
                else:
                    map_sourceSwitch_to_host[switch] = [host]
        map_switch_to_MAC = {}
        for element in map_MAC_to_switch:
            map_switch_to_MAC[map_MAC_to_switch[element]] = element

        self.number_of_links_between_switches = number_of_links_between_switches
        self.N, self.number_of_hosts, self.A, self.map_switch_to_MAC, self.possible_sources, self.map_sourceSwitch_to_host = \
            tN, number_of_hosts, A, map_switch_to_MAC, list(possible_sources), map_sourceSwitch_to_host
    def __routing_matrix(self):
        """"""
        ''' to simplify the writing'''
        F, N, src, dst, solved_problem = self.F, self.N, self.src, self.dst, self.monitoring_lp_problem
        def index_extractor(input):
            """ remove waste characters """
            input = input.replace('(', '').replace(',', '').replace(')', '')
            return int(str(input).split('_')[1]), int(str(input).split('_')[2]), int(str(input).split('_')[3])
        ''' create route-matrix'''
        routing_matrix = [[[0 for f in range(F)] for j in range(N)] for i in range(N)]
        for variable in solved_problem.variables():
            if int(variable.varValue) != 0:
                if 'R_(' in variable.name:
                    x, y, z = index_extractor(variable.name)
                    routing_matrix[x][y][z] = int(variable.varValue)
                    self.routing_matrix[x][y][z] = max(routing_matrix[x][y][z], self.routing_matrix[x][y][z])
        return routing_matrix
    def stepAware_routing_matrix(self):
        """"""
        ''' to simplify the writing'''
        F, N, src, dst, solved_problem = self.F, self.N, self.src, self.dst, self.monitoring_lp_problem
        def index_extractor(input):
            """ remove waste characters """
            input = input.replace('(', '').replace(',', '').replace(')', '')
            return int(str(input).split('_')[1]), int(str(input).split('_')[2]), int(str(input).split('_')[3])
        ''' create route-matrix'''
        stepped_routing_matrix = [[[0 for f in range(F)] for j in range(N)] for i in range(N)]
        for variable in solved_problem.variables():
            if int(variable.varValue) != 0:
                if 'P_(' in variable.name:
                    x, y, z = index_extractor(variable.name)
                    stepped_routing_matrix[x][y][z] = int(variable.varValue)
        '''purging redundant flows'''
        for f in range(F-1, -1 , -1):
            ''' removing flows doesn't leave the source switch'''
            if sum([stepped_routing_matrix[i][j][f] for i in range(N) for j in range(N)])==0:
                for i in range(N):
                    for j in range(N):
                        del stepped_routing_matrix[i][j][f]
        return stepped_routing_matrix
    # def tmp_routing_matrix(self):
    #     """"""
    #     ''' to simplify the writing'''
    #     F, N, src, dst, solved_problem = self.F, self.N, self.src, self.dst, self.monitoring_lp_problem
    #     def index_extractor(input):
    #         """ remove waste characters """
    #         input = input.replace('(', '').replace(',', '').replace(')', '')
    #         return int(str(input).split('_')[1]), int(str(input).split('_')[2]), int(str(input).split('_')[3])
    #     ''' create route-matrix'''
    #     routing_matrix = [[[0 for f in range(F)] for j in range(N)] for i in range(N)]
    #     for variable in solved_problem.variables():
    #         if int(variable.varValue) != 0:
    #             if 'R_(' in variable.name:
    #                 x, y, z = index_extractor(variable.name)
    #                 routing_matrix[x][y][z] = int(variable.varValue)
    #     '''purging redundant flows'''
    #     for f in range(F-1, -1 , -1):
    #         ''' removing flows doesn't leave the source switch'''
    #         if sum([routing_matrix[i][j][f] for i in range(N) for j in range(N)])==0:
    #             for i in range(N):
    #                 for j in range(N):
    #                     del routing_matrix[i][j][f]
    #     return routing_matrix
    def __convert_to_routing_rule_entries(self):
        """"""
        ''' to simplify the writing'''
        F, N, src, dst, solved_problem, map_sourceSwitch_to_host, map_switch_to_MAC = \
            self.F, self.N, self.src, self.dst, self.monitoring_lp_problem, self.map_sourceSwitch_to_host, self.map_switch_to_MAC

        routing_matrix = self.__routing_matrix()
        # def index_extractor(input):
        #     """ remove waste characters """
        #     input = input.replace('(', '').replace(',', '').replace(')', '')
        #     return int(str(input).split('_')[1]), int(str(input).split('_')[2]), int(str(input).split('_')[3])
        def find_next_hob(f, i):
            for j in range(N):
                if routing_matrix[i][j][f] != 0:
                    return j
            ''' if there is not any next hob then return current hob'''
            return -1
        # ''' create route-matrix'''
        # routing_matrix = [[[0 for f in range(F)] for j in range(N)] for i in range(N)]
        # for variable in solved_problem.variables():
        #     if int(variable.varValue) != 0:
        #         if 'R_(' in variable.name:
        #             x, y, z = index_extractor(variable.name)
        #             routing_matrix[x][y][z] = int(variable.varValue)

        ''' create routes-rule-entries'''
        routes_rule_entries = [[] for f in range(F)]
        for f in range(F):
            tmp_src = src[f]
            # add source host
            routes_rule_entries[f].append(map_sourceSwitch_to_host[map_switch_to_MAC[tmp_src]][0])
            # add switches in the route
            routes_rule_entries[f].append(map_switch_to_MAC[tmp_src])
            ''' In some cases the source and destination are the same (loop): find next hob '''
            tmp_src = find_next_hob(f, tmp_src)
            # if the next hob is not -1 (meaning there is not any next hob) add that to route-rules
            if tmp_src != -1:
                routes_rule_entries[f].append(map_switch_to_MAC[tmp_src])
            while tmp_src != dst[f] and tmp_src != -1:
                ''' find next hob '''
                tmp_src = find_next_hob(f, tmp_src)
                # if next-hob is -1 means there is not any next hob
                if tmp_src != -1:
                    routes_rule_entries[f].append(map_switch_to_MAC[tmp_src])
            #add destination host
            routes_rule_entries[f].append(map_sourceSwitch_to_host[map_switch_to_MAC[dst[f]]][0])
        if self.__forwarding_table_entries is None:
            self.__forwarding_table_entries = routes_rule_entries
        else:
            # merge new and existing forwarding table entries
            garbage_output = [self.__forwarding_table_entries.append(entry) for entry in routes_rule_entries]
    def __purge_redundant_flows(self):
        tempF = len(self.__forwarding_table_entries)
        for f in range(tempF-1, -1 , -1):
            ''' removing flows doesn't leave the source switch'''
            if len(self.__forwarding_table_entries[f]) == 3 or (len(self.__forwarding_table_entries[f]) == 4 and self.__forwarding_table_entries[f][1] == self.__forwarding_table_entries[f][2]):
                self.F -= 1
                del self.__forwarding_table_entries[f]
                for i in range(self.N):
                    for j in range(self.N):
                        del self.routing_matrix[i][j][f]
    def solve_optimal(self, time_limit=None):
        """ Three steps: 1. Create Problem,  2. Define Variables, and 3. Define Constraints"""
        ''' Step 1. create a (I)LP problem '''
        monitoring_lp_problem = pulp.LpProblem("Route_Calculation_for_Monitoring", pulp.LpProblem)

        ''' to simplify the writing '''
        N, F, src, dst, A, mu, L, flow_rate, B, x = self.N, self.F, self.src, self.dst, self.A, self.mu, self.L, self.flow_rate, self.B, self.x
        active_optional_constraint, min_num_monitoring_flows, E = self.active_optional_constraint, self.min_num_monitoring_flows, self.E

        '''Step 2. define (I)LP variables --> cat={'Binary', 'Continuous', 'Integer'} '''
        R = pulp.LpVariable.dicts('R', ((i, j, f) for i in range(N) for j in range(N) for f in range(F)), cat='Binary')
        P = pulp.LpVariable.dicts('P', ((i, j, f) for i in range(N) for j in range(N) for f in range(F)), lowBound=0, upBound=L + 1, cat='Integer')
        O = pulp.LpVariable.dicts('O', ((f) for f in range(F) ), cat='Binary')
        # Y = pulp.LpVariable.dicts('Y', ((f, f_prime) for f in range(F) for f_prime in range(F)), cat='Binary') #meta-variable used to make sure there is not any repeated path (similar path for two probes)

        '''Objective function'''
        monitoring_lp_problem += pulp.lpSum([R[i, j, f] for i in range(N) for j in range(N) for f in range(F)]) # minimize summation of all path lengths
        # monitoring_lp_problem += R[0, 0, 0]
        ''' -1 for MAX the objective function and 1 for minimization of that'''
        monitoring_lp_problem.sense = 1

        '''Step 3.  Define constraints '''
        '''****************************** DO NOT USE < OR > *****************************
        ************************ JUST DO USE >= OR <= OR == *****************************
        ************** NUMPY VALUES ARE DIFFERENT FROM SIMPLE VALUES ********************
        ******************** NUMPY.INT64(0) is not the same as 0 *********************'''
        ''' ensure the links used through a path are not virtual links'''
        for i in range(N):
            for j in range(N):
                for f in range(F):
                    monitoring_lp_problem += R[i, j, f] <= int(A[i][j])
        ''' Ensure all links are covered --- MERGED WITH THE NEXT CONSTRAINT'''
        # for i in range(N):
        #     for j in range(N):
        #         monitoring_lp_problem += int(A[i][j]) <= pulp.lpSum(R[i, j, f] for f in range(F))
        ''' having more than x flows traversing every link, if x=1 then Ensure all links are covered'''
        for i in range(N):
            for j in range(N):
                monitoring_lp_problem += pulp.lpSum(R[i, j, f] for f in range(F)) >= x * int(A[i][j])
        ''' Leave Source and Enter to destination '''
        for f in range(F):
            # Leave Source
            monitoring_lp_problem += pulp.lpSum(R[src[f], j, f] for j in range(N)) == O[f]
            # Enter Destination
            monitoring_lp_problem += pulp.lpSum(R[i, dst[f], f] for i in range(N)) == O[f]
        ''' Flow conservation if both src==dst and src!=dst is possible'''
        for i in range(N):
            for f in range(F):
                if i==src[f] and i!=dst[f]:
                    monitoring_lp_problem += pulp.lpSum(R[i, j, f] for j in range(N)) - pulp.lpSum(R[j, i, f] for j in range(N)) == O[f]
                elif i!=src[f] and i==dst[f]:
                    monitoring_lp_problem += pulp.lpSum(R[i, j, f] for j in range(N)) - pulp.lpSum(R[j, i, f] for j in range(N)) == -O[f]
                else:
                    monitoring_lp_problem += pulp.lpSum(R[i, j, f] for j in range(N)) - pulp.lpSum(R[j, i, f] for j in range(N)) == 0
        '''  monitoring flows use at most 𝜇 percent of link bandwidth'''
        if active_optional_constraint:
            for i in range(N):
                for j in range(N):
                    monitoring_lp_problem += pulp.lpSum(R[i, j, f] for f in range(F)) * flow_rate <= mu * B[i][j]
        ''' prevent unwanted loops'''
        for i in range(N):
            for f in range(F):
                monitoring_lp_problem += pulp.lpSum(R[i, j, f] for j in range(N)) <= 1
        ''' Keep the length of monitoring routes less than a predefined value'''
        for f in range(F):
            monitoring_lp_problem += pulp.lpSum([R[i, j, f] for i in range(N) for j in range(N)]) <= L
        ''' If R[i, j, f] is zero then P[i, j, f] is zero'''
        for f in range(F):
            for i in range(N):
                for j in range(N):
                    monitoring_lp_problem += P[i, j, f] <= (L + 1) * R[i, j, f]
        ''' whether a flow should be used for monitoring'''
        for f in range(F):
            for i in range(N):
                for j in range(N):
                    monitoring_lp_problem += R[i,j,f] <= O[f]
        ''' Number of monitoring flows should always be more thana predefined threshold'''
        monitoring_lp_problem += pulp.lpSum([O[f] for f in range(F)]) >= min_num_monitoring_flows
        ''' Number of monitoring flows should always be less or equal to the number of links to be monitored'''
        monitoring_lp_problem += pulp.lpSum([O[f] for f in range(F)]) <= E
        ''' Add the value of P by one, after each step'''
        for f in range(F):
            for i in range(N):
                if not i == src[f] == dst[f]:
                    monitoring_lp_problem += lpSum([P[i, j, f] for j in range(N)]) == lpSum(
                        [P[j, i, f] + R[j, i, f] for j in range(N)])
        ''' Prevent flows from leaving the source twice in ordering matrix P'''
        for f in range(F):
            monitoring_lp_problem += pulp.lpSum([P[src[f],j,f] for j in range(N)]) == O[f]
        ''' No repeated path (n-equation m-unknown where n<m has infinite answers, n>m has no answer, n==m has one answer'''
        # for f in range(F):
        #     for f_prime in range(f+1, F):
        #         # monitoring_lp_problem += pulp.lpSum([((N+1)*i+j)*R[i, j, f] for i in range(N) for j in range(N)])-pulp.lpSum([((N+1)*i+j)*R[i, j, f_prime] for i in range(N) for j in range(N)]) <= Y[f, f_prime]*self.big_number + (1-O[f])*self.big_number+(1-O[f_prime])*self.big_number
        #         # monitoring_lp_problem += pulp.lpSum([((N+1)*i+j)*R[i, j, f] for i in range(N) for j in range(N)])-pulp.lpSum([((N+1)*i+j)*R[i, j, f_prime] for i in range(N) for j in range(N)]) + (1-O[f])*self.big_number+(1-O[f_prime])*self.big_number >= -Y[f, f_prime]*self.big_number
        #         # monitoring_lp_problem += pulp.lpSum([((N+1)*i+j)*R[i, j, f] for i in range(N) for j in range(N)])-pulp.lpSum([((N+1)*i+j)*R[i, j, f_prime] for i in range(N) for j in range(N)]) + (1-O[f])*self.big_number+(1-O[f_prime])*self.big_number >= 1 -Y[f, f_prime]*(N+1)*self.big_number
        #         monitoring_lp_problem += pulp.lpSum([((N+1)*i+j)*R[i, j, f] for i in range(N) for j in range(N)])-pulp.lpSum([((N+1)*i+j)*R[i, j, f_prime] for i in range(N) for j in range(N)]) + (1-O[f])*self.big_number + (1-O[f_prime])*self.big_number >= 1 - Y[f, f_prime]*self.big_number
        #         monitoring_lp_problem += pulp.lpSum([((N+1)*i+j)*R[i, j, f] for i in range(N) for j in range(N)])-pulp.lpSum([((N+1)*i+j)*R[i, j, f_prime] for i in range(N) for j in range(N)]) + (1-O[f])*self.big_number + (1-O[f_prime])*self.big_number <= -1 + (1-Y[f, f_prime])*self.big_number
        for f in range(F):
            for f_prime in range(f+1, F):
                if src[f] == src[f_prime] and dst[f] == dst[f_prime]:
                    monitoring_lp_problem += pulp.lpSum([((N+1)*i+j)*R[i, j, f] for i in range(N) for j in range(N)])+ (1-O[f])*self.big_number + (1-O[f_prime])*self.big_number >= 1+pulp.lpSum([((N+1)*i+j)*R[i, j, f_prime] for i in range(N) for j in range(N)])

        self.monitoring_lp_problem = monitoring_lp_problem

        if time_limit is None:
            self.monitoring_lp_problem.solve()
        else:
            self.monitoring_lp_problem.setSolver(GLPK_CMD)
            self.monitoring_lp_problem.solve(GLPK_CMD(msg=1, options=["--tmlim", str(time_limit)]))


        # self.monitoring_lp_problem.parameters.timelimit.set(300.0)

        # P = monitoring_lp_problem
        # Build the solverModel for your preferred
        # solver = pulp.GLPK_CMD()
        # solver.buildSolverModel(P)

        #Modify the solvermodel
        # solver.solverModel.parameters.timelimit.set(60)

        #Solve P
        # solver.callSolver(P)
        # status = solver.findSolutionValues(P)
    def solve_optimal_fast(self, time_limite=None):
        """ Three steps: 1. Create Problem,  2. Define Variables, and 3. Define Constraints"""
        ''' Step 1. create a (I)LP problem '''
        monitoring_lp_problem = pulp.LpProblem("Route_Calculation_for_Monitoring", pulp.LpProblem)

        ''' to simplify the writing '''
        N, F, src, dst, A, mu, L, flow_rate, B, x = self.N, self.F, self.src, self.dst, self.A, self.mu, self.L, self.flow_rate, self.B, self.x
        active_optional_constraint, min_num_monitoring_flows, E = self.active_optional_constraint, self.min_num_monitoring_flows, self.E

        '''Step 2. define (I)LP variables --> cat={'Binary', 'Continuous', 'Integer'} '''
        R = pulp.LpVariable.dicts('R', ((i, j, f) for i in range(N) for j in range(N) for f in range(F)), cat='Binary')
        # P = pulp.LpVariable.dicts('P', ((i, j, f) for i in range(N) for j in range(N) for f in range(F)), lowBound=0, upBound=L + 1, cat='Integer')
        # O = pulp.LpVariable.dicts('O', ((f) for f in range(F) ), cat='Binary')
        # Y = pulp.LpVariable.dicts('Y', ((f, f_prime) for f in range(F) for f_prime in range(F)), cat='Binary') #meta-variable used to make sure there is not any repeated path (similar path for two probes)

        '''Objective function'''
        monitoring_lp_problem += pulp.lpSum([R[i, j, f] for i in range(N) for j in range(N) for f in range(F)]) # minimize summation of all path lengths
        # monitoring_lp_problem += R[0, 0, 0]
        ''' -1 for MAX the objective function and 1 for minimization of that'''
        monitoring_lp_problem.sense = 1

        '''Step 3.  Define constraints '''
        '''****************************** DO NOT USE < OR > *****************************
        ************************ JUST DO USE >= OR <= OR == *****************************
        ************** NUMPY VALUES ARE DIFFERENT FROM SIMPLE VALUES ********************
        ******************** NUMPY.INT64(0) is not the same as 0 *********************'''
        ''' ensure the links used through a path are not virtual links'''
        for i in range(N):
            for j in range(N):
                for f in range(F):
                    monitoring_lp_problem += R[i, j, f] <= int(A[i][j])
        ''' Ensure all links are covered --- MERGED WITH THE NEXT CONSTRAINT'''
        # for i in range(N):
        #     for j in range(N):
        #         monitoring_lp_problem += int(A[i][j]) <= pulp.lpSum(R[i, j, f] for f in range(F))
        ''' having more than x flows traversing every link, if x=1 then Ensure all links are covered'''
        for i in range(N):
            for j in range(N):
                monitoring_lp_problem += pulp.lpSum(R[i, j, f] for f in range(F)) >= x * int(A[i][j])
        ''' Leave Source and Enter to destination '''
        for f in range(F):
            # Leave Source
            monitoring_lp_problem += pulp.lpSum(R[src[f], j, f] for j in range(N)) == 1
            # Enter Destination
            monitoring_lp_problem += pulp.lpSum(R[i, dst[f], f] for i in range(N)) == 1
        ''' Flow conservation if both src==dst and src!=dst is possible'''
        for i in range(N):
            for f in range(F):
                if i==src[f] and i!=dst[f]:
                    monitoring_lp_problem += pulp.lpSum(R[i, j, f] for j in range(N)) - pulp.lpSum(R[j, i, f] for j in range(N)) == 1
                elif i!=src[f] and i==dst[f]:
                    monitoring_lp_problem += pulp.lpSum(R[i, j, f] for j in range(N)) - pulp.lpSum(R[j, i, f] for j in range(N)) == -1
                else:
                    monitoring_lp_problem += pulp.lpSum(R[i, j, f] for j in range(N)) - pulp.lpSum(R[j, i, f] for j in range(N)) == 0
        '''  monitoring flows use at most 𝜇 percent of link bandwidth'''
        if active_optional_constraint:
            for i in range(N):
                for j in range(N):
                    monitoring_lp_problem += pulp.lpSum(R[i, j, f] for f in range(F)) * flow_rate <= mu * B[i][j]
        ''' prevent unwanted loops'''
        for i in range(N):
            for f in range(F):
                monitoring_lp_problem += pulp.lpSum(R[i, j, f] for j in range(N)) <= 1
        ''' Keep the length of monitoring routes less than a predefined value'''
        for f in range(F):
            monitoring_lp_problem += pulp.lpSum([R[i, j, f] for i in range(N) for j in range(N)]) <= L
        ''' If R[i, j, f] is zero then P[i, j, f] is zero'''
        # for f in range(F):
        #     for i in range(N):
        #         for j in range(N):
        #             monitoring_lp_problem += P[i, j, f] <= (L + 1) * R[i, j, f]
        ''' whether a flow should be used for monitoring'''
        # for f in range(F):
        #     for i in range(N):
        #         for j in range(N):
        #             monitoring_lp_problem += R[i,j,f] <= O[f]
        ''' Number of monitoring flows should always be more than a predefined threshold'''
        # monitoring_lp_problem += pulp.lpSum([O[f] for f in range(F)]) >= min_num_monitoring_flows
        ''' Number of monitoring flows should always be less or equal to the number of links to be monitored'''
        # monitoring_lp_problem += pulp.lpSum([O[f] for f in range(F)]) <= E
        ''' Add the value of P by one, after each step'''
        # for f in range(F):
        #     for i in range(N):
        #         if not i == src[f] == dst[f]:
        #             monitoring_lp_problem += lpSum([P[i, j, f] for j in range(N)]) == lpSum(
        #                 [P[j, i, f] + R[j, i, f] for j in range(N)])
        ''' Prevent flows from leaving the source twice in ordering matrix P'''
        for f in range(F):
            monitoring_lp_problem += pulp.lpSum([R[src[f],j,f] for j in range(N)]) == 1
        ''' No repeated path (n-equation m-unknown where n<m has infinite answers, n>m has no answer, n==m has one answer'''
        # for f in range(F):
        #     for f_prime in range(f+1, F):
        #         # monitoring_lp_problem += pulp.lpSum([((N+1)*i+j)*R[i, j, f] for i in range(N) for j in range(N)])-pulp.lpSum([((N+1)*i+j)*R[i, j, f_prime] for i in range(N) for j in range(N)]) <= Y[f, f_prime]*self.big_number + (1-O[f])*self.big_number+(1-O[f_prime])*self.big_number
        #         # monitoring_lp_problem += pulp.lpSum([((N+1)*i+j)*R[i, j, f] for i in range(N) for j in range(N)])-pulp.lpSum([((N+1)*i+j)*R[i, j, f_prime] for i in range(N) for j in range(N)]) + (1-O[f])*self.big_number+(1-O[f_prime])*self.big_number >= -Y[f, f_prime]*self.big_number
        #         # monitoring_lp_problem += pulp.lpSum([((N+1)*i+j)*R[i, j, f] for i in range(N) for j in range(N)])-pulp.lpSum([((N+1)*i+j)*R[i, j, f_prime] for i in range(N) for j in range(N)]) + (1-O[f])*self.big_number+(1-O[f_prime])*self.big_number >= 1 -Y[f, f_prime]*(N+1)*self.big_number
        #         monitoring_lp_problem += pulp.lpSum([((N+1)*i+j)*R[i, j, f] for i in range(N) for j in range(N)])-pulp.lpSum([((N+1)*i+j)*R[i, j, f_prime] for i in range(N) for j in range(N)]) + (1-O[f])*self.big_number + (1-O[f_prime])*self.big_number >= 1 - Y[f, f_prime]*self.big_number
        #         monitoring_lp_problem += pulp.lpSum([((N+1)*i+j)*R[i, j, f] for i in range(N) for j in range(N)])-pulp.lpSum([((N+1)*i+j)*R[i, j, f_prime] for i in range(N) for j in range(N)]) + (1-O[f])*self.big_number + (1-O[f_prime])*self.big_number <= -1 + (1-Y[f, f_prime])*self.big_number
        for f in range(F):
            for f_prime in range(f+1, F):
                if src[f] == src[f_prime] and dst[f] == dst[f_prime]:
                    monitoring_lp_problem += pulp.lpSum([((N+1)*i+j)*R[i, j, f] for i in range(N) for j in range(N)]) >= 1+pulp.lpSum([((N+1)*i+j)*R[i, j, f_prime] for i in range(N) for j in range(N)])

        self.monitoring_lp_problem = monitoring_lp_problem

        if time_limite is None:
            self.monitoring_lp_problem.solve()
        else:
            self.monitoring_lp_problem.setSolver(GLPK_CMD)
            self.monitoring_lp_problem.solve(GLPK_CMD(msg=1, options=["--tmlim", str(time_limite)]))


        # self.monitoring_lp_problem.parameters.timelimit.set(300.0)

        # P = monitoring_lp_problem
        # Build the solverModel for your preferred
        # solver = pulp.GLPK_CMD()
        # solver.buildSolverModel(P)

        #Modify the solvermodel
        # solver.solverModel.parameters.timelimit.set(60)

        #Solve P
        # solver.callSolver(P)
        # status = solver.findSolutionValues(P)
    def solve_optimal_without_step_rotuing(self, time_limit=None):
        """ Three steps: 1. Create Problem,  2. Define Variables, and 3. Define Constraints"""
        ''' Step 1. create a (I)LP problem '''
        monitoring_lp_problem = pulp.LpProblem("Route_Calculation_for_Monitoring", pulp.LpProblem)

        ''' to simplify the writing '''
        N, F, src, dst, A, mu, L, flow_rate, B, x = self.N, self.F, self.src, self.dst, self.A, self.mu, self.L, self.flow_rate, self.B, self.x
        active_optional_constraint, min_num_monitoring_flows, E = self.active_optional_constraint, self.min_num_monitoring_flows, self.E

        '''Step 2. define (I)LP variables --> cat={'Binary', 'Continuous', 'Integer'} '''
        R = pulp.LpVariable.dicts('R', ((i, j, f) for i in range(N) for j in range(N) for f in range(F)), cat='Binary')
        # P = pulp.LpVariable.dicts('P', ((i, j, f) for i in range(N) for j in range(N) for f in range(F)), lowBound=0, upBound=L + 1, cat='Integer')
        O = pulp.LpVariable.dicts('O', ((f) for f in range(F) ), cat='Binary')
        # Y = pulp.LpVariable.dicts('Y', ((f, f_prime) for f in range(F) for f_prime in range(F)), cat='Binary') #meta-variable used to make sure there is not any repeated path (similar path for two probes)

        '''Objective function'''
        monitoring_lp_problem += pulp.lpSum([R[i, j, f] for i in range(N) for j in range(N) for f in range(F)]) # minimize summation of all path lengths
        # monitoring_lp_problem += R[0, 0, 0]
        ''' -1 for MAX the objective function and 1 for minimization of that'''
        monitoring_lp_problem.sense = 1

        '''Step 3.  Define constraints '''
        '''****************************** DO NOT USE < OR > *****************************
        ************************ JUST DO USE >= OR <= OR == *****************************
        ************** NUMPY VALUES ARE DIFFERENT FROM SIMPLE VALUES ********************
        ******************** NUMPY.INT64(0) is not the same as 0 *********************'''
        ''' ensure the links used through a path are not virtual links'''
        for i in range(N):
            for j in range(N):
                for f in range(F):
                    monitoring_lp_problem += R[i, j, f] <= int(A[i][j])
        ''' Ensure all links are covered --- MERGED WITH THE NEXT CONSTRAINT'''
        # for i in range(N):
        #     for j in range(N):
        #         monitoring_lp_problem += int(A[i][j]) <= pulp.lpSum(R[i, j, f] for f in range(F))
        ''' having more than x flows traversing every link, if x=1 then Ensure all links are covered'''
        for i in range(N):
            for j in range(N):
                monitoring_lp_problem += pulp.lpSum(R[i, j, f] for f in range(F)) >= x * int(A[i][j])
        ''' Leave Source and Enter to destination '''
        for f in range(F):
            # Leave Source
            monitoring_lp_problem += pulp.lpSum(R[src[f], j, f] for j in range(N)) == O[f]
            # Enter Destination
            monitoring_lp_problem += pulp.lpSum(R[i, dst[f], f] for i in range(N)) == O[f]
        ''' Flow conservation if both src==dst and src!=dst is possible'''
        for i in range(N):
            for f in range(F):
                if i==src[f] and i!=dst[f]:
                    monitoring_lp_problem += pulp.lpSum(R[i, j, f] for j in range(N)) - pulp.lpSum(R[j, i, f] for j in range(N)) == O[f]
                elif i!=src[f] and i==dst[f]:
                    monitoring_lp_problem += pulp.lpSum(R[i, j, f] for j in range(N)) - pulp.lpSum(R[j, i, f] for j in range(N)) == -O[f]
                else:
                    monitoring_lp_problem += pulp.lpSum(R[i, j, f] for j in range(N)) - pulp.lpSum(R[j, i, f] for j in range(N)) == 0
        '''  monitoring flows use at most 𝜇 percent of link bandwidth'''
        if active_optional_constraint:
            for i in range(N):
                for j in range(N):
                    monitoring_lp_problem += pulp.lpSum(R[i, j, f] for f in range(F)) * flow_rate <= mu * B[i][j]
        ''' prevent unwanted loops'''
        for i in range(N):
            for f in range(F):
                monitoring_lp_problem += pulp.lpSum(R[i, j, f] for j in range(N)) <= 1
        ''' Keep the length of monitoring routes less than a predefined value'''
        for f in range(F):
            monitoring_lp_problem += pulp.lpSum([R[i, j, f] for i in range(N) for j in range(N)]) <= L
        ''' If R[i, j, f] is zero then P[i, j, f] is zero'''
        # for f in range(F):
        #     for i in range(N):
        #         for j in range(N):
        #             monitoring_lp_problem += P[i, j, f] <= (L + 1) * R[i, j, f]
        ''' whether a flow should be used for monitoring'''
        for f in range(F):
            for i in range(N):
                for j in range(N):
                    monitoring_lp_problem += R[i,j,f] <= O[f]
        ''' Number of monitoring flows should always be more thana predefined threshold'''
        monitoring_lp_problem += pulp.lpSum([O[f] for f in range(F)]) >= min_num_monitoring_flows
        ''' Number of monitoring flows should always be less or equal to the number of links to be monitored'''
        monitoring_lp_problem += pulp.lpSum([O[f] for f in range(F)]) <= E
        ''' Add the value of P by one, after each step'''
        # for f in range(F):
        #     for i in range(N):
        #         if not i == src[f] == dst[f]:
        #             monitoring_lp_problem += lpSum([P[i, j, f] for j in range(N)]) == lpSum([P[j, i, f] + R[j, i, f] for j in range(N)])
        ''' Prevent flows from leaving the source twice in ordering matrix P'''
        for f in range(F):
            monitoring_lp_problem += pulp.lpSum([R[src[f],j,f] for j in range(N)]) == O[f]
        ''' No repeated path (n-equation m-unknown where n<m has infinite answers, n>m has no answer, n==m has one answer'''
        # for f in range(F):
        #     for f_prime in range(f+1, F):
        #         # monitoring_lp_problem += pulp.lpSum([((N+1)*i+j)*R[i, j, f] for i in range(N) for j in range(N)])-pulp.lpSum([((N+1)*i+j)*R[i, j, f_prime] for i in range(N) for j in range(N)]) <= Y[f, f_prime]*self.big_number + (1-O[f])*self.big_number+(1-O[f_prime])*self.big_number
        #         # monitoring_lp_problem += pulp.lpSum([((N+1)*i+j)*R[i, j, f] for i in range(N) for j in range(N)])-pulp.lpSum([((N+1)*i+j)*R[i, j, f_prime] for i in range(N) for j in range(N)]) + (1-O[f])*self.big_number+(1-O[f_prime])*self.big_number >= -Y[f, f_prime]*self.big_number
        #         # monitoring_lp_problem += pulp.lpSum([((N+1)*i+j)*R[i, j, f] for i in range(N) for j in range(N)])-pulp.lpSum([((N+1)*i+j)*R[i, j, f_prime] for i in range(N) for j in range(N)]) + (1-O[f])*self.big_number+(1-O[f_prime])*self.big_number >= 1 -Y[f, f_prime]*(N+1)*self.big_number
        #         monitoring_lp_problem += pulp.lpSum([((N+1)*i+j)*R[i, j, f] for i in range(N) for j in range(N)])-pulp.lpSum([((N+1)*i+j)*R[i, j, f_prime] for i in range(N) for j in range(N)]) + (1-O[f])*self.big_number + (1-O[f_prime])*self.big_number >= 1 - Y[f, f_prime]*self.big_number
        #         monitoring_lp_problem += pulp.lpSum([((N+1)*i+j)*R[i, j, f] for i in range(N) for j in range(N)])-pulp.lpSum([((N+1)*i+j)*R[i, j, f_prime] for i in range(N) for j in range(N)]) + (1-O[f])*self.big_number + (1-O[f_prime])*self.big_number <= -1 + (1-Y[f, f_prime])*self.big_number
        for f in range(F):
            for f_prime in range(f+1, F):
                if src[f] == src[f_prime] and dst[f] == dst[f_prime]:
                    monitoring_lp_problem += pulp.lpSum([((N+1)*i+j)*R[i, j, f] for i in range(N) for j in range(N)])+ (1-O[f])*self.big_number + (1-O[f_prime])*self.big_number >= 1+pulp.lpSum([((N+1)*i+j)*R[i, j, f_prime] for i in range(N) for j in range(N)])

        self.monitoring_lp_problem = monitoring_lp_problem

        if time_limit is None:
            self.monitoring_lp_problem.solve()
        else:
            self.monitoring_lp_problem.setSolver(GLPK_CMD)
            self.monitoring_lp_problem.solve(GLPK_CMD(msg=1, options=["--tmlim", str(time_limit)]))


        # self.monitoring_lp_problem.parameters.timelimit.set(300.0)

        # P = monitoring_lp_problem
        # Build the solverModel for your preferred
        # solver = pulp.GLPK_CMD()
        # solver.buildSolverModel(P)

        #Modify the solvermodel
        # solver.solverModel.parameters.timelimit.set(60)

        #Solve P
        # solver.callSolver(P)
        # status = solver.findSolutionValues(P)

    def forwarding_table_entries(self):
        if self.monitoring_lp_problem is None:
            raise Exception('Problem is not solved yet')
        if self.optimality_status() == 'Optimal' and self.__forwarding_table_entries is None:
            self.__convert_to_routing_rule_entries()
            self.__purge_redundant_flows()
        return self.__forwarding_table_entries
    def optimality_status(self):
        if monitoring is None: raise Exception('Problem is not defined yet')
        return LpStatus[self.monitoring_lp_problem.status]
    def selected_routes(self):
        if self.monitoring_lp_problem is not None:
            print("Objective function value: {}".format(pulp.value(self.monitoring_lp_problem.objective)))
            print('Variables: ')
            for variable in self.monitoring_lp_problem.variables():
                if int(variable.varValue) != 0 and 'O_' in variable.name:
                    print("   {} = {}".format(variable.name, variable.varValue))
        else:
            raise Exception('The problem is not solved yet.')
    def print_results(self):
        if self.monitoring_lp_problem is not None:
            print('Problem Solving Status: {}'.format(pulp.LpStatus[self.monitoring_lp_problem.status]))
            print("Objective function value: {}".format(pulp.value(self.monitoring_lp_problem.objective)))
            print('Variables: ')
            for variable in self.monitoring_lp_problem.variables():
                if int(variable.varValue) != 0:
                    print("   {} = {}".format(variable.name, variable.varValue))
        else:
            raise Exception('The problem is not solved yet.')
if __name__ == '__main__':
    # main()
    now = datetime.datetime.now()
    topo = {('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:02', 's'): 1,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:0a', 's'): 1,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:0b', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:0c', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:01', 's'): 1,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:03', 's'): 1,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:09', 's'): 1,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:0a', 's'): 1,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:0b', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:0c', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:02', 's'): 1,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:04', 's'): 1,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:0a', 's'): 1,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:0b', 's'): 1,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:0c', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:03', 's'): 1,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:05', 's'): 1,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:0b', 's'): 1,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:0c', 's'): 1,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:0d', 's'): 1,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:04', 's'): 1,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:06', 's'): 1,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:0b', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:0c', 's'): 1,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:0d', 's'): 1,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:0e', 's'): 1,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:05', 's'): 1,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:07', 's'): 1,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:0b', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:0c', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:0f', 's'): 1,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:15', 's'): 1,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:16', 's'): 1,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:06', 's'): 1,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:08', 's'): 1,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:0b', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:0c', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:0e', 's'): 1,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:0f', 's'): 1,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:10', 's'): 1,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:07', 's'): 1,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:0b', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:0c', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:0f', 's'): 1,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:10', 's'): 1,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:02', 's'): 1,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:0b', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:0c', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:11', 's'): 1,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:1b', 's'): 1,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:01', 's'): 1,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:02', 's'): 1,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:03', 's'): 1,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:0b', 's'): 1,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:0c', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:11', 's'): 1,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:12', 's'): 1,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:13', 's'): 1,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:14', 's'): 1,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:03', 's'): 1,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:04', 's'): 1,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:0a', 's'): 1,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:0b', 's'): 0,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:0c', 's'): 1,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:12', 's'): 1,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:13', 's'): 1,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:14', 's'): 1,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:15', 's'): 1,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:16', 's'): 1,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:0b', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:04', 's'): 1,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:05', 's'): 1,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:0b', 's'): 1,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:0c', 's'): 0,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:0d', 's'): 1,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:1a', 's'): 1,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:1b', 's'): 1,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:1c', 's'): 1,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:1d', 's'): 1,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:1e', 's'): 1,('00:00:00:00:00:00:00:0c', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:04', 's'): 1,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:05', 's'): 1,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:0b', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:0c', 's'): 1,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:0e', 's'): 1,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:17', 's'): 1,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:1d', 's'): 1,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:0d', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:05', 's'): 1,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:07', 's'): 1,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:0b', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:0c', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:0d', 's'): 1,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:0f', 's'): 1,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:17', 's'): 1,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:18', 's'): 1,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:1a', 's'): 1,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:1e', 's'): 1,('00:00:00:00:00:00:00:0e', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:06', 's'): 1,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:07', 's'): 1,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:08', 's'): 1,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:0b', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:0c', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:0e', 's'): 1,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:16', 's'): 1,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:17', 's'): 1,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:18', 's'): 1,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:0f', '00:00:00:00:00:00:00:1f', 's'): 1,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:07', 's'): 1,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:08', 's'): 1,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:0b', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:0c', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:17', 's'): 1,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:18', 's'): 1,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:10', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:09', 's'): 1,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:0a', 's'): 1,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:0b', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:0c', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:19', 's'): 1,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:11', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:0a', 's'): 1,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:0b', 's'): 1,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:0c', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:1a', 's'): 1,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:12', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:0a', 's'): 1,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:0b', 's'): 1,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:0c', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:1b', 's'): 1,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:13', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:0a', 's'): 1,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:0b', 's'): 1,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:0c', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:1d', 's'): 1,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:14', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:06', 's'): 1,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:0b', 's'): 1,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:0c', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:1b', 's'): 1,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:15', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:06', 's'): 1,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:0b', 's'): 1,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:0c', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:0f', 's'): 1,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:1e', 's'): 1,('00:00:00:00:00:00:00:16', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:0b', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:0c', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:0d', 's'): 1,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:0e', 's'): 1,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:0f', 's'): 1,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:10', 's'): 1,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:1e', 's'): 1,('00:00:00:00:00:00:00:17', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:0b', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:0c', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:0e', 's'): 1,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:0f', 's'): 1,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:10', 's'): 1,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:18', '00:00:00:00:00:00:00:1f', 's'): 1,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:0b', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:0c', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:11', 's'): 1,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:1a', 's'): 1,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:19', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:0b', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:0c', 's'): 1,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:0e', 's'): 1,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:12', 's'): 1,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:19', 's'): 1,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:1b', 's'): 1,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:1a', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:09', 's'): 1,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:0b', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:0c', 's'): 1,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:13', 's'): 1,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:15', 's'): 1,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:1a', 's'): 1,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:1c', 's'): 1,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:1b', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:0b', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:0c', 's'): 1,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:1b', 's'): 1,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:1d', 's'): 1,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:1c', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:0b', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:0c', 's'): 1,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:0d', 's'): 1,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:14', 's'): 1,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:1c', 's'): 1,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:1e', 's'): 1,('00:00:00:00:00:00:00:1d', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:0b', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:0c', 's'): 1,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:0e', 's'): 1,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:0f', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:16', 's'): 1,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:17', 's'): 1,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:18', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:1d', 's'): 1,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:1e', 's'): 0,('00:00:00:00:00:00:00:1e', '00:00:00:00:00:00:00:1f', 's'): 1,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:01', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:02', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:03', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:04', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:05', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:06', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:07', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:08', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:09', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:0a', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:0b', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:0c', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:0d', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:0e', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:0f', 's'): 1,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:10', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:11', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:12', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:13', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:14', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:15', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:16', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:17', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:18', 's'): 1,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:19', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:1a', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:1b', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:1c', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:1d', 's'): 0,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:1e', 's'): 1,('00:00:00:00:00:00:00:1f', '00:00:00:00:00:00:00:1f', 's'): 0,('00:00:00:00:00:01', '00:00:00:00:00:00:00:19', 'h'): 1,('00:00:00:00:00:02', '00:00:00:00:00:00:00:1a', 'h'): 1,('00:00:00:00:00:03', '00:00:00:00:00:00:00:1b', 'h'): 1,('00:00:00:00:00:04', '00:00:00:00:00:00:00:1c', 'h'): 1,('00:00:00:00:00:05', '00:00:00:00:00:00:00:1d', 'h'): 1,('00:00:00:00:00:06', '00:00:00:00:00:00:00:1e', 'h'): 1,('00:00:00:00:00:07', '00:00:00:00:00:00:00:1f', 'h'): 1,('00:00:00:00:00:08', '00:00:00:00:00:00:00:18', 'h'): 1,('00:00:00:00:00:09', '00:00:00:00:00:00:00:10', 'h'): 1,('00:00:00:00:00:10', '00:00:00:00:00:00:00:08', 'h'): 1,('00:00:00:00:00:11', '00:00:00:00:00:00:00:07', 'h'): 1,('00:00:00:00:00:12', '00:00:00:00:00:00:00:06', 'h'): 1,('00:00:00:00:00:13', '00:00:00:00:00:00:00:05', 'h'): 1,('00:00:00:00:00:14', '00:00:00:00:00:00:00:04', 'h'): 1,('00:00:00:00:00:15', '00:00:00:00:00:00:00:03', 'h'): 1,('00:00:00:00:00:16', '00:00:00:00:00:00:00:02', 'h'): 1,('00:00:00:00:00:17', '00:00:00:00:00:00:00:01', 'h'): 1}
    # topo = {('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:01', 's'): 0, ('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:02', 's'): 1, ('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:03', 's'): 0, ('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:04', 's'): 0, ('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:05', 's'): 0, ('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:06', 's'): 1, ('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:07', 's'): 0, ('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:08', 's'): 1, ('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:09', 's'): 0, ('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:0a', 's'): 0, ('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:01', 's'): 1, ('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:02', 's'): 0, ('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:03', 's'): 1, ('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:04', 's'): 0, ('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:05', 's'): 0, ('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:06', 's'): 0, ('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:07', 's'): 1, ('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:08', 's'): 0, ('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:09', 's'): 0, ('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:0a', 's'): 0, ('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:01', 's'): 0, ('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:02', 's'): 1, ('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:03', 's'): 0, ('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:04', 's'): 1, ('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:05', 's'): 0, ('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:06', 's'): 0, ('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:07', 's'): 0, ('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:08', 's'): 0, ('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:09', 's'): 0, ('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:0a', 's'): 1, ('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:01', 's'): 0, ('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:02', 's'): 0, ('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:03', 's'): 1, ('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:04', 's'): 0, ('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:05', 's'): 1, ('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:06', 's'): 0, ('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:07', 's'): 0, ('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:08', 's'): 0, ('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:09', 's'): 0, ('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:0a', 's'): 0, ('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:01', 's'): 0, ('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:02', 's'): 0, ('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:03', 's'): 0, ('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:04', 's'): 1, ('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:05', 's'): 0, ('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:06', 's'): 0, ('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:07', 's'): 1, ('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:08', 's'): 0, ('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:09', 's'): 0, ('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:0a', 's'): 1, ('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:01', 's'): 1, ('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:02', 's'): 0, ('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:03', 's'): 0, ('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:04', 's'): 0, ('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:05', 's'): 0, ('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:06', 's'): 0, ('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:07', 's'): 0, ('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:08', 's'): 0, ('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:09', 's'): 1, ('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:0a', 's'): 0, ('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:01', 's'): 0, ('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:02', 's'): 1, ('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:03', 's'): 0, ('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:04', 's'): 0, ('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:05', 's'): 1, ('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:06', 's'): 0, ('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:07', 's'): 0, ('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:08', 's'): 1, ('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:09', 's'): 0, ('00:00:00:00:00:00:00:07', '00:00:00:00:00:00:00:0a', 's'): 0, ('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:01', 's'): 1, ('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:02', 's'): 0, ('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:03', 's'): 0, ('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:04', 's'): 0, ('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:05', 's'): 0, ('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:06', 's'): 0, ('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:07', 's'): 1, ('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:08', 's'): 0, ('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:09', 's'): 1, ('00:00:00:00:00:00:00:08', '00:00:00:00:00:00:00:0a', 's'): 0, ('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:01', 's'): 0, ('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:02', 's'): 0, ('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:03', 's'): 0, ('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:04', 's'): 0, ('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:05', 's'): 0, ('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:06', 's'): 1, ('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:07', 's'): 0, ('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:08', 's'): 1, ('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:09', 's'): 0, ('00:00:00:00:00:00:00:09', '00:00:00:00:00:00:00:0a', 's'): 1, ('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:01', 's'): 0, ('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:02', 's'): 0, ('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:03', 's'): 1, ('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:04', 's'): 0, ('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:05', 's'): 1, ('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:06', 's'): 0, ('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:07', 's'): 0, ('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:08', 's'): 0, ('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:09', 's'): 1, ('00:00:00:00:00:00:00:0a', '00:00:00:00:00:00:00:0a', 's'): 0, ('00:00:00:00:00:01', '00:00:00:00:00:00:00:01', 'h'): 1, ('00:00:00:00:00:02', '00:00:00:00:00:00:00:02', 'h'): 1, ('00:00:00:00:00:03', '00:00:00:00:00:00:00:03', 'h'): 1, ('00:00:00:00:00:04', '00:00:00:00:00:00:00:04', 'h'): 1, ('00:00:00:00:00:05', '00:00:00:00:00:00:00:05', 'h'): 1, ('00:00:00:00:00:06', '00:00:00:00:00:00:00:0a', 'h'): 1, ('00:00:00:00:00:07', '00:00:00:00:00:00:00:09', 'h'): 1, ('00:00:00:00:00:08', '00:00:00:00:00:00:00:08', 'h'): 1}
    # topo = {('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:01', 's'): 0, ('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:02', 's'): 1, ('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:03', 's'): 0, ('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:04', 's'): 0, ('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:05', 's'): 0, ('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:06', 's'): 1, ('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:01', 's'): 1, ('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:02', 's'): 0, ('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:03', 's'): 1, ('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:04', 's'): 0, ('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:05', 's'): 0, ('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:06', 's'): 0, ('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:01', 's'): 0, ('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:02', 's'): 1, ('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:03', 's'): 0, ('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:04', 's'): 1, ('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:05', 's'): 0, ('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:06', 's'): 0, ('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:01', 's'): 0, ('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:02', 's'): 0, ('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:03', 's'): 1, ('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:04', 's'): 0, ('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:05', 's'): 1, ('00:00:00:00:00:00:00:04', '00:00:00:00:00:00:00:06', 's'): 0, ('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:01', 's'): 0, ('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:02', 's'): 0, ('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:03', 's'): 0, ('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:04', 's'): 1, ('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:05', 's'): 0, ('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:06', 's'): 0, ('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:01', 's'): 1, ('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:02', 's'): 0, ('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:03', 's'): 0, ('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:04', 's'): 0, ('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:05', 's'): 0, ('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:06', 's'): 0, ('00:00:00:00:00:00:00:05', '00:00:00:00:00:00:00:06', 's'): 1, ('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:05', 's'): 1,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:06', 's'): 1,('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:03', 's'): 1,('00:00:00:00:00:02', '00:00:00:00:00:00:00:02', 'h'): 1, ('00:00:00:00:00:03', '00:00:00:00:00:00:00:03', 'h'): 1, ('00:00:00:00:00:04', '00:00:00:00:00:00:00:04', 'h'): 1, ('00:00:00:00:00:05', '00:00:00:00:00:00:00:05', 'h'): 1}
    # topo = {('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:02', 's'): 1, ('00:00:00:00:00:00:00:01', '00:00:00:00:00:00:00:06', 's'): 1, ('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:01', 's'): 1, ('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:01', 's'): 1, ('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:02', 's'): 1, ('00:00:00:00:00:00:00:02', '00:00:00:00:00:00:00:03', 's'): 1, ('00:00:00:00:00:00:00:06', '00:00:00:00:00:00:00:03', 's'): 1,('00:00:00:00:00:00:00:03', '00:00:00:00:00:00:00:06', 's'): 1, ('00:00:00:00:00:02', '00:00:00:00:00:00:00:02', 'h'): 1, ('00:00:00:00:00:03', '00:00:00:00:00:00:00:03', 'h'): 1, ('00:00:00:00:00:06', '00:00:00:00:00:00:00:06', 'h'): 1}
    # topo = None
    x = monitoring(in_topo=topo)
    x.solve_optimal(time_limit=300)
    # x.solve_optimal_without_step_rotuing(time_limit=300)
    # x.solve_optimal_fast(time_limite=30)
    # x.solve_incremental()

    optimality_status = x.optimality_status()
    stepped_routing_matrix = x.stepAware_routing_matrix()
    # tmp_routing = x.tmp_routing_matrix()
    forwarding_table_entries = x.forwarding_table_entries()
    routing_matrix = x.routing_matrix

    x.selected_routes()

    print("Solution status: {}".format(optimality_status))
    print("Objective function value: {}".format(pulp.value(x.monitoring_lp_problem.objective)))
    print('Execution time: ' + str(datetime.datetime.now() - now))
    print('Execution time: ' + str(datetime.datetime.now() - now))
    print('Routing matrix:{0}'.format(routing_matrix))
    print('Switch mapping to MAC:{0}'.format(x.map_switch_to_MAC))
    print('Forwarding table entries:{0}'.format(forwarding_table_entries))
    # print('Forwarding table entries:{0}'.format([[ele.replace('00:00:00:00:00:00:00:0','S').replace('00:00:00:00:00:0','H') for ele in element] for element in forwarding_table_entries]))
