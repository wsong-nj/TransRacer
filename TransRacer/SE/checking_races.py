from __future__ import print_function
from parse_code import *
import copy
from global_vars import get_params, set_params, initialize_params, print_params, MyGlobals, clear_globals, optimize_hb
from exploring_paths import *
import z3
from z3 import *
import datetime
from os import path
import sys

sys.path.insert(0, '../concrete_executor')
sys.path.insert(0, '../pkgs')
from check import *
import op_parse
from search_enhance import SearchEnhance
from copy import deepcopy
from math import floor
from web3 import Web3

class RaceDetector:
    '''
	* RaceDetector is responsible for find the race and race bugs
	'''

    def __init__(self, contract_bytecode, contract_address, owner, debug, funclist,noimpFuncs, read_from_blockchain, web3):
        self._contract_bytecode = contract_bytecode
        self._contract_address = contract_address
        self._debug = debug
        self._funclist = funclist
        self.noimpFuncs=noimpFuncs
        self._read_from_blockchain = read_from_blockchain
        self._ops = parse_code(self._contract_bytecode, self._debug)
        self.hb_valid = False
        self.web3 = web3
        self.owner = owner
        self.cfg = None
    # Changes the context into a suitable format.
    def changeContext(self, key, value):
        print('%-20s :  %s ' % (key, str(value)))
        if not ('input' in key and not 'inputlength' in key):
            if isinstance(value, str):
                value = int(value, 16)

            else:
                value = int(value.as_long())

        if 'input' in key and not 'inputlength' in key:
            key = 'tx_input'

        if 'CALLVALUE' in key:
            if value > 10 ** 19:
                value = 10 ** 19
            key = 'tx_value'

        if 'NUMBER' in key:
            if value > 9900000:
                value = 9900000
            key = 'tx_blocknumber'

        if 'GASLIMIT' in key:
            key = 'tx_gaslimit'

        if 'TIMESTAMP' in key:
            if value > 1515978781:
                value = 1515978781
            key = 'tx_timestamp'

        if 'ADDRESS' in key:
            value = ((hex(value).ljust(40, '0')).rstrip('L')).lstrip('0x')
            key = 'contract_address'

        if 'ORIGIN' in key:
            value = ((hex(value).ljust(40, '0')).rstrip('L')).lstrip('0x')
            key = 'tx_origin'

        if 'BLOCKHASH' in key:
            key = 'tx_blockhash'

        if 'BALANCE' in key:
            if value > 10000:
                value = 10000
            key = 'contract_balance'

        if 'CALLER' in key:
            value = (hex(value).rstrip('L')).lstrip('0x').zfill(40)
            key = 'tx_caller'

        if not ('input' in key and not 'inputlength' in key):
            if not isinstance(value, str) and (not value == 0):
                value = hex(value).rstrip('L').lstrip('0x')

            if value == 0:
                value = '0'

        return key, value

    # Find the functions that need to be concretely executed
    def concrete_exe_set(self, pair_s0, pair_s1, pair_s2, func_stage0):
        remain_pair_executable = []
        pair_set2_0 = [var[0] for var in pair_s2]
        for var in pair_set2_0:
            if var in func_stage0:
                func_stage0.remove(var)
        pair_set0_0 = [var[0] for var in pair_s0]
        pair_set2_1 = [var[1] for var in pair_s2]
        iter_var = func_stage0
        for var in iter_var:
            if var in pair_set0_0 and var in pair_set2_1 and var:
                for elem0 in pair_s2:
                    if var == elem0[1]:
                        causal_pair = deepcopy(elem0)
                        if not causal_pair in MyGlobals.all_causal_pair and causal_pair not in remain_pair_executable:  # concrete exe may not run as expected, we do not give second chance for same causal pair
                            MyGlobals.all_causal_pair.append(deepcopy(causal_pair))
                            remain_pair_executable.append(
                                deepcopy(causal_pair))  # (f1,f2), means that f2 can be executed after f1
        return remain_pair_executable

    # List of pairs that should be tested on newer round
    def pair_list_renew(self, func, function_pairs_list, pair_s2, pair_s0, is_multi_dr):
        pair_list = []
        for pair in function_pairs_list:
            if (pair not in pair_s2) and func == pair[0] and (pair not in pair_list) and (
            not is_multi_dr):  # only retain pair that not in pair_s2 and func == pair[0]
                pair_list.append(pair)
            elif (pair not in pair_s2) and func == pair[1] and (pair not in pair_list) and is_multi_dr:
                pair_list.append(pair)

        return pair_list

    def concrete_execute(self, contract_address, ops, pair0, pair1, sol, storage_info_temp1):
        trace = {}
        tx_input = 'ffffffff'
        sol_val = sol[pair0]
        for j in range(len(sol_val)):
            if sol_val[j][0] == 'tx_input':
                trace['tx_input'] = sol_val[j][1]
                tx_input = sol_val[j][1]
            if sol_val[j][0] == 'tx_value':
                trace['tx_value'] = int(str(sol_val[j][1]), 16)
            if sol_val[j][0] == 'tx_caller':
                if len(sol_val[j][1]) != 40:
                    trace['tx_caller'] = self.owner[2:]
                else:
                    trace['tx_caller'] = sol_val[j][1]
            if sol_val[j][0] == 'tx_blocknumber':
                trace['tx_blocknumber'] = hex(int(str(sol_val[j][1]), 16))
            if sol_val[j][0] == 'tx_timestamp':
                trace['tx_timestamp'] = sol_val[j][1]
            if sol_val[j][0] == 'tx_blockhash':
                trace['tx_blockhash'] = sol_val[j][1]
        if 'tx_value' not in trace:
            trace['tx_value'] = '0'
        if 'tx_caller' not in trace:
            trace['tx_caller'] = '7' * 40
        if 'tx_blocknumber' not in trace:
            trace['tx_blocknumber'] = hex(8715204)
        if 'contract_address' not in trace:
            trace['contract_address'] = contract_address if contract_address[:2] == '0x' else '0x' + contract_address
        trace['storage'] = storage_info_temp1
        if not self.hb_valid:
            MyGlobals.trace_for_funcs[pair1].append(deepcopy(trace))
        trace = [trace]
        storage = {}
        code = ops
        debug = False
        read_from_blockchain = True
        st_blocknumber = MyGlobals.STORAGE_AT_BLOCK
        exe_result = check_one_trace(contract_address, trace, storage, code, debug, read_from_blockchain,
                                     st_blocknumber)
        return tx_input, exe_result, trace[0]

    # Update solution to record whether new race or dependence are found
    def solution_info_update(self, solution_dict, solution_dict_stage2, solution_dict_temp, solution_dict_stage2_temp,
                             solution_stage, solution_stage_temp):
        for pair in solution_dict_temp:
            if not pair in solution_dict:
                solution_dict[pair] = deepcopy(solution_dict_temp[pair])
        for pair in solution_dict_stage2_temp:
            solution_dict_stage2[pair] = deepcopy(solution_dict_stage2_temp[pair])
        for pair in solution_stage_temp:
            solution_stage[pair] = deepcopy(solution_stage_temp[pair])
        return

    # Initialization
    def initialize_global_param(self):
        MyGlobals.function_calls.clear()
        MyGlobals.datastructures.clear()

    # Calculate true read/write variables
    def cal_true_rw(self, r_or_w, rw, stack_record_temp, step_diff, unsettled_rw_addrs, r_or_w_dict):
        if not r_or_w_dict:
            for j in list(rw):
                r_or_w_dict[j] = set()
        if r_or_w == 'SLOAD':
            for j in list(rw):
                for k in range(len(stack_record_temp)):
                    elem = stack_record_temp[k]
                    if elem[1] == 'SLOAD' and j == elem[2]:
                        if k == len(stack_record_temp) - 1:
                            unsettled_rw_addrs.add(elem[2])
                            break
                        if stack_record_temp[k + 1][1] == 'AND' and abs(
                                stack_record_temp[k + 1][0] - stack_record_temp[k][0]) < step_diff:
                            r_or_w_dict[j].add(stack_record_temp[k + 1][2])
                        else:
                            unsettled_rw_addrs.add(elem[2])
                            break
        else:
            for j in list(rw):
                for k in range(len(stack_record_temp)):
                    elem = stack_record_temp[k]
                    if elem[1] == 'SSTORE' and j == elem[2]:
                        if k < 1:
                            unsettled_rw_addrs.add(elem[2])
                            break
                        if stack_record_temp[k - 1][1] == 'AND' and abs(
                                stack_record_temp[k - 1][0] - stack_record_temp[k][0]) < step_diff:
                            r_or_w_dict[j].add(stack_record_temp[k - 1][2])
                        else:
                            unsettled_rw_addrs.add(elem[2])
                            break
        return unsettled_rw_addrs, r_or_w_dict

    # Calculate r/w for f1,f2 and f2,f1
    def rw_for_each(self, str0, str1, rw, stack_record_temp10, stack_record_temp11, stack_record_temp20,
                    stack_record_temp21):
        unsettled_f1 = set()
        f1_dict = {}
        unsettled_f1, f1_dict = self.cal_true_rw(str0, rw, stack_record_temp10, 1000, unsettled_f1, f1_dict)
        unsettled_f1, f1_dict = self.cal_true_rw(str0, rw, stack_record_temp11, 1000, unsettled_f1, f1_dict)
        unsettled_f2 = set()
        f2_dict = {}
        unsettled_f2, f2_dict = self.cal_true_rw(str1, rw, stack_record_temp20, 1000, unsettled_f2, f2_dict)
        unsettled_f2, f2_dict = self.cal_true_rw(str1, rw, stack_record_temp21, 1000, unsettled_f2, f2_dict)
        return unsettled_f1, unsettled_f2, f1_dict, f2_dict

    # Add function pairs that contain the same function
    def add_duplicate_pair(self, impFunctionList, function_pairs_list, is_duplicate):
        if is_duplicate:
            if not impFunctionList:
                impFunctionList.extend(MyGlobals.impfuncs)
            for var in impFunctionList:
                pair = (var, var)
                if not pair in function_pairs_list:
                    function_pairs_list.append(pair)

    def generate_candidate_deps(self, candidate_former_funcs, candidate_latter_funcs, rw_pairs):
        pair_list = []
        for func in candidate_former_funcs:
            for func_non in candidate_latter_funcs:
                pair = (func, func_non)
                if pair in rw_pairs:
                    pair_list.append(pair)
        return pair_list

    def add_possible_bd_pair(self, impFunctionList, function_pairs_list, func_hash2abi):
        for func in impFunctionList:
            if func in func_hash2abi and "'payable': True" in str(func_hash2abi[func]):
                for func2 in MyGlobals.funcs_involve_call:
                    if not (func, func2) in function_pairs_list:
                        function_pairs_list.append((func, func2))
    def race_test(self,pair_list, storage_info, path_set_pairs0, path_set_pairs1, terminate_stage):

        MyGlobals.terminate_stage=terminate_stage
        solution_dict = {}
        solution_dict_stage2 = {}
        solution_stage = {}
        func_hash = {}
        data_race_set = []
        inst_pair_race_total=[]
        for f in self._funclist:
            func_hash[f[1]] = f[0]
        num = 0
        for i_th,pair in enumerate(pair_list):
            MyGlobals.storage_temp = deepcopy(storage_info[i_th])

            if terminate_stage==3:
                MyGlobals.dep_activated = True
                MyGlobals.m.activated_paths.clear()
                l_inf=len(MyGlobals.m.infeasible_paths)
                MyGlobals.solution_dict_stage2[pair] = []
                self.cal_feasible_jumpis(path_set_pairs0[i_th],path_set_pairs1[i_th],terminate_stage,None,None)
                p_to_be_activated=list(path_set_pairs1[i_th])[0]
            elif terminate_stage==5:
                MyGlobals.dep_activated = False
                self.cal_feasible_jumpis(path_set_pairs0[i_th],path_set_pairs1[i_th],terminate_stage,pair[0],pair[1])
            else:
                MyGlobals.dep_activated = False
            MyGlobals.reach_stage = 0

            num += 1
            MyGlobals.addr_read = []
            MyGlobals.addr_write = []
            MyGlobals.stage2_actived = True
            MyGlobals.j_c = []
            MyGlobals.mul_dr_suspend = False

            MyGlobals.call_vars = []
            MyGlobals.bals_1 = {}
            MyGlobals.bals_2 = {}
            MyGlobals.pair = pair
            MyGlobals.Time_checkpoint = datetime.datetime.now()
            MyGlobals.num_solver_calls = 0
            MyGlobals.total_time_solver = 0
            MyGlobals.solver_configurations.clear()
            MyGlobals.MAX_VISITED_NODES = 750

            MyGlobals.w_overall = []
            MyGlobals.path = [0, 0, 0, 0]
            MyGlobals.paths = [0]
            MyGlobals.m.rs_temp.clear()
            MyGlobals.m.ws_temp.clear()
            MyGlobals.m.rs_added.clear()
            MyGlobals.m.ws_added.clear()  # added during dep check

            MyGlobals.m.rs_temp_id.clear()
            MyGlobals.m.ws_temp_id.clear()
            MyGlobals.m.rs_added_id.clear()
            MyGlobals.m.ws_added_id.clear()  # added during dep check
            MyGlobals.m.sha_v2slot.clear()
            MyGlobals.m.rwaddr2id.clear()
            MyGlobals.m.inst_pair=()
            MyGlobals.m.inst_pairs.clear()
            solution = self.check_one_function_on_execute(pair[0], pair[1],
                                                          func_hash[pair[0]] if pair[0] in func_hash else pair[0],
                                                          func_hash[pair[1]] if pair[1] in func_hash else pair[1])
            if terminate_stage==3:#process dep pair
                self.hb_valid=True
                if MyGlobals.solution_dict_stage2:
                    if p_to_be_activated in MyGlobals.m.infeasible_paths:
                        MyGlobals.m.infeasible_paths.remove(p_to_be_activated)
                    self.update_m(MyGlobals.solution_dict_stage2[pair],pair)
                    MyGlobals.solution_dict_stage2={}
            sd=[]
            bd=[]
            for elem in MyGlobals.dr_bug_sd:
                func_pair_temp=(elem[0],elem[1])
                sd.append(func_pair_temp)
            for elem in MyGlobals.dr_bug_bd:
                func_pair_temp=(elem[0],elem[1])
                bd.append(func_pair_temp)
            inst_pair_race=[]
            if solution:
                if pair in bd:
                    data_race_set.append(pair)
                    inst_pair_race.append(MyGlobals.m.inst_pairs)
                elif pair in MyGlobals.solution_dict:
                    solution_dict[(pair[0], pair[1])] = solution
                    p0 = pair[0]
                    p1 = pair[1]
                    if p0 == p1:
                        p1 = p0 + '-2'

                    solution_temp = deepcopy(solution)
                    l = len(solution.keys())
                    for sol_num in range(1, l + 1):
                        is_tp = False

                        storage_temp_backup = deepcopy(MyGlobals.storage_temp)
                        self.hb_valid = True
                        MyGlobals.newpair = True
                        MyGlobals.balance_f = {}
                        sol = solution_temp[sol_num]
                        MyGlobals.sol = sol
                        MyGlobals.concrete_read = set()
                        MyGlobals.concrete_write = set()
                        res00, res10, trace_ = self.concrete_execute(self._contract_address, self._ops, p0, pair[1],
                                                                     sol, MyGlobals.storage_temp)
                        f1_0_r = deepcopy(MyGlobals.concrete_read)
                        f1_0_w = deepcopy(MyGlobals.concrete_write)
                        MyGlobals.concrete_read = set()
                        MyGlobals.concrete_write = set()
                        stack_record_temp10 = deepcopy(MyGlobals.stack_record)
                        MyGlobals.stack_record.clear()

                        res00, res20, trace_ = self.concrete_execute(self._contract_address, self._ops, p1, pair[1],
                                                                     sol, MyGlobals.storage_temp)
                        f2_0_r = deepcopy(MyGlobals.concrete_read)
                        f2_0_w = deepcopy(MyGlobals.concrete_write)
                        MyGlobals.concrete_read = set()
                        MyGlobals.concrete_write = set()
                        storage_change_0 = deepcopy(MyGlobals.storage_temp)
                        balance_change_0 = deepcopy(MyGlobals.balance_f)
                        stack_record_temp20 = deepcopy(MyGlobals.stack_record);
                        MyGlobals.stack_record.clear()

                        MyGlobals.storage_temp = deepcopy(storage_temp_backup);
                        MyGlobals.balance_f = {};
                        MyGlobals.newpair = True
                        res00, res21, trace_ = self.concrete_execute(self._contract_address, self._ops, p1, pair[1],
                                                                     sol, MyGlobals.storage_temp)
                        f2_1_r = deepcopy(MyGlobals.concrete_read);
                        f2_1_w = deepcopy(MyGlobals.concrete_write)
                        MyGlobals.concrete_read = set();
                        MyGlobals.concrete_write = set()
                        stack_record_temp21 = deepcopy(MyGlobals.stack_record);
                        MyGlobals.stack_record.clear()

                        res00, res11, trace_ = self.concrete_execute(self._contract_address, self._ops, p0, pair[1],
                                                                     sol, MyGlobals.storage_temp)
                        f1_1_r = deepcopy(MyGlobals.concrete_read);
                        f1_1_w = deepcopy(MyGlobals.concrete_write)
                        MyGlobals.concrete_read = set();
                        MyGlobals.concrete_write = set()
                        stack_record_temp11 = deepcopy(MyGlobals.stack_record);
                        MyGlobals.stack_record.clear()

                        storage_change_1 = deepcopy(MyGlobals.storage_temp)
                        balance_change_1 = deepcopy(MyGlobals.balance_f)
                        f1_r = f1_0_r | f1_1_r;
                        f1_w = f1_0_w | f1_1_w
                        f2_r = f2_0_r | f2_1_r;
                        f2_w = f2_0_w | f2_1_w
                        st_keys = set(storage_change_0.keys()) | set(storage_change_1.keys())
                        st_keys = list(st_keys)

                        for key in st_keys:
                            if not key in storage_change_0:

                                value_int=0
                                if int(key) in MyGlobals.initial_storage:
                                    value_int = MyGlobals.initial_storage[int(key)]
                                storage_change_0[key] = value_int
                            if not key in storage_change_1:

                                value_int=0
                                if int(key) in MyGlobals.initial_storage:
                                    value_int=MyGlobals.initial_storage[int(key)]

                                storage_change_1[key] = value_int
                        unsettled_rw_addrs = set()
                        if (f1_r & f2_w or f1_w & f2_r or f1_w & f2_w) and (res10 & res20 & res21 & res11):

                            if pair in sd:
                                if storage_change_0 == storage_change_1:
                                    if MyGlobals.dr_bug_sd and (MyGlobals.dr_bug_sd[-1][0], MyGlobals.dr_bug_sd[-1][1]) == pair:
                                        MyGlobals.dr_bug_sd.pop(-1)
                            if pair in bd:
                                if balance_change_0 == balance_change_1:
                                    if MyGlobals.dr_bug_bd and (MyGlobals.dr_bug_bd[-1][0], MyGlobals.dr_bug_bd[-1][1]) == pair:
                                        MyGlobals.dr_bug_bd.pop(-1)
                            for jj in list(((f1_r & f2_w) | (f1_w & f2_r) | (f1_w & f2_w))):
                                if jj > 30:
                                    is_tp = True
                                    if not pair in data_race_set:
                                        data_race_set.append(pair)
                                        if sol_num<=len(MyGlobals.m.inst_pairs):
                                            inst_pair_race.append(MyGlobals.m.inst_pairs[sol_num-1])
                                        else:
                                            inst_pair_race.append((0,0))
                                    break
                            # if not (pair in data_race_set):
                            if pair in sd or pair in bd:
                                is_tp = True
                                if pair not in data_race_set:
                                    data_race_set.append(pair)
                                    if sol_num <= len(MyGlobals.m.inst_pairs):
                                        inst_pair_race.append(MyGlobals.m.inst_pairs[sol_num-1])
                                    else:
                                        inst_pair_race.append((0,0))
                            if f1_r & f2_w:
                                rw = f1_r & f2_w
                                unsettled_r_addrs, unsettled_w_addrs, r_dict, w_dict = self.rw_for_each('SLOAD',
                                                                                                        'SSTORE', rw,
                                                                                                        stack_record_temp10,
                                                                                                        stack_record_temp11,
                                                                                                        stack_record_temp20,
                                                                                                        stack_record_temp21)
                            elif f1_w & f2_r:
                                rw = f1_w & f2_r
                                unsettled_r_addrs, unsettled_w_addrs, r_dict, w_dict = self.rw_for_each('SSTORE',
                                                                                                        'SLOAD', rw,
                                                                                                        stack_record_temp10,
                                                                                                        stack_record_temp11,
                                                                                                        stack_record_temp20,
                                                                                                        stack_record_temp21)
                            elif f1_w & f2_w:
                                rw = f1_w & f2_r
                                unsettled_r_addrs, unsettled_w_addrs, r_dict, w_dict = self.rw_for_each('SSTORE',
                                                                                                        'SSTORE', rw,
                                                                                                        stack_record_temp10,
                                                                                                        stack_record_temp11,
                                                                                                        stack_record_temp20,
                                                                                                        stack_record_temp21)
                            if unsettled_r_addrs | unsettled_w_addrs:
                                is_tp = True
                                if pair not in data_race_set:
                                    data_race_set.append(pair)
                                    if sol_num <= len(MyGlobals.m.inst_pairs):
                                        inst_pair_race.append(MyGlobals.m.inst_pairs[sol_num-1])
                                    else:
                                        inst_pair_race.append((0,0))
                            else:
                                for j in list(rw):
                                    if j in r_dict and j in w_dict:
                                        if r_dict[j] & w_dict[j]:
                                            is_tp = True
                                            if pair not in data_race_set:
                                                data_race_set.append(pair)
                                                if sol_num <= len(MyGlobals.m.inst_pairs):
                                                    inst_pair_race.append(MyGlobals.m.inst_pairs[sol_num-1])
                                                else:
                                                    inst_pair_race.append((0,0))
                        if not is_tp:
                            solution.pop(sol_num)

                        MyGlobals.storage_temp = deepcopy(storage_temp_backup)
                        self.hb_valid = False;
                        MyGlobals.sol = {}
                        print('data_race_set_for_now:', data_race_set)
                    if not pair in data_race_set:
                        if pair in sd:
                            if MyGlobals.dr_bug_sd and (MyGlobals.dr_bug_sd[-1][0],MyGlobals.dr_bug_sd[-1][1])==pair:
                                MyGlobals.dr_bug_sd.pop(-1)

                else:
                    solution_dict_stage2[(pair[0], pair[1])] = solution

            if terminate_stage == 5 and solution:
                inst_pair_race_total.append(inst_pair_race)
            t2 = datetime.datetime.now()
            sys.stdout.flush()
            if MyGlobals.ONE_CONTRACT_TIMEOUT < int((t2 - MyGlobals.Time_checkpoint_HB).total_seconds()):
                print('\n', '\033[91m-------Finding the DR relations timed out\033[0m', '\n')
                break
        MyGlobals.m.inst_pairs = inst_pair_race_total
        return solution_dict, data_race_set

    def begin_iteration(self):
        self.check_bc_size()

        impFunctionList = MyGlobals.functions
        if len(impFunctionList) > 40:
            MyGlobals.large_contract = True
        elif len(impFunctionList) < 1:
            MyGlobals.too_short_contract = True
            return [], {}


        initial_storage = MyGlobals.initial_storage
        storage_info = initial_storage
        duplicate_pairs=[]
        states=[]
        for func in impFunctionList:
            duplicate_pairs.append((func[1],func[1]))
            states.append(storage_info)
            MyGlobals.m.triggered_rs[func[1]]=set()
            MyGlobals.m.triggered_ws[func[1]] = set()

            MyGlobals.m.triggered_rs_id[func[1]]=set()
            MyGlobals.m.triggered_ws_id[func[1]] = set()
        t_start_static=datetime.datetime.now()
        self.race_test(duplicate_pairs, states, [], [], 2)
        t_end_static = datetime.datetime.now()
        MyGlobals.t_record.append((t_end_static-t_start_static).total_seconds())
        for p_hash in MyGlobals.m.hash2path:
            MyGlobals.m.bestfit[p_hash]=[]
            MyGlobals.m.bestfit_state[p_hash]=initial_storage

        max_seq_length=4
        terminate=False
        t_start_dep = datetime.datetime.now()
        for nested_round in range(3):  # nest dep round
            if self.check_timeout(30*60):
                break
            for p_hash in MyGlobals.m.infeasible_paths:
                MyGlobals.m.bestfit[p_hash] = []
                MyGlobals.m.bestfit_state[p_hash] = initial_storage
            feasible_paths_valid=deepcopy(MyGlobals.m.feasible_paths_valid)
            for dep_search_round in range(max_seq_length):
                if nested_round > 0 and dep_search_round == 0:
                    candidate_path0_hash = deepcopy(list(MyGlobals.m.activated_paths_nested))
                    MyGlobals.activated_paths_nested=set()
                    for p_hash in MyGlobals.m.infeasible_paths:
                        MyGlobals.m.bestfit[p_hash]=[]
                        MyGlobals.m.bestfit_state[p_hash] = initial_storage
                else:
                    candidate_path0_hash = feasible_paths_valid
                if dep_search_round == 0:
                    candidate_path1_hash = deepcopy(MyGlobals.m.infeasible_paths)
                else:
                    candidate_path1_hash = deepcopy(MyGlobals.m.activated_paths_fd)
                    MyGlobals.m.activated_paths_fd=set()

                func_pairs, storage_list, path_set_pairs0,path_set_pairs1 = self.extract_input_for_dep_test(candidate_path0_hash,candidate_path1_hash, nested_round)
                if not func_pairs:
                    terminate=True
                    break

                self.race_test(func_pairs, storage_list, path_set_pairs0, path_set_pairs1, 3)
            if terminate and dep_search_round==0:
                break
            else:
                terminate=False
        t_end_dep = datetime.datetime.now()
        MyGlobals.t_record.append((t_end_dep - t_start_dep).total_seconds())

        t_start_rd = datetime.datetime.now()
        MyGlobals.terminate_stage = 5
        storage_list=[]
        func_pairs=[]
        path_set_pairs0=[]
        path_set_pairs1=[]
        feasible_valid_list=list(MyGlobals.m.feasible_paths_valid)
        p2f=MyGlobals.m.path_hash2func_hash
        for i_th,path0 in enumerate(feasible_valid_list):
            for j_th, path1 in enumerate(feasible_valid_list):
                if i_th>j_th:
                    continue
                f0=p2f[path0]
                f1=p2f[path1]
                func_pairs.append((f0,f1))
                path_set_pairs0.append({path0})
                path_set_pairs1.append({path1})
                storage_temp0=MyGlobals.m.bestfit_state[path0]
                storage_temp1=MyGlobals.m.bestfit_state[path1]

                if i_th==j_th:
                    storage_list.append(storage_temp0)
                else:
                    if storage_temp0==deepcopy(initial_storage):
                        storage_temp=storage_temp1
                        storage_list.append(storage_temp)
                    elif storage_temp1==deepcopy(initial_storage):
                        storage_temp = storage_temp0
                        storage_list.append(storage_temp)
                    else:
                        storage_list.append(storage_temp0)

        func_pairs,storage_list,path_set_pairs0,path_set_pairs1=self.gather_same_state(func_pairs, storage_list, path_set_pairs0,path_set_pairs1)
        solution_dict, data_race_set=self.race_test(func_pairs, storage_list, path_set_pairs0, path_set_pairs1, 5)
        t_end_rd = datetime.datetime.now()
        MyGlobals.t_record.append((t_end_rd - t_start_rd).total_seconds())

        return data_race_set,solution_dict

    # Refine solution
    def qualified_as_func_cd(self, function1, function2, key, cd):
        if function1 == function2:
            str2 = '-' + str(cd) + '-'
            if str2 in key:
                return True
        elif cd == 1:
            return function1 in key
        elif cd == 2:
            return function2 in key
        else:
            return 'wrong cd'

    # Responsible for checking data race for one function pair
    def check_one_function_on_execute(self, function1, function2, fn1, fn2):

        # The compiled code should have STOP or RETURN instructions.
        ops = parse_code(self._contract_bytecode, self._debug)
        if not code_has_instruction(ops, ['STOP', 'RETURN']):
            print('\033[91m[-] The code does not have STOP or RETURN\033[0m')
            return False
        if self._debug: print_code(self._contract_bytecode, ops)

        if MyGlobals.terminate_stage==2:
            print(
                '\n \033[95m[ ] Callable function identifying and static analyzing for function  %s :   %s  \033[0m' % (fn1, function1))
        elif MyGlobals.terminate_stage == 3:
            print(
                '\n \033[95m[ ] Finding deps for the pair  %s ,  %s :   %s , %s  \033[0m' % (fn1, fn2, function1, function2))
        else:
            print(
                '\n \033[95m[ ] Finding races for the pair  %s ,  %s :   %s , %s  \033[0m' % (fn1, fn2, function1, function2))
        # Set the given event field to be symbolic
        MyGlobals.symbolic_vars = ['CALLVALUE', 'NUMBER', 'GASLIMIT', 'ORIGIN', 'BLOCKHASH',
                                   'CALLER','TIMESTAMP']
        MyGlobals.solution_found = False
        MyGlobals.search_condition_found = False
        MyGlobals.stop_search = False

        evmInstance = EVM(1, MyGlobals.max_jumpdepth_in_normal_search, False, self._contract_address, function1,
                          function2, False, self._debug, self._read_from_blockchain)
        evmInstance.run_one_check(ops, 1, 0)

        soldict = {}
        solution_dict_stage2=[]
        # Get the concrete values of event fields if static analysis finds wHB relation for an event pair.
        if (function1, function2) in MyGlobals.solution_dict:

            print('\033[92m[+] Solution found \033[0m \n')
            i = 0

            for lists in MyGlobals.solution_dict[(function1, function2)]:
                i += 1
                mydict = {}

                for key, value in lists.items():
                    convert = True
                    if 'input' in key:
                        if 'inputlength' in key or not 'input-' in key:
                            convert = False

                    if convert:
                        if self.qualified_as_func_cd(function1, function2, key, 1):  # my modify
                            if function1 in key:
                                if not function1 in mydict:
                                    mydict[function1] = []
                                    key, value = self.changeContext(key, value)
                                    mydict[function1].append((key, value))

                                else:
                                    key, value = self.changeContext(key, value)
                                    mydict[function1].append((key, value))
                        if self.qualified_as_func_cd(function1, function2, key, 2):
                            if function2 in key:
                                function2_rename = function2
                                if function1 == function2:
                                    function2_rename = function2 + '-2'
                                if not function2_rename in mydict:
                                    mydict[function2_rename] = []
                                    key, value = self.changeContext(key, value)
                                    mydict[function2_rename].append((key, value))
                                else:
                                    key, value = self.changeContext(key, value)
                                    mydict[function2_rename].append((key, value))

                soldict[i] = mydict

            print_solution(function1, function2, fn1, fn2, soldict)
        elif (function1, function2) in MyGlobals.solution_dict_stage2 and not function1 == function2:
            i = 0

            for lists in MyGlobals.solution_dict_stage2[(function1, function2)]:
                i += 1
                mydict = {}
                for key, value in lists.items():
                    convert = True
                    if 'input' in key:
                        if 'inputlength' in key or not 'input-' in key:
                            convert = False

                    if convert:
                        if function1 in key:
                            if not function1 in mydict:
                                mydict[function1] = []
                                key, value = self.changeContext(key, value)
                                mydict[function1].append((key, value))

                            else:
                                key, value = self.changeContext(key, value)
                                mydict[function1].append((key, value))

                        if function2 in key:
                            if not function2 in mydict:
                                mydict[function2] = []
                                key, value = self.changeContext(key, value)
                                mydict[function2].append((key, value))

                            else:
                                key, value = self.changeContext(key, value)
                                mydict[function2].append((key, value))

                soldict[i] = mydict
                solution_dict_stage2.append(mydict)
            MyGlobals.solution_dict_stage2[(function1, function2)]=solution_dict_stage2
        else:
            print('\033[91m[-] No DR found for %s , %s  : %s , %s\033[0m ' % (fn1, fn2, function1, function2))

        if MyGlobals.stop_search or soldict:
            return soldict

        return {}

    def check_bc_size(self):
        if len(self._contract_bytecode) <= 2:
            print('Contract bytecode is too short:\n\tlen:%d\n\tbytecode:%s' % (
                len(self._contract_bytecode), self._contract_bytecode))
            return [], {}

    def check_timeout(self,limit):
        t2 = datetime.datetime.now()
        if limit < int((t2 - MyGlobals.Time_checkpoint_HB).total_seconds()):
            return True
    def add_may_feasible_paths(self,p_hash_set,p0):
        for p_hash in MyGlobals.m.may_feasible_paths:
            if MyGlobals.m.path_hash2func_hash[p_hash]==p0:
                p_hash_set.add(p_hash)
    def gather_same_state(self, func_pairs, storage_list, path_set_pairs0,path_set_pairs1):
        state_hashs = []
        func_pairs_temp = []
        storage_list_temp=[]
        path_set_pairs0_temp=[]
        path_set_pairs1_temp=[]
        for i,pair in enumerate(func_pairs):
            storage = storage_list[i]
            state_hash = self.get_state_hash(storage)
            if not pair in func_pairs_temp:
                func_pairs_temp.append(pair)
                storage_list_temp.append(storage)
                state_hashs.append(state_hash)
                path_set_pairs0_temp.append(path_set_pairs0[i])
                path_set_pairs1_temp.append(path_set_pairs1[i])
            else:
                if state_hash in state_hashs:
                    ind=state_hashs.index(state_hash)
                    path_set_pairs0_temp[ind].update(path_set_pairs0[ind])
                    path_set_pairs1_temp[ind].update(path_set_pairs1[ind])
                else:
                    func_pairs_temp.append(pair)
                    storage_list_temp.append(storage)
                    state_hashs.append(state_hash)
                    path_set_pairs0_temp.append(path_set_pairs0[i])
                    path_set_pairs1_temp.append(path_set_pairs1[i])

        for ind,pair in enumerate(func_pairs_temp):

            self.add_may_feasible_paths(path_set_pairs0_temp[ind],pair[0])
            self.add_may_feasible_paths(path_set_pairs1_temp[ind],pair[1])
        return  func_pairs_temp,storage_list_temp,path_set_pairs0_temp,path_set_pairs1_temp

    def rw_check(self,path0_hash,path1_hash):
        if path0_hash in MyGlobals.m.ws and path1_hash in MyGlobals.m.rs:
            shared_rw=MyGlobals.m.ws[path0_hash] & MyGlobals.m.rs[path1_hash]
        if shared_rw:
            return True
        else:
            return False
    def extract_input_for_dep_test(self, candidate_path0_hash,
                                   candidate_path1_hash, nested_round):
        path_pairs0=[]
        path_pairs1=[]
        storage_list=[]
        func_pairs=[]
        for path0_hash in candidate_path0_hash:
            for path1_hash in candidate_path1_hash:
                rw = self.rw_check(path0_hash, path1_hash )
                func1 = MyGlobals.m.path_hash2func_hash[path0_hash]
                func2 = MyGlobals.m.path_hash2func_hash[path1_hash]
                if rw and not func1==func2:
                    if nested_round==0:
                        MyGlobals.m.bestfit[path1_hash]=deepcopy(MyGlobals.m.bestfit[path0_hash])
                        storage_temp = MyGlobals.m.bestfit_state[path1_hash]
                    else:
                        storage_temp = MyGlobals.m.bestfit_state[path0_hash]
                    func_pairs.append((func1, func2))
                    storage_list.append(storage_temp)

                    path_pairs0.append({path0_hash})
                    path_pairs1.append({path1_hash})
        return func_pairs, storage_list, path_pairs0, path_pairs1

    def init_feasible_jumpdest(self):
        for i in range(1,5):
            MyGlobals.feasible_jumpdest[1]={}
    def cal_feasible_jumpis(self,path_set_pair0,path_set_pair1,terminate_stage,func1=None,func2=None):
        self.init_feasible_jumpdest()

        if terminate_stage==3:
            key2dest0 = self.get_key2dest(path_set_pair0)
            MyGlobals.feasible_jumpdest[1]=key2dest0
            MyGlobals.feasible_jumpdest[2]=MyGlobals.m.hash2path_list[list(path_set_pair1)[0]]
        else:
            key2dest0 = self.get_key2dest(path_set_pair0)
            key2dest1 = self.get_key2dest(path_set_pair1)
            MyGlobals.feasible_jumpdest[1] = key2dest0
            MyGlobals.feasible_jumpdest[3] = key2dest1

            key2dest2= self.get_key2dest(path_set_pair1,func1)
            key2dest3 = self.get_key2dest(path_set_pair1, func2)
            MyGlobals.feasible_jumpdest[4] = key2dest2
            MyGlobals.feasible_jumpdest[2] = key2dest3

    def get_key2dest(self, path_hashs, func=None):
        key2dest = {}
        keys = set()
        hash2path=MyGlobals.m.hash2path
        if func:
            path_hashs=set()
            for p_hash,p in hash2path.items():
                if MyGlobals.m.path_hash2func_hash[p_hash]==func:
                    keys = keys | set(p.keys())
                    path_hashs.add(p_hash)
        else:
            for p_hash in path_hashs:
                p = hash2path[p_hash]
                keys = keys | set(p.keys())

        for key in keys:
            key2dest[key] = set()
            for p_hash in path_hashs:
                p = hash2path[p_hash]
                if key in p:
                    key2dest[key] = key2dest[key] | {p[key]}
        return key2dest


    def key2dest_for_static_filter(self,hash2path,unique_path_hash):
        key2dest = {}
        keys = set()
        for p_hash in unique_path_hash:
            p = hash2path[p_hash]
            keys = keys | set(p.keys())

        for key in keys:
            key2dest[key] = set()
            for p_hash in unique_path_hash:
                p = hash2path[p_hash]
                if key in p:
                    key2dest[key] = key2dest[key] | set(p[key])
        return key2dest

    def is_rw(self,p0,p1,sorted_r_addrs,sorted_w_addrs):
        if sorted_r_addrs[p1] & sorted_w_addrs[p0]:
            return True
        else:
            return False
    def get_state_hash(self,state:dict):
        str0=''
        ks=list(state.keys())
        ks.sort()
        for k in ks:
            v=state[k]
            str0+=str(k)
            str0 += str(v)
        state_hash = hash(str0)
        return state_hash


    def update_m(self, sols, pair):
        if sols:

            storage_temp_back_up = deepcopy(MyGlobals.storage_temp)
            for i_th,sol in enumerate(sols):
                MyGlobals.storage_temp = deepcopy(storage_temp_back_up)
                p_hash=MyGlobals.m.activated_paths[i_th][0]
                if not p_hash in MyGlobals.m.bestfit:
                    MyGlobals.m.bestfit[p_hash]=[]
                    MyGlobals.m.bestfit_state[p_hash]=MyGlobals.initial_storage
                is_feasible=MyGlobals.m.activated_paths[i_th][1]
                input, res, exe_trace = self.concrete_execute(self._contract_address, self._ops, pair[0], pair[1], sol,
                                                              MyGlobals.storage_temp)

                if is_feasible:

                    MyGlobals.m.activated_paths_nested.add(p_hash)
                    MyGlobals.m.bestfit[p_hash].append((input, res, exe_trace))
                    MyGlobals.m.bestfit_state[p_hash] = deepcopy(MyGlobals.storage_temp)
                else:
                    MyGlobals.m.activated_paths_fd.add(p_hash)
                    MyGlobals.m.bestfit[p_hash].append((input, res, exe_trace))
                    MyGlobals.m.bestfit_state[p_hash]=deepcopy(MyGlobals.storage_temp)
