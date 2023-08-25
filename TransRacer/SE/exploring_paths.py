from __future__ import print_function
import sys
import re
from execute_instruction import *
from execute_inst_shadow_se import EVMCore_stack2
from global_vars import get_storage_value,get_params, initialize_params, print_params
from global_vars import MyGlobals, clear_globals, update_global_datastructures
from misc import *
import random
from random import shuffle
import datetime
import z3
from z3 import *
from web3 import Web3
from copy import deepcopy


class EVM(EVMCore):
    '''
	* This class is responsible for explore pathes and collect constraints
	'''

    def __init__(self, max_call_depth, max_jump_depth, search_enhance, contract_address, function1, function2, se_for_single_func,
                 debug, read_from_blockchain):
        self.max_call_depth = max_call_depth
        self.max_jump_depth = max_jump_depth
        self.search_enhance = search_enhance
        self.contract_address = contract_address
        self.function1 = function1
        self.function2 = function2
        self.se_for_single_func=se_for_single_func
        self.debug = debug
        self.read_from_blockchain = read_from_blockchain
        self.pc=0
        self.path=[]
        self.allowed_cycle=2
        self.s_except_last_eq=Solver()
        self.last_eq=None
        self.pos_last_jumpi=0
        self.triggered_length=0
        self.pos_last_jumpi_other_dir=None
        self.impinsts=[]
    def function_accept(self, op, stack, trace, debug):
        op_name = op['o']
        op_val = op['input']
        return True, False

    def function_throw(self, op, stack, trace, debug):
        op_name = op['o']
        op_val = op['input']

        if 'JUMP' in op_name:

            if self.is_fixed(stack[-1]):

                if self.get_value(stack[-1]) == 0:
                    return True, False

                else:
                    return False, False

            else:
                return False, False

        return True, False

    def function_sstore(self, op, stack, trace, debug):
        op_name = op['o']
        op_val = op['input']
        return True, True


    def new_state(self, stack, storage, sha3_dict, sha3_values, mmemory, trace, data):
        datastructures = {}
        datastructures['stack'] = copy.deepcopy(stack)
        datastructures['storage'] = copy.deepcopy(storage)
        datastructures['sha3_dict'] = copy.deepcopy(sha3_dict)
        datastructures['data'] = copy.deepcopy(data)
        datastructures['sha3_values'] = copy.deepcopy(sha3_values)
        return datastructures

    def key_inst(self,no_imp_ops):
        found=False
        ids=[]
        inst2id={'CALL':'f1','JUMPI':'57','DELEGATECALL':'f4','SELFDESTRUCT':'ff'}
        for elem in self.impinsts:
            for op in no_imp_ops:
                if not elem.find(inst2id[op])>0:
                    found=True
                    ids.append(elem[:-2])
        return found, ids

    def concretize(self,stack,memory,sym_var,v):
        for st in stack:
            if 'z3' in st:
                st['z3'] = simplify(substitute(st['z3'], (BitVec(sym_var, 256), BitVecVal(v,256))))
        for st in memory:
            if 'z3' in memory[st]:
                memory[st]['z3'] = simplify(
                    substitute(memory[st]['z3'], (BitVec(sym_var, 256), BitVecVal(v,256))))

    def is_deeper(self, key,ind):
        num=0
        for elem in self.path:
            if elem[0]==key:
                num += 1
        if num>MyGlobals.m.max_jump_num[ind]:
            MyGlobals.m.max_jump_num[MyGlobals.ind[1]] = num
            return True,num
        return False,0

    def path2dict(self,key,k,v):
        p_dict={}
        p_list=[]
        for tup in self.path :
            if len(tup)==3 and tup[0]==key:
                p_dict[tup[1]]=tup[2]
                p_list.append(tup[1])
                p_list.append(tup[2])
        if key==3:
            p_dict[k]=v
        return p_dict,p_list
    def rw_back_up(self):
        rs_temp = deepcopy(MyGlobals.m.rs_temp)
        ws_temp = deepcopy(MyGlobals.m.ws_temp)
        rs_temp_id = deepcopy(MyGlobals.m.rs_temp_id)
        ws_temp_id = deepcopy(MyGlobals.m.ws_temp_id)
        rwaddr2id=deepcopy(MyGlobals.m.rwaddr2id)
        return rs_temp,ws_temp,rs_temp_id,ws_temp_id,rwaddr2id


    def to_other_direction(self,path,path_dict=None,last_jump_start=None):
        if not last_jump_start:
            last_jump_start=path[-2]
        if not path_dict:
            path_dict={}

        if self.pos_last_jumpi_other_dir:
            jump_end=self.pos_last_jumpi_other_dir
            p_temp = deepcopy(path)
            p_temp[-1] = jump_end
            h_temp = hash(str(p_temp))
            path_dict[last_jump_start]=jump_end

            return True,p_temp,h_temp,path_dict
        else:
            return False, {}, 0
    '''
		Finding DR between function1, function2 in two phases:
        1. SE for function1
        2. SE for function2
        3. SE for function2
        4. SE for function1
	'''

    def run_one_check(self, ops, key, datastructures={}):

        # Stop the search once it exceeds timeout
        time_now = datetime.datetime.now()

        if MyGlobals.ONE_PAIR_TIMEOUT < int((time_now - MyGlobals.Time_checkpoint).total_seconds()):
            MyGlobals.stop_search = True
            return

        MyGlobals.MAX_JUMP_DEPTH = self.max_jump_depth
        MyGlobals.MAX_CALL_DEPTH = self.max_call_depth
        configurations = {}
        '''

		** Phase 1

		'''
        if 1 == key:
            set_balances_bd([],self.contract_address,1)
            MyGlobals.current_key = (1, 0)
            addr_read_backup=deepcopy(MyGlobals.addr_read)
            addr_write_backup=deepcopy(MyGlobals.addr_write)
            MyGlobals.addr_read.append(MyGlobals.current_key)
            MyGlobals.addr_write.append(MyGlobals.current_key)
            MyGlobals.reach_stage = max(1, MyGlobals.reach_stage)
            print('[ ] Started executing 1st tree... ')
            clear_globals()
            sym = BitVec("CALLER-1-" + self.function1, 256)
            con = BitVecVal(0, 256)
            MyGlobals.s1.add(sym != con)
            con = BitVecVal(int(MyGlobals.contract_addr, 16), 256)
            MyGlobals.s1.add(sym & 0xffffffffffffffffffffffffffffffffffffffff != con)

            if  "'payable': True" in str(MyGlobals.func_hash2abi[self.function1]):
                sym_callv=BitVec('CALLVALUE-1-'+self.function1,256)
                MyGlobals.s1.add(ULT(sym_callv,10**20))
                if self.function1=='11111111':
                    MyGlobals.m.callable_funcs.add(self.function1)

            storage = {}
            stack = []
            mmemory = {}
            data = {}
            trace = []
            sha3_dict = {}
            sha3_values = {}
            function_hash = self.function1

            if self.search_enhance:
                MyGlobals.s.push()
                self.execute_one_block(ops, stack, 0, trace, storage, mmemory, data, configurations, sha3_dict,
                                       sha3_values, ['SSTORE', 'CALL', 'DELEGATECALL', 'CALLCODE', 'SUICIDE'],
                                       self.function_sstore, 0, 0, function_hash, False, key)
                MyGlobals.s.pop()

                return MyGlobals.solution_found



            MyGlobals.s = MyGlobals.s1
            MyGlobals.s.set("timeout", 1000)

            MyGlobals.s.push();
            MyGlobals.new_branch = True

            self.execute_one_block(ops, stack, 0, trace, storage, mmemory, data, configurations, sha3_dict, sha3_values,
                                   ['STOP', 'RETURN'], self.function_accept, 0, 0, function_hash, False, key)
            MyGlobals.s.pop();

            print('\033[94m[+] Finished executing 1st tree... \033[0m')
            print('\033[92m    Visited %d nodes\033[0m' % (MyGlobals.visited_nodes))
            MyGlobals.current_key = (1, 1);

            MyGlobals.addr_read = deepcopy(addr_read_backup)
            MyGlobals.addr_write = deepcopy(addr_write_backup)
            return

        '''

		** Phase 2

		'''
        if 2 == key:



            MyGlobals.path[0]=self.pc
            #enforce state change
            addr_w_1 = []
            for elem_w in MyGlobals.addr_write:
                if len(elem_w) > 2:
                    t = deepcopy(elem_w[-1])
                    t['z3']=simplify(t['z3'])
                    if (is_bv_value(t['z3']) and t['z3'].as_long()>0) or (is_bv(t['z3']) and 'input' in str(t['z3'])):
                        if elem_w[1] in MyGlobals.storage_temp:
                            value=MyGlobals.storage_temp[elem_w[1]]
                            addr_w_1.append(t['z3'] !=value)
                        else:
                            if elem_w[1] in MyGlobals.addr2val:
                                addr_w_1.append(t['z3'] != MyGlobals.addr2val[elem_w[1]])
                            else:
                                addr_w_1.append(t['z3'] != 0)
                                MyGlobals.addr2val[elem_w[1]]=0
            state_changed = False
            if addr_w_1:
                MyGlobals.s.add(simplify(Or(addr_w_1)))
                if not MyGlobals.s.check()==sat:
                    if MyGlobals.terminate_stage == 2:
                        state_changed = False
                    else:
                        return
                else:
                    state_changed=True


            MyGlobals.current_key = (2, 0)
            addr_read_backup = deepcopy(MyGlobals.addr_read)
            addr_write_backup = deepcopy(MyGlobals.addr_write)
            MyGlobals.addr_read.append(MyGlobals.current_key)
            MyGlobals.addr_write.append(MyGlobals.current_key)
            bals_1_backup=deepcopy(MyGlobals.bals_1)
            bals_2_backup = deepcopy(MyGlobals.bals_2)
            call_vars_backup=deepcopy(MyGlobals.call_vars)
            if  "'payable': True" in str(MyGlobals.func_hash2abi[self.function1]):
                sym_caller=BitVec('CALLER-1-'+self.function1,256)
                sym_callv=BitVec('CALLVALUE-1-'+self.function1,256)
                send_ether_bd(1,sym_caller ,self.contract_address, sym_callv)
            for elem in MyGlobals.call_vars:
                send_ether_bd(elem[1], self.contract_address, elem[2], elem[3])
            if "'payable': True" in str(MyGlobals.func_hash2abi[self.function2]):
                sym_caller = BitVec('CALLER-2-' + self.function2, 256)
                sym_callv = BitVec('CALLVALUE-2-' + self.function2, 256)
                send_ether_bd(2, sym_caller, self.contract_address, sym_callv)
                MyGlobals.s1.add(ULT(sym_callv, 10 ** 22))

            if MyGlobals.terminate_stage==2:
                if state_changed or "'payable': True" in str(MyGlobals.func_hash2abi[self.function1]) or MyGlobals.call_vars:
                    p_dict,p_list = self.path2dict(1, 0, 0)
                    p_hash=hash(str(p_list))
                    if True:
                        if not p_hash in MyGlobals.m.hash2path:
                            MyGlobals.m.hash2path[p_hash] = p_dict
                            MyGlobals.m.hash2path_list[p_hash] = p_list
                        MyGlobals.m.feasible_paths_valid.add(p_hash)
                        MyGlobals.m.path_hash2func_hash[p_hash] = self.function1

                        MyGlobals.m.ws[p_hash]=MyGlobals.m.ws_temp
                        MyGlobals.m.rs[p_hash] = MyGlobals.m.rs_temp
                        MyGlobals.m.triggered_ws[self.function1].update(MyGlobals.m.ws_temp)
                        MyGlobals.m.triggered_rs[self.function1].update(MyGlobals.m.rs_temp)

                        MyGlobals.m.triggered_ws_id[self.function1].update(MyGlobals.m.ws_temp_id)
                        MyGlobals.m.triggered_rs_id[self.function1].update(MyGlobals.m.rs_temp_id)
                else:
                    p_dict, p_list = self.path2dict(1, 0, 0)
                    p_hash = hash(str(p_list))
                    if True:
                        if not p_hash in MyGlobals.m.hash2path:
                            MyGlobals.m.hash2path[p_hash] = p_dict
                            MyGlobals.m.hash2path_list[p_hash] = p_list
                        MyGlobals.m.infeasible_paths.add(p_hash)
                        MyGlobals.m.may_feasible_paths.add(p_hash)
                        MyGlobals.m.path_hash2func_hash[p_hash] = self.function1

                        MyGlobals.m.rs[p_hash] = MyGlobals.m.rs_temp
                        MyGlobals.m.ws[p_hash] = MyGlobals.m.ws_temp
                        MyGlobals.m.rs_added.update(MyGlobals.m.rs_temp)
                        MyGlobals.m.ws_added.update(MyGlobals.m.ws_temp)

                        MyGlobals.m.rs_added_id.update(MyGlobals.m.rs_temp_id)
                        MyGlobals.m.ws_added_id.update(MyGlobals.m.rs_temp_id)
                return
            MyGlobals.call_vars.clear()



            MyGlobals.reach_stage = max(2, MyGlobals.reach_stage)
            print('\033[92m    Visited %d nodes\033[0m' % (MyGlobals.visited_nodes))
            print('[ ] Started executing 2nd tree... ')
            function_hash = self.function2
            stack = [];     MyGlobals.stack2=[];MyGlobals.stack2_all=[[]];MyGlobals.mmemory_stack2={};MyGlobals.mmemory_stack2_all = [[]];MyGlobals.storage_stack2={}
            storage2 = copy.deepcopy(datastructures['storage'])
            sha3_dict2 = copy.deepcopy(datastructures['sha3_dict'])
            sha3_values2 = copy.deepcopy(datastructures['sha3_values'])
            data2 = copy.deepcopy(datastructures['data'])
            mmemory = {}
            trace = []
            MyGlobals.search_condition_found = False
            MyGlobals.stop_search = False

            # Setting up the solvers

            MyGlobals.s2.reset()
            MyGlobals.s2.set("timeout", 1000)
            MyGlobals.s = MyGlobals.s2

            sym = BitVec("CALLER-2-" + self.function2, 256)
            con = BitVecVal(0, 256)
            MyGlobals.s.add(sym != con)
            con = BitVecVal(int(MyGlobals.contract_addr, 16), 256)
            MyGlobals.s.add(sym & 0xffffffffffffffffffffffffffffffffffffffff != con)

            MyGlobals.s.push();
            MyGlobals.new_branch = True

            if MyGlobals.reach_stage ==key== 2: MyGlobals.stack2_all.append(deepcopy(MyGlobals.stack2));MyGlobals.mmemory_stack2_all.append(deepcopy(MyGlobals.mmemory_stack2))

            self.execute_one_block(ops, stack, 0, trace, storage2, mmemory, data2, configurations, sha3_dict2,sha3_values2, ['STOP', 'RETURN'], self.function_accept, 0, 0, function_hash, True,
                                   key)

            MyGlobals.s.pop()
            if MyGlobals.reach_stage ==key== 2 and len(MyGlobals.stack2_all)>1: MyGlobals.stack2 = MyGlobals.stack2_all.pop();MyGlobals.mmemory_stack2=MyGlobals.mmemory_stack2_all.pop()

            MyGlobals.s = MyGlobals.s1
            print('\033[94m[+] Finished executing 2nd tree... \033[0m')
            MyGlobals.current_key = (2, 1)
            MyGlobals.addr_read = deepcopy(addr_read_backup)
            MyGlobals.addr_write = deepcopy(addr_write_backup)

            MyGlobals.bals_1=deepcopy(bals_1_backup)
            MyGlobals.bals_2 = deepcopy(bals_2_backup)
            MyGlobals.call_vars=deepcopy(call_vars_backup)
            return

        '''

		** Phase 3

		'''
        if 3 == key:

            MyGlobals.path[1]=self.pc
            addr_dict_w_1= {}
            addr_w_2 = []
            for elem_w in MyGlobals.addr_write:
                if len(elem_w) > 2:
                    if elem_w[0]==1:
                        addr_dict_w_1[elem_w[1]] = simplify(elem_w[-1]['z3'])
            for elem_w in MyGlobals.addr_write:
                if len(elem_w) > 2:
                    if elem_w[0] == 2:
                        t = deepcopy(elem_w[-1])
                        t['z3'] = simplify(t['z3'])
                        if  (is_bv(t['z3']) and 'input' in str(t['z3']) and self.function2 in str(t['z3']) and not self.function1 in str(t['z3'])):#(is_bv_value(t['z3']) and t['z3'].as_long()>0) or
                            if elem_w[1] in MyGlobals.storage_temp:
                                value=MyGlobals.storage_temp[elem_w[1]]
                                addr_w_2.append(t['z3'] != value)
                            else:
                                if elem_w[1] in MyGlobals.addr2val:# if addr in storage , val must be storage val
                                    value=MyGlobals.addr2val[elem_w[1]]
                                    addr_w_2.append(t['z3'] != value)
                                else:
                                    value=0
                                    addr_w_2.append(t['z3'] != value)
                                    MyGlobals.addr2val[elem_w[1]]=value
                            if elem_w[1] in addr_dict_w_1:
                                elem_int=int(elem_w[1])
                                if elem_int.bit_length()<10:
                                    addr_w_2.pop()
                                    addr_w_2.append(Or(t['z3'] != value, t['z3'] != addr_dict_w_1[elem_w[1]]))# t['z3'] must change initial storage or storage after stage1

            if addr_w_2:
                if MyGlobals.s.check()==sat:
                    MyGlobals.s.add(simplify(Or(addr_w_2)))
                    if not MyGlobals.s.check()==sat:
                        return

            MyGlobals.current_key = (3, 0)
            addr_read_backup = deepcopy(MyGlobals.addr_read)
            addr_write_backup = deepcopy(MyGlobals.addr_write)
            MyGlobals.addr_read.append(MyGlobals.current_key)
            MyGlobals.addr_write.append(MyGlobals.current_key)

            MyGlobals.reach_stage = max(3, MyGlobals.reach_stage)
            solution_dict_stage2 = {}
            p_dict, p_list = self.path2dict(2, 0, 0)
            self.triggered_length = len(p_list)
            p_hash = hash(str(p_list))
            if [p_hash,True] in MyGlobals.m.activated_paths and MyGlobals.terminate_stage==3:
                return
            if MyGlobals.dep_activated:
                if MyGlobals.s.check() == sat:

                    s_temp00=Solver()
                    s_temp00.add(MyGlobals.s.assertions())
                    addr_w_12=[]
                    for elem_w in MyGlobals.addr_write:
                        if len(elem_w)>2:
                            t = deepcopy(elem_w[-1])
                            t['z3'] = simplify(t['z3'])
                            if is_bv(t['z3']) and 'input' in str(t['z3']):
                                if elem_w[1] in MyGlobals.addr2val:
                                    v=MyGlobals.addr2val[elem_w[1]]
                                    addr_w_12.append(t['z3'] != v)
                                else:
                                    addr_w_12.append(t['z3']!=0)
                                    MyGlobals.addr2val[elem_w[1]]=0
                    if addr_w_12:
                        s_temp00.add(Or(addr_w_12))
                        MyGlobals.s.push()
                        MyGlobals.s.add(s_temp00.assertions())
                        if MyGlobals.s.check()==sat:
                            solution_dict_stage2 = get_function_calls(22, key, self.function1, self.function1,self.function2,self.debug,datastructures['sha3_values'])
                        MyGlobals.s.pop()
                    if not solution_dict_stage2:
                        solution_dict_stage2 = get_function_calls(22, key, self.function1, self.function1,self.function2,self.debug,datastructures['sha3_values'])
                    if solution_dict_stage2:
                        MyGlobals.solution_dict_stage2[(self.function1, self.function2)].append(solution_dict_stage2)

            if solution_dict_stage2 and MyGlobals.dep_activated:
                print('dep found')

                if not [p_hash,True] in MyGlobals.m.activated_paths:
                    MyGlobals.m.activated_paths.append([p_hash,True])
                    MyGlobals.m.feasible_paths_valid.add(p_hash)
                    if p_hash in MyGlobals.m.infeasible_paths:
                        MyGlobals.m.infeasible_paths.remove(p_hash)

                    MyGlobals.m.hash2path[p_hash] = p_dict
                    MyGlobals.m.hash2path_list[p_hash] = p_list
                    MyGlobals.m.path_hash2func_hash[p_hash] = self.function2
                    MyGlobals.m.rs[p_hash] = deepcopy(MyGlobals.m.rs_temp)
                    MyGlobals.m.ws[p_hash] = deepcopy(MyGlobals.m.ws_temp)

                    MyGlobals.m.rs_added.update(MyGlobals.m.rs_temp)
                    MyGlobals.m.ws_added.update(MyGlobals.m.ws_temp)
                    MyGlobals.m.rs_added_id.update(MyGlobals.m.rs_temp)
                    MyGlobals.m.ws_added_id.update(MyGlobals.m.ws_temp)

                return
            if MyGlobals.terminate_stage==3:
                return
            function_hash = self.function2
            stack = []
            storage3 = {}
            sha3_dict3 = copy.deepcopy(datastructures['sha3_dict'])
            sha3_values3 = copy.deepcopy(datastructures['sha3_values'])
            data3 = copy.deepcopy(datastructures['data'])
            mmemory = {}
            trace = []
            MyGlobals.search_condition_found = False
            MyGlobals.stop_search = False
            MyGlobals.solution_found = False
            MyGlobals.new_branch = True
            if not MyGlobals.solution_found:
                print('\033[92m    Visited %d nodes\033[0m' % (MyGlobals.visited_nodes))
                print('[ ] Started executing 3rd tree... ')
                function_hash = self.function2
                stack[:] = []; MyGlobals.stack2[:]=[]
                storage3.clear()
                sha3_dict3 = copy.deepcopy(datastructures['sha3_dict'])
                sha3_values3 = copy.deepcopy(datastructures['sha3_values'])
                data3 = copy.deepcopy(datastructures['data'])
                mmemory.clear()
                trace[:] = []
                MyGlobals.search_condition_found = False
                MyGlobals.stop_search = False

                MyGlobals.s.push();
                MyGlobals.new_branch = True
                self.execute_one_block(ops, stack, 0, trace, storage3, mmemory, data3, configurations, sha3_dict3,
                                       sha3_values3, ['STOP', 'RETURN'], self.function_accept, 0, 0, function_hash,
                                       False, key)
                MyGlobals.s.pop();

                print('\033[94m[+] Finished executing 3rd tree... \033[0m')
                MyGlobals.current_key = (3, 1)
                MyGlobals.addr_read = deepcopy(addr_read_backup)
                MyGlobals.addr_write = deepcopy(addr_write_backup)
            if MyGlobals.in_sha3 > 0 and MyGlobals.solution_found:
                return

            MyGlobals.solution_found = False

            return

        '''

		** Phase 4

		'''
        if 4 == key:
            MyGlobals.path[2]=self.pc
            MyGlobals.current_key = (4, 0)

            addr_read_backup = deepcopy(MyGlobals.addr_read)
            addr_write_backup = deepcopy(MyGlobals.addr_write)
            MyGlobals.addr_read.append(MyGlobals.current_key)
            MyGlobals.addr_write.append(MyGlobals.current_key)
            MyGlobals.new_branch = True
            MyGlobals.reach_stage = max(4, MyGlobals.reach_stage)

            bals_1_backup_key4=deepcopy(MyGlobals.bals_1)
            bals_2_backup_key4 = deepcopy(MyGlobals.bals_2)
            call_vars_backup_key4=deepcopy(MyGlobals.call_vars)
            if "'payable': True" in str(MyGlobals.func_hash2abi[self.function2]):
                sym_caller = BitVec('CALLER-2-' + self.function2, 256)
                sym_callv = BitVec('CALLVALUE-2-' + self.function2, 256)
                send_ether_bd(3, sym_caller, self.contract_address, sym_callv)

            for elem in MyGlobals.call_vars:
                send_ether_bd(elem[1], self.contract_address, elem[2], elem[3])
            if "'payable': True" in str(MyGlobals.func_hash2abi[self.function1]):
                sym_caller = BitVec('CALLER-1-' + self.function1, 256)
                sym_callv = BitVec('CALLVALUE-1-' + self.function1, 256)
                send_ether_bd(4, sym_caller, self.contract_address, sym_callv)
            MyGlobals.call_vars.clear()

            print('\033[92m    Visited %d nodes\033[0m' % (MyGlobals.visited_nodes))
            print('[ ] Started executing 4th tree... ')
            function_hash = self.function1
            stack = []
            storage4 = copy.deepcopy(datastructures['storage'])
            sha3_dict4 = copy.deepcopy(datastructures['sha3_dict'])
            sha3_values4 = copy.deepcopy(datastructures['sha3_values'])
            data4 = copy.deepcopy(datastructures['data'])
            mmemory = {}
            trace = []
            MyGlobals.search_condition_found = False
            MyGlobals.stop_search = False

            # Setting up the solvers
            MyGlobals.s = Solver()

            MyGlobals.s = MyGlobals.s1
            MyGlobals.s1.set("timeout", 1000)
            MyGlobals.s.push()
            MyGlobals.s.push();
            MyGlobals.new_branch = True
            self.execute_one_block(ops, stack, 0, trace, storage4, mmemory, data4, configurations, sha3_dict4,
                                   sha3_values4, ['STOP', 'RETURN'], self.function_accept, 0, 0, function_hash, False,
                                   key)
            MyGlobals.s.pop()

            print('\033[94m[+] Finished executing 4th tree... \033[0m')

            MyGlobals.bals_1=deepcopy(bals_1_backup_key4)
            MyGlobals.bals_2 = deepcopy(bals_2_backup_key4)
            MyGlobals.call_vars=deepcopy(call_vars_backup_key4)

            MyGlobals.current_key = (4, 1)
            MyGlobals.addr_read = deepcopy(addr_read_backup)
            MyGlobals.addr_write = deepcopy(addr_write_backup)
            MyGlobals.s = MyGlobals.s2

            if MyGlobals.in_sha3 > 0 and MyGlobals.solution_found:
                return
            MyGlobals.solution_found = False
            return

        return

    '''
        This function executes opcodes
	'''

    def execute_one_block(self, ops, stack, pos, trace, storage, mmemory, data, configurations, sha3_dict, sha3_values,
                          search_op, search_function, jumpdepth, calldepth, function_hash, find_solution, key):

        sys.stdout.flush()

        EVM_stack_shadow_se=EVMCore_stack2()

        global s, d, stop_search, search_condition_found, visited_nodes, st, MAX_JUMP_DEPTH, MAX_CALL_DEPTH, fast_search, solution_found, max_solutions, solution_dict


        actual_key = 0
        if key in [1, 4]: actual_key = 1
        if key in [2, 3]: actual_key = 2
        jump_condition = False

        if MyGlobals.stop_search: return

        MyGlobals.visited_nodes += 1
        if MyGlobals.visited_nodes > MyGlobals.MAX_VISITED_NODES: MyGlobals.stop_search = True; return

        # Stop the search once it exceeds timeout
        time_now = datetime.datetime.now()
        if MyGlobals.ONE_PAIR_TIMEOUT < int((time_now - MyGlobals.Time_checkpoint).total_seconds()):
            MyGlobals.stop_search = True
            return
        if MyGlobals.ONE_CONTRACT_TIMEOUT < int((time_now - MyGlobals.Time_checkpoint_HB).total_seconds()):
            MyGlobals.stop_search = True
            return

        # Execute the next block of operations.
        first = True
        newpos = pos
        while (first or newpos != pos) and not MyGlobals.stop_search:
            first = False
            pos = newpos
            return_False=False
            if (ops[pos]['o']=='JUMPI' or ops[pos]['o']=='CALL' or ops[pos]['o']=='DELEGATECALL' or ops[pos]['o']=='SELFDESTRUCT' ):
                self.impinsts.append(str(ops[pos]['id'])+str(ops[pos]['op']))
            if MyGlobals.reach_stage ==key== 2 and 'RETURN' == ops[pos]['o']:
                if self.is_fixed(stack[-1]):
                        return_False=simplify(mmemory[self.get_value(stack[-1])]['z3'] ==0)

            if ops[pos]['o'] in ['RETURN','STOP','SELFDESTRUCT','SUICIDE']:
                if actual_key==1:
                    MyGlobals.m.callable_funcs.add(self.function1)
                elif actual_key==2:
                    MyGlobals.m.callable_funcs.add(self.function2)
            if (ops[pos]['o'] == 'REVERT' or  return_False) and key in [1,2] and MyGlobals.terminate_stage in [2,3]:
                p_dict, p_list = self.path2dict(key, ops[pos]['id'], ops[pos + 1]['id'])
                p_hash = hash(str(p_list))
                res, path_temp_other_dir, path_hash_other_direction,path_temp_other_dir_dict = self.to_other_direction(p_list,p_dict,self.pos_last_jumpi)
                if key==1 and MyGlobals.terminate_stage==2:
                    if path_hash_other_direction in MyGlobals.m.covered_prefixs:
                        return
                    else:
                        self.s_except_last_eq.push()
                        self.s_except_last_eq.add(self.last_eq)
                        branch_covered_temp = False
                        if self.s_except_last_eq.check() == sat:  # we do not add indv that leads cost to 0, because we sure this will be encountered later at "REVERT" or "RETURN" or ...
                            # this means branch_covered
                            self.s_except_last_eq.pop()
                            MyGlobals.m.covered_prefixs.add(path_hash_other_direction)
                            return
                        else:
                            self.s_except_last_eq.pop()
                            if True:
                                MyGlobals.m.hash2path[path_hash_other_direction] =path_temp_other_dir_dict
                                MyGlobals.m.hash2path_list[path_hash_other_direction]=path_temp_other_dir
                                MyGlobals.m.infeasible_paths.add(path_hash_other_direction)
                                MyGlobals.m.path_hash2func_hash[path_hash_other_direction] = self.function1

                                MyGlobals.m.rs[path_hash_other_direction] = MyGlobals.m.rs_temp
                                MyGlobals.m.ws[path_hash_other_direction]=MyGlobals.m.ws_temp
                                MyGlobals.m.rs_added.update(MyGlobals.m.rs_temp)
                                MyGlobals.m.ws_added.update(MyGlobals.m.ws_temp)

                                MyGlobals.m.rs_added_id.update(MyGlobals.m.rs_temp_id)
                                MyGlobals.m.ws_added_id.update(MyGlobals.m.rs_temp_id)


                        return

                if key ==2 and MyGlobals.terminate_stage==3:
                    if not MyGlobals.feasible_jumpdest[2]:
                        #dep found

                        if path_hash_other_direction in MyGlobals.m.covered_prefixs:
                            return
                        else:
                            self.s_except_last_eq.push()
                            self.s_except_last_eq.add(self.last_eq)
                            branch_covered_temp = False
                            if self.s_except_last_eq.check() == sat:
                                self.s_except_last_eq.pop()
                                return
                            else:
                                self.s_except_last_eq.pop()
                                if True:
                                    solution_dict_stage2 = get_function_calls(22, key + 1, self.function1,
                                                                              self.function1,
                                                                              self.function2, self.debug, sha3_values)
                                    if solution_dict_stage2:

                                        MyGlobals.solution_dict_stage2[(self.function1, self.function2)].append(
                                            solution_dict_stage2)
                                        MyGlobals.m.hash2path[path_hash_other_direction] = path_temp_other_dir_dict
                                        MyGlobals.m.hash2path_list[path_hash_other_direction] = path_temp_other_dir
                                        MyGlobals.m.path_hash2func_hash[path_hash_other_direction] = self.function2
                                        MyGlobals.m.activated_paths.append([path_hash_other_direction,False])
                                        MyGlobals.m.infeasible_paths.add(path_hash_other_direction)

                                        MyGlobals.m.rs[path_hash_other_direction] = MyGlobals.m.rs_temp
                                        MyGlobals.m.ws[path_hash_other_direction] = MyGlobals.m.ws_temp
                                        MyGlobals.m.rs_added.update(MyGlobals.m.rs_temp)
                                        MyGlobals.m.ws_added.update(MyGlobals.m.ws_temp)

                                        MyGlobals.m.rs_added_id.update(MyGlobals.m.rs_temp_id)
                                        MyGlobals.m.ws_added_id.update(MyGlobals.m.rs_temp_id)
                            return

            # If no more code, then stop
            if pos >= len(ops) or pos < 0:
                if self.debug: print('\033[94m[+] Reached bad/end of execution\033[0m')
                return False

            # self.debug info
            if self.debug: print('[ %3d %3d %5d] : %4x : %12s : %s  ' % (
                calldepth, jumpdepth, MyGlobals.visited_nodes, ops[pos]['id'], ops[pos]['o'], ops[pos]['input']),
                                 search_op)

            # Check if calldepth or jumpdepth should be changed
            # and stop the search if certain conditions are met
            if pos == 0:
                calldepth += 1
                jumpdepth = 0
            if ops[pos]['o'] == 'JUMPDEST': jumpdepth += 1
            if (jumpdepth > MyGlobals.MAX_JUMP_DEPTH):
                if self.debug: print('\033[95m[-] Reach MAX_JUMP_DEPTH\033[0m', jumpdepth, MyGlobals.MAX_JUMP_DEPTH)
                return
            if (calldepth > MyGlobals.MAX_CALL_DEPTH):
                if self.debug: print('\033[95m[-] Reach MAX_CALL_DEPTH\033[0m')
                return

            # Check if the current op is one of the search ops.
            if ops[pos]['o'] in search_op:
                if self.debug:
                    print('\033[96m[+] Reached %s at %x \033[0m' % (ops[pos]['o'], ops[pos]['id']))

                # If JUMPI is the search op and a push2 0000 before it, ensure that we add the additional condition on the stack to check for satisfiability.
                if 'JUMPI' == ops[pos]['o'] and 'JUMPI' in search_op:
                    if self.is_fixed(stack[-1]):
                        if self.get_value(stack[-1]) == 0:
                            jump_condition = True
                # Return value should not be False
                if 'RETURN' == ops[pos]['o']:
                    return_False=False
                    if key==1:
                        return_False = True
                    elif key==2 or key==3:
                        return_False = True
                    if return_False:
                        if self.is_fixed(stack[-1]):
                            MyGlobals.s.add(mmemory[self.get_value(stack[-1])]['z3'] != 0)


                if self.search_enhance:
                    new_search_condition_found, stop_expanding_the_search_tree = search_function(ops[pos], stack, trace,self.debug)

                else:
                    new_search_condition_found, stop_expanding_the_search_tree = search_function(ops[pos], stack, trace,self.debug) #true ,false by default

                MyGlobals.search_condition_found = MyGlobals.search_condition_found or new_search_condition_found

                if MyGlobals.search_condition_found and self.search_enhance:
                    MyGlobals.solution_found = True

                # In case there is a probability of finding a solution we need to add the additional constraints to the solver before finding the solutions.
                if MyGlobals.search_condition_found and not self.search_enhance:
                    # If jump_condition is True then add the addtional condition of JUMPI to the global solver to retrieve solutions.
                    if jump_condition:
                        temp = copy.deepcopy(stack[-2])
                        MyGlobals.s.push()
                        MyGlobals.new_branch = True
                        MyGlobals.s.add(temp['z3'] != 0)

                if MyGlobals.search_condition_found and (not self.search_enhance)  and (
                        (key == 1 or key == 2) or (key == 3 and not find_solution)) and (not jump_condition):

                    if MyGlobals.s.check() == sat:
                        if key == 1 or key == 2:
                            MyGlobals.s1_temp.reset()
                            MyGlobals.s2_temp.reset()
                            MyGlobals.sstore_set = []
                        # Save the state of execution before calling next tree
                        datastructures = self.new_state(stack, storage, sha3_dict, sha3_values, mmemory, trace, data)

                        MyGlobals.s.push();
                        MyGlobals.new_branch = True
                        self.pc=ops[pos]['id']
                        self.run_one_check(ops, key + 1, datastructures)
                        MyGlobals.s.pop();

                    else:
                        return
                    return

                if key == 4 and not self.search_enhance:
                    solution = get_function_calls(calldepth, key, function_hash, self.function1, self.function2,
                                                  self.debug,sha3_values,self.path)

                    if not solution:
                        # In case of jump condition, the control should not be returned to the caller of execute_block. Instead, callee function continues to execute.
                        if not jump_condition:
                            return

                        else:
                            MyGlobals.s.pop();

                            jump_condition = False
                            MyGlobals.search_condition_found = False

                    else:

                        MyGlobals.solution_found = True


                        if not (self.function1, self.function2) in MyGlobals.solution_dict:
                            MyGlobals.solution_dict[(self.function1, self.function2)] = []

                        if solution_filter(solution, self.function1, self.function2):

                            MyGlobals.solution_dict[(self.function1, self.function2)].append(solution)
                            MyGlobals.m.inst_pairs.append(deepcopy(MyGlobals.m.inst_pair))

                        if len(MyGlobals.solution_dict[(self.function1, self.function2)]) == MyGlobals.max_solutions:
                            MyGlobals.stop_search = True

                        # In case of jump condition, the stack has to be cleared with the extra jump condition before handling JUMPI operation in its usual way.
                        if jump_condition and not len(
                                MyGlobals.solution_dict[(self.function1, self.function2)]) == MyGlobals.max_solutions:
                            MyGlobals.s.pop();

                            jump_condition = False
                            MyGlobals.search_condition_found = False


                        else:
                            return

                if jump_condition:
                    jump_condition = False



            # Execute the next operation
            newpos, halt = self.execute(ops, stack, pos, storage, mmemory, data, sha3_values, calldepth, function_hash, key,
                                        self.search_enhance, self.debug, self.read_from_blockchain)
            if MyGlobals.reach_stage ==key== 2:
                EVM_stack_shadow_se.execute_stack2(ops, MyGlobals.stack2, pos, MyGlobals.storage_stack2, MyGlobals.mmemory_stack2, data, sha3_values, calldepth, function_hash, key, self.search_enhance, self.debug, self.read_from_blockchain)
            # If halt is True, then the execution should stop
            if halt:

                if self.debug: print('\033[94m[+] Halted on %s on line %x \033[0m' % (ops[pos]['o'], ops[pos]['id']))

                # if MyGlobals.stop_search: Search condition found
                # if not MyGlobals.stop_search: Search condition not found
                # If normal stop
                if self.search_enhance and ops[pos]['o'] in ['REVERT']:
                    MyGlobals.solution_found = True
                    # p_hash = hash(str(self.path))
                    # MyGlobals.hash2path[p_hash] = self.path

                    return

                if ops[pos]['o'] in ['STOP', 'RETURN', 'SUICIDE']:

                    # If search condition still not found then call again the contract
                    # (infinite loop is prevented by calldepth )
                    if not MyGlobals.search_condition_found:
                        return

                    # Else stop the search
                    else:
                        if self.search_enhance:
                            MyGlobals.solution_found = True

                            return
                        if (not self.search_enhance) and (
                                (key == 1 or key == 2) or (key == 3 and 'STOP' in search_op)):

                            # Save the state of execution before calling next tree
                            if MyGlobals.s.check() == sat:
                                if key == 1 or key == 2:
                                    MyGlobals.s1_temp.reset()
                                    MyGlobals.s2_temp.reset()
                                    MyGlobals.sstore_set = []

                                # Save the state of execution before calling next tree
                                datastructures = self.new_state(stack, storage, sha3_dict, sha3_values, mmemory, trace,
                                                                data)
                                MyGlobals.s.push();
                                MyGlobals.new_branch = True
                                self.pc = ops[pos]['id']
                                self.run_one_check(ops, key + 1, datastructures)
                                MyGlobals.s.pop();

                            else:
                                return

                        if find_solution and  (key == 3 and find_solution) or key == 4:
                            MyGlobals.path[3]=ops[pos]['id']
                            solution = get_function_calls(calldepth, key, function_hash, self.function1, self.function2,
                                                          self.debug,sha3_values,self.path)

                            if not solution:
                                return
                            MyGlobals.solution_found = True


                            if not (self.function1, self.function2) in MyGlobals.solution_dict:
                                MyGlobals.solution_dict[(self.function1, self.function2)] = []

                            # if not solution in MyGlobals.solution_dict[(self.function1, function2)] and len(MyGlobals.solution_dict[(self.function1, function2)]) < MyGlobals.max_solutions:
                            if solution_filter(solution, self.function1, self.function2):

                                MyGlobals.solution_dict[(self.function1, self.function2)].append(solution)
                                MyGlobals.m.inst_pairs.append(deepcopy(MyGlobals.m.inst_pair))
                            if len(MyGlobals.solution_dict[
                                       (self.function1, self.function2)]) == MyGlobals.max_solutions:
                                MyGlobals.stop_search = True

                        return


                # In all other cases stop further search in this branch of the tree
                else:
                    return

            # If program counter did not move
            # It means either:
            # 1) we need to branch
            # 2) unknown instruction
            if pos == newpos:

                si = ops[pos]
                # It can be JUMPI
                if si['o'] == 'JUMPI':

                    is_new_call = True
                    if ("'payable': True" in str(MyGlobals.func_hash2abi[self.function1]) and "'payable': True" in str(MyGlobals.func_hash2abi[self.function2]) and (self.function1=='11111111' or self.function2=='11111111')):
                        is_new_call, imp_ids = self.key_inst(['JUMPI'])
                    if len(stack) < 2:
                        if self.debug: print(
                            '\033[95m[-] In JUMPI (line %x) the stack is too small to execute JUMPI\033[0m' % pos)
                        return False

                    addr = stack.pop()
                    des = stack.pop()

                    if MyGlobals.reach_stage ==key== 2:
                        addr2 = MyGlobals.stack2.pop()
                        des2=MyGlobals.stack2.pop()


                    if self.is_undefined(des) and not self.search_enhance:
                        if self.debug: print(
                            '\033[95m[-] In JUMPI the expression cannot be evaluated (is undefined)\033[0m')
                        return False

                    sole = '  * sole * '

                    fallback_frame = False

                    #
                    # Branch when decision is incorrect (no need to compute the addresses)
                    #

                    MyGlobals.new_branch = True
                    if MyGlobals.terminate_stage in [2]:
                        add_feasible_jump_constraints=False
                    elif MyGlobals.terminate_stage in [5] and ("'payable': True" in str(MyGlobals.func_hash2abi[self.function1]) and "'payable': True" in str(MyGlobals.func_hash2abi[self.function2])) :
                        add_feasible_jump_constraints = False
                    else:
                        add_feasible_jump_constraints=True

                    jump_decision=True
                    if add_feasible_jump_constraints:
                        if MyGlobals.terminate_stage==3 and key==2:
                            p_dict_temp, p_list_temp = self.path2dict(2, 0, 0)
                            l = len(p_list_temp)
                            if len(MyGlobals.feasible_jumpdest[2])>l:
                                if MyGlobals.feasible_jumpdest[2][:l]==p_list_temp:
                                    jump_start=MyGlobals.feasible_jumpdest[2][l]
                                    jump_des=MyGlobals.feasible_jumpdest[2][l+1]
                                    if  si['id'] == jump_start and ops[pos + 1]['id'] ==jump_des:
                                        jump_decision =True
                                    else:
                                        jump_decision = False
                            else:
                                jump_decision=True
                        else:
                            if MyGlobals.feasible_jumpdest[key]:
                                jump_decision = si['id'] in MyGlobals.feasible_jumpdest[key] and ops[pos + 1]['id'] in \
                                            MyGlobals.feasible_jumpdest[key][si['id']]
                            else:
                                jump_decision=True
                    if jump_decision:
                        try:
                            # We want to switch off the check for jumpi while we are searching for functions which can change the global state.
                            # But, we will switch off the jumpi check only when the execution of the desired function starts.

                            if self.search_enhance:

                                if self.debug: print('Now searching without jumpi check : Branch 1\n')
                                storage2 = copy.deepcopy(storage)
                                stack2 = copy.deepcopy(stack)
                                trace2 = copy.deepcopy(trace)
                                mmemory2 = copy.deepcopy(mmemory)
                                data2 = copy.deepcopy(data)
                                sha3_values2 = copy.deepcopy(sha3_values)
                                sha3_dict2 = copy.deepcopy(sha3_dict)

                                if self.debug: print('\t' * 8 + '-' * 20 + 'JUMPI branch 1 (go through)')
                                sole = ''
                                if self.path.count((key, ops[pos]['id'], ops[pos + 1]['id'])) > self.allowed_cycle:
                                    return
                                path_back_up = deepcopy(self.path)
                                call_vars= deepcopy(MyGlobals.call_vars)
                                rs_temp, ws_temp, rs_temp_id, ws_temp_id, rwaddr2id = self.rw_back_up()

                                self.path.append((key, ops[pos]['id'], ops[pos + 1]['id']))
                                self.execute_one_block(ops, stack2, pos + 1, trace2, storage2, mmemory2, data2,
                                                       configurations, sha3_dict2, sha3_values2, search_op, search_function,
                                                       jumpdepth + 1, calldepth, function_hash, find_solution, key)
                                self.path = deepcopy(path_back_up)

                                if is_new_call:
                                    MyGlobals.call_vars = call_vars
                                MyGlobals.m.rs_temp, MyGlobals.m.ws_temp, MyGlobals.m.rs_temp_id, MyGlobals.m.ws_temp_id, MyGlobals.m.rwaddr2id = rs_temp, ws_temp, rs_temp_id, ws_temp_id, rwaddr2id
                            else:
                                self.s_except_last_eq.reset()
                                self.s_except_last_eq.set('timeout', 1000)
                                self.s_except_last_eq.add(MyGlobals.s.assertions())
                                add_additional_conditions(self.s_except_last_eq, sha3_values)
                                self.last_eq = deepcopy(des['z3'] == 1)
                                self.pos_last_jumpi = ops[pos]['id']
                                if not self.is_fixed(addr):
                                    return
                                jump_dest = self.get_value(addr)
                                pos_temp=find_pos(ops, jump_dest)
                                self.pos_last_jumpi_other_dir= ops[pos_temp]['id']

                                exp_temp = des['z3'] == 0
                                self.s_except_last_eq.push()
                                self.s_except_last_eq.add(exp_temp)
                                checked_Res = self.s_except_last_eq.check()
                                self.s_except_last_eq.pop()
                                satisfied = False

                                MyGlobals.num_solver_calls += 1
                                time1 = datetime.datetime.now()

                                MyGlobals.s.push()
                                if checked_Res==sat:
                                    MyGlobals.s.add(des['z3'] == 0)
                                    if MyGlobals.reach_stage == key == 2:
                                        MyGlobals.j_c.append(des2['z3'] == 0)
                                    satisfied=True
                                elif str(checked_Res) == 'unknown':

                                    text = str(des['z3'])
                                    regex = re.compile('CALLVALUE-[1-2]-[0-9a-f]{8}')
                                    match = re.search(regex, text)
                                    if match:
                                        sm = text[match.start():match.end()]
                                        if MyGlobals.s.check() == sat:
                                            m = MyGlobals.s.model()
                                            callv = BitVec(sm, 256)
                                            des_copy=deepcopy(des)

                                            if str(callv) in str(m):

                                                if m[callv].as_long()==0 and "'payable': True" in str(MyGlobals.func_hash2abi[function_hash]):
                                                    v=random.randint(0,1000)

                                                else:
                                                    v=m[callv].as_long()
                                                des_copy['z3']=simplify(substitute(des_copy['z3'], (callv, BitVecVal(v,256))))
                                                if MyGlobals.reach_stage == key == 2:
                                                    des2_copy = deepcopy(des2)
                                                    des2_copy['z3']=simplify(substitute(des2_copy['z3'], (callv, BitVecVal(v,256))))
                                                    MyGlobals.j_c.append(des2_copy['z3'] == 0)
                                                MyGlobals.s.add(des_copy['z3'] == 0)


                                                storage2 = copy.deepcopy(storage)
                                                stack2 = copy.deepcopy(stack)
                                                trace2 = copy.deepcopy(trace)
                                                mmemory2 = copy.deepcopy(mmemory)
                                                data2 = copy.deepcopy(data)
                                                sha3_values2 = copy.deepcopy(sha3_values)
                                                sha3_dict2 = copy.deepcopy(sha3_dict)

                                                self.concretize(stack2, mmemory2, sm, v)
                                                sha3_values2[sm] = []
                                                sha3_values2[sm].append(v)

                                                if MyGlobals.reach_stage == key == 2:
                                                    MyGlobals.stack2_all.append(deepcopy(MyGlobals.stack2))
                                                    MyGlobals.mmemory_stack2_all.append(deepcopy(MyGlobals.mmemory_stack2))
                                                    MyGlobals.storage_stack2_all.append(deepcopy(MyGlobals.storage_stack2))

                                                path_back_up = deepcopy(self.path)
                                                call_vars = deepcopy(MyGlobals.call_vars)
                                                rs_temp, ws_temp, rs_temp_id, ws_temp_id, rwaddr2id = self.rw_back_up()
                                                self.path.append((key, ops[pos]['id'], ops[pos + 1]['id']))

                                                self.execute_one_block(ops, stack2, pos + 1, trace2, storage2, mmemory2,
                                                                       data2,
                                                                       configurations, sha3_dict2, sha3_values2, search_op,
                                                                       search_function, jumpdepth + 1, calldepth,
                                                                       function_hash,
                                                                       find_solution, key)

                                                self.path = deepcopy(path_back_up)
                                                if is_new_call:
                                                    MyGlobals.call_vars = call_vars
                                                MyGlobals.m.rs_temp, MyGlobals.m.ws_temp, MyGlobals.m.rs_temp_id, MyGlobals.m.ws_temp_id, MyGlobals.m.rwaddr2id = rs_temp, ws_temp, rs_temp_id, ws_temp_id, rwaddr2id
                                                if MyGlobals.reach_stage == key == 2 and len(
                                                        MyGlobals.stack2_all) > 1: MyGlobals.stack2 = MyGlobals.stack2_all.pop();MyGlobals.mmemory_stack2 = MyGlobals.mmemory_stack2_all.pop();MyGlobals.storage_stack2 = MyGlobals.storage_stack2_all.pop()

                                    satisfied = False
                                else:
                                    satisfied = False

                                if satisfied:
                                    if (MyGlobals.last_eq_func) == (
                                            int(MyGlobals.functions[len(MyGlobals.functions) - 1][1], 16)) and (MyGlobals.set_storage_symbolic) and function_hash in ['11111111', '22222222']:
                                        MyGlobals.jumpi_switch = True
                                        MyGlobals.last_eq_func = -1
                                        fallback_frame = True

                                    time2 = datetime.datetime.now()
                                    MyGlobals.total_time_solver += (time2 - time1).total_seconds()

                                    if self.debug: print('Now searching with jumpi check : Branch 1\n')

                                    storage2 = copy.deepcopy(storage)
                                    stack2 = copy.deepcopy(stack)
                                    trace2 = copy.deepcopy(trace)
                                    mmemory2 = copy.deepcopy(mmemory)
                                    data2 = copy.deepcopy(data)
                                    sha3_values2 = copy.deepcopy(sha3_values)
                                    sha3_dict2 = copy.deepcopy(sha3_dict)
                                    addr_read2 = copy.deepcopy(MyGlobals.addr_read)
                                    addr_write2 = copy.deepcopy(MyGlobals.addr_write)
                                    if self.debug: print('\t' * 8 + '-' * 20 + 'JUMPI branch 1 (go through)')

                                    if MyGlobals.reach_stage ==key== 2:
                                        MyGlobals.stack2_all.append(deepcopy(MyGlobals.stack2))
                                        MyGlobals.mmemory_stack2_all.append(deepcopy(MyGlobals.mmemory_stack2))
                                        MyGlobals.storage_stack2_all.append(deepcopy(MyGlobals.storage_stack2))
                                    sole = ''

                                    if self.path.count((key, ops[pos]['id'], ops[pos + 1]['id'])) > self.allowed_cycle:
                                        return
                                    path_back_up = deepcopy(self.path)
                                    self.path.append((key, ops[pos]['id'], ops[pos + 1]['id']))
                                    call_vars = deepcopy(MyGlobals.call_vars)
                                    rs_temp, ws_temp, rs_temp_id, ws_temp_id, rwaddr2id = self.rw_back_up()

                                    self.execute_one_block(ops, stack2, pos + 1, trace2, storage2, mmemory2, data2,
                                                           configurations, sha3_dict2, sha3_values2, search_op,
                                                           search_function, jumpdepth + 1, calldepth, function_hash,
                                                           find_solution, key)
                                    MyGlobals.search_condition_found = False
                                    self.path = deepcopy(path_back_up)
                                    if is_new_call:
                                        MyGlobals.call_vars = call_vars
                                    MyGlobals.m.rs_temp, MyGlobals.m.ws_temp, MyGlobals.m.rs_temp_id, MyGlobals.m.ws_temp_id, MyGlobals.m.rwaddr2id = rs_temp, ws_temp, rs_temp_id, ws_temp_id, rwaddr2id

                                    MyGlobals.addr_read = copy.deepcopy(addr_read2)
                                    MyGlobals.addr_write = copy.deepcopy(addr_write2)
                                    if MyGlobals.reach_stage ==key== 2 and len(MyGlobals.stack2_all)>1:MyGlobals.stack2=MyGlobals.stack2_all.pop();MyGlobals.mmemory_stack2=MyGlobals.mmemory_stack2_all.pop();MyGlobals.storage_stack2=MyGlobals.storage_stack2_all.pop()
                                    if MyGlobals.jumpi_switch: MyGlobals.jumpi_switch = False

                                else:
                                    time2 = datetime.datetime.now()
                                    MyGlobals.total_time_solver += (time2 - time1).total_seconds()

                                MyGlobals.s.pop()
                        except Exception as e:
                            print("Exception: " + str(e))
                        if MyGlobals.reach_stage == key == 2 and satisfied:
                            MyGlobals.j_c.pop()



                    if MyGlobals.stop_search: return

                    #
                    # Branch when the decision is possibly correct
                    #
                    if not self.is_fixed(addr):
                        # for statistics
                        return False

                    jump_dest = self.get_value(addr)
                    if (jump_dest <= 0):
                        if self.debug: print(
                            '\033[95m[-] The jump destination is not a valid address : %x\033[0m' % jump_dest)
                        return False

                    new_position = find_pos(ops, jump_dest)
                    if (new_position < 0):
                        if self.debug: print(
                            '\033[95m[-] The code has no such jump destination: %s at line %x\033[0m' % (
                                hex(jump_dest), si['id']))
                        return False
                    if add_feasible_jump_constraints:
                        if MyGlobals.terminate_stage==3 and key==2:
                            p_dict_temp, p_list_temp = self.path2dict(2, 0, 0)
                            l = len(p_list_temp)
                            if len(MyGlobals.feasible_jumpdest[2]) > l:
                                if MyGlobals.feasible_jumpdest[2][:l] == p_list_temp:
                                    jump_start = MyGlobals.feasible_jumpdest[2][l]
                                    jump_des = MyGlobals.feasible_jumpdest[2][l + 1]
                                    if si['id'] == jump_start and ops[new_position]['id'] == jump_des:
                                        jump_decision = True
                                    else:
                                        jump_decision = False
                            else:
                                jump_decision=True
                        else:
                            if MyGlobals.feasible_jumpdest[key]:
                                jump_decision = si['id'] in MyGlobals.feasible_jumpdest[key] and ops[new_position]['id'] in \
                                            MyGlobals.feasible_jumpdest[key][si['id']]
                            else:
                                jump_decision=True

                    if jump_decision:
                        MyGlobals.s.push()
                        MyGlobals.new_branch = True

                        try:
                            if fallback_frame: return

                            # If already in sha3 and solution found do not branch
                            if MyGlobals.solution_found and MyGlobals.in_sha3 > 0:
                                MyGlobals.s.pop()
                                return

                            if self.search_enhance:
                                storage2 = copy.deepcopy(storage)
                                stack2 = copy.deepcopy(stack)
                                trace2 = copy.deepcopy(trace)
                                mmemory2 = copy.deepcopy(mmemory)
                                data2 = copy.deepcopy(data)
                                sha3_values2 = copy.deepcopy(sha3_values)
                                sha3_dict2 = copy.deepcopy(sha3_dict)

                                if MyGlobals.reach_stage ==key== 2:
                                    MyGlobals.stack2_all.append(deepcopy(MyGlobals.stack2))
                                    MyGlobals.mmemory_stack2_all.append(deepcopy(MyGlobals.mmemory_stack2))
                                    MyGlobals.storage_stack2_all.append(deepcopy(MyGlobals.storage_stack2))
                                if self.path.count((key, ops[pos]['id'], ops[new_position]['id'])) > self.allowed_cycle:
                                    return

                                path_back_up = deepcopy(self.path)
                                call_vars = deepcopy(MyGlobals.call_vars)
                                rs_temp, ws_temp, rs_temp_id, ws_temp_id, rwaddr2id = self.rw_back_up()

                                self.path.append((key, ops[pos]['id'], ops[new_position]['id']))
                                self.execute_one_block(ops, stack2, new_position, trace2, storage2, mmemory2, data2,
                                                       configurations, sha3_dict2, sha3_values2, search_op, search_function,
                                                       jumpdepth, calldepth, function_hash, find_solution, key)
                                self.path=deepcopy(path_back_up)
                                if is_new_call:
                                    MyGlobals.call_vars = call_vars
                                MyGlobals.m.rs_temp, MyGlobals.m.ws_temp, MyGlobals.m.rs_temp_id, MyGlobals.m.ws_temp_id, MyGlobals.m.rwaddr2id = rs_temp, ws_temp, rs_temp_id, ws_temp_id, rwaddr2id

                                MyGlobals.search_condition_found = False

                            else:

                                MyGlobals.num_solver_calls += 1
                                time1 = datetime.datetime.now()

                                self.s_except_last_eq.reset()
                                self.s_except_last_eq.set('timeout', 4000)
                                self.s_except_last_eq.add(MyGlobals.s.assertions())
                                add_additional_conditions(self.s_except_last_eq, sha3_values)
                                self.last_eq = deepcopy(des['z3'] == 0)
                                self.pos_last_jumpi = ops[pos]['id']
                                self.pos_last_jumpi_other_dir = ops[pos]['id'] + 1
                                exp_temp = des['z3'] == 1
                                self.s_except_last_eq.push()
                                self.s_except_last_eq.add(exp_temp)
                                checked_Res = self.s_except_last_eq.check()
                                self.s_except_last_eq.pop()
                                satisfied = False

                                if checked_Res == sat:

                                    MyGlobals.s.add(des['z3'] != 0)
                                    if MyGlobals.reach_stage == key == 2:
                                        MyGlobals.j_c.append(des2['z3'] != 0)
                                    satisfied = True
                                elif str(checked_Res) == 'unknown':
                                    text = str(des['z3'])
                                    regex = re.compile('CALLVALUE-[1-2]-[0-9a-f]{8}')
                                    match = re.search(regex, text)
                                    if match:
                                        sm = text[match.start():match.end()]
                                        if MyGlobals.s.check() == sat:
                                            m = MyGlobals.s.model()
                                            callv = BitVec(sm, 256)
                                            if str(callv) in str(m):
                                                if m[callv].as_long()==0 and "'payable': True" in str(MyGlobals.func_hash2abi[function_hash]):
                                                    v=random.randint(0,1000)

                                                else:
                                                    v=m[callv].as_long()

                                                des_copy = deepcopy(des)
                                                des_copy['z3']=simplify(substitute(des_copy['z3'], (callv, BitVecVal(v,256))))
                                                if MyGlobals.reach_stage == key == 2:
                                                    des2_copy = deepcopy(des2)
                                                    des2_copy['z3']=simplify(substitute(des2_copy['z3'], (callv, BitVecVal(v,256))))
                                                    MyGlobals.j_c.append(des2['z3'] != 0)
                                                MyGlobals.s.add(des_copy['z3'] != 0)

                                                storage2 = copy.deepcopy(storage)
                                                stack2 = copy.deepcopy(stack)
                                                trace2 = copy.deepcopy(trace)
                                                mmemory2 = copy.deepcopy(mmemory)
                                                data2 = copy.deepcopy(data)
                                                sha3_values2 = copy.deepcopy(sha3_values)
                                                sha3_dict2 = copy.deepcopy(sha3_dict)

                                                self.concretize(stack2, mmemory2, sm, v)
                                                sha3_values2[sm] = []
                                                sha3_values2[sm].append(v)

                                                if MyGlobals.reach_stage == key == 2:
                                                    MyGlobals.stack2_all.append(deepcopy(MyGlobals.stack2))
                                                    MyGlobals.mmemory_stack2_all.append(deepcopy(MyGlobals.mmemory_stack2))
                                                    MyGlobals.storage_stack2_all.append(deepcopy(MyGlobals.storage_stack2))

                                                path_back_up = deepcopy(self.path)
                                                rs_temp,ws_temp,rs_temp_id,ws_temp_id,rwaddr2id= self.rw_back_up()
                                                call_vars = deepcopy(MyGlobals.call_vars)
                                                self.path.append((key, ops[pos]['id'], ops[new_position]['id']))
                                                self.execute_one_block(ops, stack2, new_position, trace2, storage2, mmemory2,data2,
                                                                       configurations, sha3_dict2, sha3_values2, search_op,
                                                                       search_function, jumpdepth + 1, calldepth,function_hash,
                                                                       find_solution, key)

                                                self.path = deepcopy(path_back_up)

                                                if is_new_call:
                                                    MyGlobals.call_vars = call_vars
                                                MyGlobals.m.rs_temp, MyGlobals.m.ws_temp, MyGlobals.m.rs_temp_id, MyGlobals.m.ws_temp_id, MyGlobals.m.rwaddr2id = rs_temp, ws_temp, rs_temp_id, ws_temp_id, rwaddr2id

                                                if MyGlobals.reach_stage == key == 2 and len(
                                                        MyGlobals.stack2_all) > 1: MyGlobals.stack2 = MyGlobals.stack2_all.pop();MyGlobals.mmemory_stack2 = MyGlobals.mmemory_stack2_all.pop();MyGlobals.storage_stack2 = MyGlobals.storage_stack2_all.pop()

                                    satisfied = False
                                else:
                                    satisfied = False

                                if satisfied:
                                    time2 = datetime.datetime.now()
                                    MyGlobals.total_time_solver += (time2 - time1).total_seconds()

                                    storage2 = copy.deepcopy(storage)
                                    stack2 = copy.deepcopy(stack)
                                    trace2 = copy.deepcopy(trace)
                                    mmemory2 = copy.deepcopy(mmemory)
                                    data2 = copy.deepcopy(data)
                                    sha3_values2 = copy.deepcopy(sha3_values)
                                    sha3_dict2 = copy.deepcopy(sha3_dict)
                                    addr_read2 = copy.deepcopy(MyGlobals.addr_read)
                                    addr_write2 = copy.deepcopy(MyGlobals.addr_write)

                                    if MyGlobals.reach_stage ==key== 2:
                                        MyGlobals.stack2_all.append(deepcopy(MyGlobals.stack2))
                                        MyGlobals.mmemory_stack2_all.append(deepcopy(MyGlobals.mmemory_stack2))
                                        MyGlobals.storage_stack2_all.append(deepcopy(MyGlobals.storage_stack2))

                                    if self.path.count((key, ops[pos]['id'], ops[new_position]['id'])) > self.allowed_cycle:
                                        return
                                    path_back_up = deepcopy(self.path)
                                    call_vars = deepcopy(MyGlobals.call_vars)
                                    rs_temp, ws_temp, rs_temp_id, ws_temp_id, rwaddr2id = self.rw_back_up()
                                    self.path.append((key, ops[pos]['id'], ops[new_position]['id']))
                                    self.execute_one_block(ops, stack2, new_position, trace2, storage2, mmemory2, data2,
                                                           configurations, sha3_dict2, sha3_values2, search_op,
                                                           search_function, jumpdepth, calldepth, function_hash,
                                                           find_solution, key)
                                    MyGlobals.search_condition_found = False
                                    self.path = deepcopy(path_back_up)
                                    if is_new_call:
                                        MyGlobals.call_vars = call_vars
                                    MyGlobals.m.rs_temp, MyGlobals.m.ws_temp, MyGlobals.m.rs_temp_id, MyGlobals.m.ws_temp_id, MyGlobals.m.rwaddr2id = rs_temp, ws_temp, rs_temp_id, ws_temp_id, rwaddr2id

                                    MyGlobals.addr_read = copy.deepcopy(addr_read2)
                                    MyGlobals.addr_write = copy.deepcopy(addr_write2)
                                    if MyGlobals.reach_stage ==key== 2 and len(MyGlobals.stack2_all)>1: MyGlobals.stack2 = MyGlobals.stack2_all.pop();MyGlobals.mmemory_stack2=MyGlobals.mmemory_stack2_all.pop();MyGlobals.storage_stack2=MyGlobals.storage_stack2_all.pop()

                                    if MyGlobals.jumpi_switch: MyGlobals.jumpi_switch = False

                                else:
                                    time2 = datetime.datetime.now()
                                    MyGlobals.total_time_solver += (time2 - time1).total_seconds()


                        except Exception as e:
                            print("Exception: " + str(e))

                        MyGlobals.s.pop()
                        if MyGlobals.reach_stage ==key== 2 and satisfied:
                            MyGlobals.j_c.pop()

                    return

                # It can be CALLDATALOAD
                elif si['o'] == 'CALLDATALOAD':

                    addr = stack.pop()
                    if MyGlobals.reach_stage==key==2: MyGlobals.stack2.pop()

                    # First find the symbolic variable name 'input[0-9]*\[[0-9 ]*\]-[0-9a-f]{8}'
                    text = str(addr['z3'])
                    regex = re.compile('input[0-9]*\[[0-9 ]*\]-[0-9a-f]{8}')
                    match = re.search(regex, text)
                    if match:
                        sm = text[match.start():match.end()]

                        # assign random (offset) address as value for the variable
                        random_address = get_hash(sm) >> 64

                        r2 = re.compile('\[[0-9 ]*\]')
                        indmat = re.search(r2, sm)
                        index = -2
                        if indmat:
                            index = int(sm[indmat.start() + 1:indmat.end() - 1])

                        total_added_to_solver = 0

                        # add 'd' at the end of the name of the symbolic variable (used later to distinguish them)
                        if index >= 0 and ('data-' + str(calldepth) + '-' + str(index) + '-' + str(
                                actual_key) + '-' + function_hash) in data:
                            data[('data-' + str(calldepth) + '-' + str(index) + '-' + str(
                                actual_key) + '-' + function_hash)] = BitVec(sm + 'd', 256)
                            MyGlobals.s.push();
                            MyGlobals.new_branch = True
                            MyGlobals.s.add(data[('data-' + str(calldepth) + '-' + str(index) + '-' + str(
                                actual_key) + '-' + function_hash)] == random_address)
                            total_added_to_solver = 1

                        # replace the variable with concrete value in stack and memory
                        for st in stack:
                            if 'z3' in st:
                                st['z3'] = simplify(
                                    substitute(st['z3'], (BitVec(sm, 256), BitVecVal(random_address, 256))))
                        for st in mmemory:
                            if 'z3' in mmemory[st]:
                                mmemory[st]['z3'] = simplify(
                                    substitute(mmemory[st]['z3'], (BitVec(sm, 256), BitVecVal(random_address, 256))))

                        # replace in the address as well
                        addr = simplify(substitute(addr['z3'], (BitVec(sm, 256), BitVecVal(random_address, 256))))

                        # Branch
                        branch_array_size = [0, 1, 2]
                        for one_branch_size in branch_array_size:
                            # do not branch if solution found and in sha3
                            if MyGlobals.solution_found and MyGlobals.in_sha3 > 0:
                                for tempp in range(total_added_to_solver):
                                    MyGlobals.s.pop();

                                return

                            storage2 = copy.deepcopy(storage)
                            stack2 = copy.deepcopy(stack)
                            trace2 = copy.deepcopy(trace)
                            mmemory2 = copy.deepcopy(mmemory)
                            data2 = copy.deepcopy(data)
                            sha3_values2 = copy.deepcopy(sha3_values)
                            sha3_dict2 = copy.deepcopy(sha3_dict)

                            data2['data-' + str(actual_key) + '-' + str(addr) + '-' + function_hash] = BitVecVal(
                                one_branch_size, 256)
                            for i in range(one_branch_size):
                                data2['data-' + str(actual_key) + '-' + str(
                                    addr.as_long() + 32 + 32 * i) + '-' + function_hash] = BitVec(
                                    'input' + str(actual_key) + '[' + (
                                            '%s' % (addr.as_long() + 32 + 32 * i)) + ']' + '-' + function_hash, 256)
                            if MyGlobals.reach_stage ==key== 2:
                                MyGlobals.stack2_all.append(deepcopy(MyGlobals.stack2))
                                MyGlobals.stack2.append({'type': 'constant', 'step': ops[pos]['id'], 'z3': BitVecVal(one_branch_size, 256)})
                                MyGlobals.mmemory_stack2_all.append(deepcopy(MyGlobals.mmemory_stack2))
                                MyGlobals.storage_stack2_all.append(deepcopy(MyGlobals.storage_stack2))

                            stack2.append({'type': 'constant', 'step': ops[pos]['id'], 'z3': BitVecVal(one_branch_size, 256)})


                            MyGlobals.s.push();
                            MyGlobals.new_branch = True
                            MyGlobals.s.add(
                                BitVec('input' + str(actual_key) + ('[%x' % addr.as_long()) + ']' + '-' + function_hash,
                                       256) == one_branch_size)

                            self.execute_one_block(ops, stack2, pos + 1, trace2, storage2, mmemory2, data2,
                                                   configurations, sha3_dict2, sha3_values2, search_op, search_function,
                                                   jumpdepth, calldepth, function_hash, find_solution, key)
                            MyGlobals.search_condition_found = False
                            MyGlobals.s.pop();

                            if MyGlobals.reach_stage ==key== 2 and len(MyGlobals.stack2_all)>1: MyGlobals.stack2 = MyGlobals.stack2_all.pop();MyGlobals.mmemory_stack2=MyGlobals.mmemory_stack2_all.pop();MyGlobals.storage_stack2=MyGlobals.storage_stack2_all.pop()


                        for ta in range(total_added_to_solver):
                            MyGlobals.s.pop()
                    else:
                        if self.debug:
                            print(
                                '\033[95m[-] In CALLDATALOAD the address does not contain symbolic variable input[*]\033[0m')
                        return

                    return


                # It can be CALLDATASIZE
                elif si['o'] == 'CALLDATASIZE':
                    if function_hash in ['11111111','22222222']:
                        stack.append({'type': 'constant', 'step': ops[pos]['id'],
                                       'z3':BitVecVal(0,256)})
                        if MyGlobals.reach_stage == key == 2:
                            MyGlobals.stack2.append({'type': 'constant', 'step': ops[pos]['id'],
                                           'z3':BitVecVal(0,256)})
                        newpos+=1
                    elif function_hash in MyGlobals.sz:
                        stack.append({'type': 'constant', 'step': ops[pos]['id'],
                                      'z3': BitVecVal(MyGlobals.sz[function_hash], 256)})
                        if MyGlobals.reach_stage == key == 2:
                            MyGlobals.stack2.append({'type': 'constant', 'step': ops[pos]['id'],
                                          'z3': BitVecVal(MyGlobals.sz[function_hash], 256)})
                        newpos+=1
                    else:
                        # Assume it is SYMBOLIC variable
                        storage2 = copy.deepcopy(storage)
                        stack2 = copy.deepcopy(stack)
                        trace2 = copy.deepcopy(trace)
                        mmemory2 = copy.deepcopy(mmemory)
                        data2 = copy.deepcopy(data)
                        sha3_values2 = copy.deepcopy(sha3_values)
                        sha3_dict2 = copy.deepcopy(sha3_dict)

                        if -1 not in data2:
                            data2['inputlength-' + str(actual_key) + '-' + function_hash] = BitVec(
                                'inputlength-' + str(actual_key) + '-' + function_hash, 256)
                        if MyGlobals.reach_stage ==key== 2:
                            MyGlobals.stack2_all.append(deepcopy(MyGlobals.stack2))
                            MyGlobals.stack2.append({'type': 'constant', 'step': ops[pos]['id'],'z3': data2['inputlength-' + str(actual_key) + '-' + function_hash]})
                            MyGlobals.mmemory_stack2_all.append(deepcopy(MyGlobals.mmemory_stack2))
                            MyGlobals.storage_stack2_all.append(deepcopy(MyGlobals.storage_stack2))

                        stack2.append({'type': 'constant', 'step': ops[pos]['id'],'z3': data2['inputlength-' + str(actual_key) + '-' + function_hash]})


                        MyGlobals.s.push();
                        MyGlobals.new_branch = True
                        MyGlobals.s.append(
                            If(data2['inputlength-' + str(actual_key) + '-' + function_hash] > BitVecVal(0, 256),
                               BitVecVal(1, 256), BitVecVal(0, 256)) == BitVecVal(1, 256))

                        self.execute_one_block(ops, stack2, pos + 1, trace2, storage2, mmemory2, data2, configurations,
                                               sha3_dict2, sha3_values2, search_op, search_function, jumpdepth, calldepth,
                                               function_hash, find_solution, key)
                        MyGlobals.s.pop();

                        if MyGlobals.reach_stage ==key== 2 and len(MyGlobals.stack2_all)>1: MyGlobals.stack2 = MyGlobals.stack2_all.pop();MyGlobals.mmemory_stack2=MyGlobals.mmemory_stack2_all.pop();MyGlobals.storage_stack2=MyGlobals.storage_stack2_all.pop()



                        if self.search_enhance and MyGlobals.stop_search:
                            return
                        MyGlobals.search_condition_found = False

                        # or Branch on 4 different FIXED sizes
                        # branch_array_size = [0,8,8+1*32,8+2*32]
                        branch_array_size = [8, 8 + 1 * 32, 8 + 2 * 32]
                        i = 0
                        for one_branch_size in branch_array_size:

                            if MyGlobals.solution_found and MyGlobals.in_sha3 > 0:
                                return

                            i += 1
                            storage2 = copy.deepcopy(storage)
                            stack2 = copy.deepcopy(stack)
                            trace2 = copy.deepcopy(trace)
                            mmemory2 = copy.deepcopy(mmemory)
                            data2 = copy.deepcopy(data)
                            sha3_values2 = copy.deepcopy(sha3_values)
                            sha3_dict2 = copy.deepcopy(sha3_dict)

                            if MyGlobals.reach_stage ==key== 2:
                                MyGlobals.stack2_all.append(deepcopy(MyGlobals.stack2))
                                MyGlobals.stack2.append({'type': 'constant', 'step': ops[pos]['id'], 'z3': BitVecVal(one_branch_size, 256)})
                                MyGlobals.mmemory_stack2_all.append(deepcopy(MyGlobals.mmemory_stack2))
                                MyGlobals.storage_stack2_all.append(deepcopy(MyGlobals.storage_stack2))

                            stack2.append({'type': 'constant', 'step': ops[pos]['id'], 'z3': BitVecVal(one_branch_size, 256)})

                            MyGlobals.s.push();
                            MyGlobals.new_branch = True


                            if self.debug: print('\033[91m In branch %x of Calldatasize\n \033[0m' % (i))
                            self.execute_one_block(ops, stack2, pos + 1, trace2, storage2, mmemory2, data2, configurations,
                                                   sha3_dict2, sha3_values2, search_op, search_function, jumpdepth,
                                                   calldepth, function_hash, find_solution, key)

                            MyGlobals.s.pop();
                            if MyGlobals.reach_stage ==key== 2 and len(MyGlobals.stack2_all)>1 : MyGlobals.stack2 = MyGlobals.stack2_all.pop();MyGlobals.mmemory_stack2=MyGlobals.mmemory_stack2_all.pop();MyGlobals.storage_stack2=MyGlobals.storage_stack2_all.pop()

                            MyGlobals.search_condition_found = False
                        return
                elif si['o'] == 'SHA3':

                    s1 = stack.pop()
                    s2 = stack.pop()
                    if MyGlobals.reach_stage == key == 2:
                        MyGlobals.stack2.pop()
                        MyGlobals.stack2.pop()

                    if self.is_fixed(s2):
                        addr = self.get_value(s2)

                    else:
                        print('Address not fixed in sha3\n')

                    exact_address = self.get_value(s1) if is_bv_value(s1['z3']) else -1
                    changed_offset = exact_address
                    if (addr - exact_address) // 32 >= 2: changed_offset = addr // 2

                    if self.search_enhance:
                        if not self.is_fixed(mmemory[changed_offset]):
                            res = {'type': 'constant', 'step': ops[pos]['id'], 'z3': mmemory[changed_offset]['z3']}

                        else:
                            res = {'type': 'constant', 'step': ops[pos]['id'],
                                   'z3': BitVec('SHA3' + '-' + str(ops[pos]['id']) + '-' + function_hash, 256)}
                        stack.append(res)
                        newpos = pos + 1
                        continue

                    text = str(mmemory[self.get_value(s1)]['z3'])

                    if 'CALLER' in text:

                        # Find the exact name of symbolic variable.
                        sm = ''
                        regex = re.compile('CALLER-[0-9]-[0-9a-f]{8}')
                        match = re.search(regex, text)

                        if match:
                            sm = text[match.start():match.end()]
                        else:
                            print('\033[91m[-] NO such symbolic variable found \033[0m', '\n')
                            return

                        # If values of the symbolic variable have already been defined
                        if sm in sha3_values:
                            if self.debug: print('In branch 1 \n')

                            const_addr = sha3_values[sm][0]
                            mmemory[self.get_value(s1)]['z3'] = BitVecVal(const_addr, 256)

                            # find the keccak hash of the new concrete value
                            val = ''

                            for i in range(addr // 32):
                                val += '%064x' % self.get_value(mmemory[self.get_value(s1) + i * 32])

                            k = keccak_256()
                            k.update(codecs.decode(val, 'hex'))
                            digest = k.hexdigest()
                            res = {'type': 'constant', 'step': ops[pos]['id'],
                                   'z3': BitVecVal(int(digest, 16), 256)}
                            if addr // 32==2:
                                MyGlobals.m.sha_v2slot[int(digest, 16)]=[self.get_value(mmemory[self.get_value(s1)]),self.get_value(mmemory[self.get_value(s1) +  32])]

                            # Copy all the contents of the previous sha3 dict and sha3_values
                            sha3_dict2 = copy.deepcopy(sha3_dict)
                            sha3_values2 = copy.deepcopy(sha3_values)
                            sha3_dict2[mmemory[addr // 2]['z3'].as_long()] = []
                            sha3_dict2[mmemory[addr // 2]['z3'].as_long()].append(const_addr)
                            # Copy all the datastructures
                            storage2 = copy.deepcopy(storage)
                            stack2 = copy.deepcopy(stack)
                            trace2 = copy.deepcopy(trace)
                            mmemory2 = copy.deepcopy(mmemory)
                            data2 = copy.deepcopy(data)
                            addr_read2=copy.deepcopy(MyGlobals.addr_read)
                            addr_write2=copy.deepcopy(MyGlobals.addr_write)
                            if MyGlobals.reach_stage == key == 2:
                                MyGlobals.stack2_all.append(deepcopy(MyGlobals.stack2))
                                MyGlobals.stack2.append(res);
                                MyGlobals.mmemory_stack2_all.append(deepcopy(MyGlobals.mmemory_stack2))
                                MyGlobals.storage_stack2_all.append(deepcopy(MyGlobals.storage_stack2))

                            stack2.append(res)

                            # Activate the sha3 branch
                            MyGlobals.in_sha3 += 1
                            MyGlobals.solution_found = False

                            MyGlobals.s.push()
                            MyGlobals.new_branch = True
                            call_vars = deepcopy(MyGlobals.call_vars)
                            self.execute_one_block(ops, stack2, pos + 1, trace2, storage2, mmemory2, data2,
                                                   configurations, sha3_dict2, sha3_values2, search_op,
                                                   search_function, jumpdepth, calldepth, function_hash,
                                                   find_solution, key)
                            MyGlobals.call_vars = call_vars
                            MyGlobals.s.pop()
                            MyGlobals.addr_read=copy.deepcopy(addr_read2)
                            MyGlobals.addr_write=copy.deepcopy(addr_write2)
                            if MyGlobals.reach_stage == key == 2 and len(MyGlobals.stack2_all) > 1:
                                MyGlobals.stack2 = MyGlobals.stack2_all.pop()
                                MyGlobals.mmemory_stack2 = MyGlobals.mmemory_stack2_all.pop()
                                MyGlobals.storage_stack2 = MyGlobals.storage_stack2_all.pop()
                            MyGlobals.search_condition_found = False

                            # Deactivate the sha3 branch
                            MyGlobals.in_sha3 -= 1

                        # If values of the symbolic variable have not been defined
                        else:
                            if self.debug: print('In branch 2 \n')

                            value_list = MyGlobals.st['caller']
                            if not '0x1' in value_list:
                                value_list.append('0x1')
                            for each_value in value_list:

                                const_addr = (int(each_value, 16))
                                found = False
                                # replace the symbolic variable with a concrete variable
                                mmemory[self.get_value(s1)]['z3'] = BitVecVal(const_addr, 256)
                                # find the keccak hash of the new concrete value
                                val = ''

                                for i in range(addr // 32):
                                    val += '%064x' % self.get_value(mmemory[self.get_value(s1) + i * 32])

                                k = keccak_256()
                                k.update(codecs.decode(val, 'hex'))
                                digest = k.hexdigest()
                                res = {'type': 'constant', 'step': ops[pos]['id'],
                                       'z3': BitVecVal(int(digest, 16), 256)}
                                if addr // 32 == 2:
                                    MyGlobals.m.sha_v2slot[int(digest, 16)] = [
                                        self.get_value(mmemory[self.get_value(s1)]),
                                        self.get_value(mmemory[self.get_value(s1) + 32])]

                                # Copy all the contents of the previous sha3 dict and sha3_values
                                sha3_dict2 = copy.deepcopy(sha3_dict)
                                sha3_values2 = copy.deepcopy(sha3_values)
                                sha3_dict2[mmemory[addr // 2]['z3'].as_long()] = []
                                sha3_dict2[mmemory[addr // 2]['z3'].as_long()].append(const_addr)
                                sha3_values2[sm] = []
                                sha3_values2[sm].append(const_addr)

                                storage2 = copy.deepcopy(storage)
                                stack2 = copy.deepcopy(stack)
                                trace2 = copy.deepcopy(trace)
                                mmemory2 = copy.deepcopy(mmemory)
                                data2 = copy.deepcopy(data)
                                addr_read2 = copy.deepcopy(MyGlobals.addr_read)
                                addr_write2 = copy.deepcopy(MyGlobals.addr_write)
                                if MyGlobals.reach_stage == key == 2:
                                    MyGlobals.stack2_all.append(deepcopy(MyGlobals.stack2))
                                    MyGlobals.stack2.append(res)
                                    MyGlobals.mmemory_stack2_all.append(deepcopy(MyGlobals.mmemory_stack2))
                                    MyGlobals.storage_stack2_all.append(deepcopy(MyGlobals.storage_stack2))

                                stack2.append(res)

                                # Activate the sha3 branch
                                MyGlobals.in_sha3 += 1
                                MyGlobals.solution_found = False

                                MyGlobals.s.push();
                                MyGlobals.new_branch = True
                                call_vars = deepcopy(MyGlobals.call_vars)
                                self.execute_one_block(ops, stack2, pos + 1, trace2, storage2, mmemory2, data2,
                                                       configurations, sha3_dict2, sha3_values2, search_op,
                                                       search_function, jumpdepth, calldepth, function_hash,
                                                       find_solution, key)
                                MyGlobals.call_vars = call_vars
                                MyGlobals.s.pop();
                                MyGlobals.addr_read = copy.deepcopy(addr_read2)
                                MyGlobals.addr_write = copy.deepcopy(addr_write2)
                                if MyGlobals.reach_stage == key == 2 and len(MyGlobals.stack2_all) > 1:
                                    MyGlobals.stack2 = MyGlobals.stack2_all.pop()
                                    MyGlobals.mmemory_stack2 = MyGlobals.mmemory_stack2_all.pop()
                                    MyGlobals.storage_stack2 = MyGlobals.storage_stack2_all.pop()

                                # Deactivate the sha3 branch
                                MyGlobals.in_sha3 -= 1

                                MyGlobals.search_condition_found = False

                    if 'input' in text:

                        # Find the exact name of symbolic variable.
                        sm = ''
                        regex = re.compile('input[0-9]*\[[0-9 ]*\]-[0-9a-f]{8}')
                        match = re.search(regex, text)

                        if match:
                            sm = text[match.start():match.end()]
                        else:
                            print('\033[91m[-] No such symbolic variable found \033[0m', '\n')
                            return

                        # If values of the symbolic variable have already been defined
                        if sm in sha3_values:
                            if self.debug: print('In branch 3 \n')
                            const_addr = sha3_values[sm][0]
                            mmemory[self.get_value(s1)]['z3'] = BitVecVal(const_addr, 256)

                            # find the keccak hash of the new concrete value
                            val = ''

                            for i in range(addr // 32):
                                val += '%064x' % self.get_value(mmemory[self.get_value(s1) + i * 32])

                            k = keccak_256()
                            k.update(codecs.decode(val, 'hex'))
                            digest = k.hexdigest()
                            res = {'type': 'constant', 'step': ops[pos]['id'],
                                   'z3': BitVecVal(int(digest, 16), 256)}
                            if addr // 32 == 2:
                                MyGlobals.m.sha_v2slot[int(digest, 16)] = [self.get_value(mmemory[self.get_value(s1)]),
                                                                           self.get_value(
                                                                               mmemory[self.get_value(s1) + 32])]
                            # Copy all the contents of the previous sha3 dict and sha3_values
                            sha3_dict2 = copy.deepcopy(sha3_dict)
                            sha3_values2 = copy.deepcopy(sha3_values)
                            sha3_dict2[mmemory[addr // 2]['z3'].as_long()] = []
                            sha3_dict2[mmemory[addr // 2]['z3'].as_long()].append(const_addr)
                            # Copy all the datastructures
                            storage2 = copy.deepcopy(storage)
                            stack2 = copy.deepcopy(stack)
                            trace2 = copy.deepcopy(trace)
                            mmemory2 = copy.deepcopy(mmemory)
                            data2 = copy.deepcopy(data)
                            addr_read2=copy.deepcopy(MyGlobals.addr_read)
                            addr_write2=copy.deepcopy(MyGlobals.addr_write)
                            if MyGlobals.reach_stage == key == 2:
                                MyGlobals.stack2_all.append(deepcopy(MyGlobals.stack2))
                                MyGlobals.stack2.append(res)
                                MyGlobals.mmemory_stack2_all.append(deepcopy(MyGlobals.mmemory_stack2))
                                MyGlobals.storage_stack2_all.append(deepcopy(MyGlobals.storage_stack2))

                            stack2.append(res)

                            # Activate the sha3 branch
                            MyGlobals.in_sha3 += 1
                            MyGlobals.solution_found = False

                            MyGlobals.s.push();
                            MyGlobals.new_branch = True
                            call_vars = deepcopy(MyGlobals.call_vars)
                            self.execute_one_block(ops, stack2, pos + 1, trace2, storage2, mmemory2, data2,
                                                   configurations, sha3_dict2, sha3_values2, search_op,
                                                   search_function, jumpdepth, calldepth, function_hash,
                                                   find_solution, key)
                            MyGlobals.call_vars = call_vars
                            MyGlobals.s.pop();
                            MyGlobals.addr_read=copy.deepcopy(addr_read2)
                            MyGlobals.addr_write=copy.deepcopy(addr_write2)
                            if MyGlobals.reach_stage == key == 2 and len(MyGlobals.stack2_all) > 1:
                                MyGlobals.stack2 = MyGlobals.stack2_all.pop();
                                MyGlobals.mmemory_stack2 = MyGlobals.mmemory_stack2_all.pop();
                                MyGlobals.storage_stack2 = MyGlobals.storage_stack2_all.pop()
                            MyGlobals.search_condition_found = False
                            # Deactivate the sha3 branch
                            MyGlobals.in_sha3 -= 1

                        # If values of the symbolic variable have not been defined
                        else:
                            if self.debug: print('In branch 4 \n')
                            lists = []
                            value_list = MyGlobals.st['caller']
                            if not '0x1' in value_list:
                                value_list.append('0x1')
                            for index in range(5):
                                ind=4+index*32
                                if str(ind) in sm[:10]:
                                    if ind in MyGlobals.input_types[function_hash]:
                                        if  "uint" in MyGlobals.input_types[function_hash][ind]:
                                            value_list=["0x1"]
                                            break

                            for each_value in value_list:
                                lists.append(int(each_value, 16))

                            shuffle(lists)

                            for value in lists:
                                const_addr = value
                                found = False
                                # replace the symbolic variable with a concrete variable
                                mmemory[self.get_value(s1)]['z3'] = BitVecVal(const_addr, 256)
                                # find the keccak hash of the new concrete value
                                val = ''

                                for i in range(addr // 32):
                                    val += '%064x' % self.get_value(mmemory[self.get_value(s1) + i * 32])

                                k = keccak_256()
                                k.update(codecs.decode(val, 'hex'))
                                digest = k.hexdigest()
                                res = {'type': 'constant', 'step': ops[pos]['id'],
                                       'z3': BitVecVal(int(digest, 16), 256)}
                                if addr // 32 == 2:
                                    MyGlobals.m.sha_v2slot[int(digest, 16)] = [
                                        self.get_value(mmemory[self.get_value(s1)]),
                                        self.get_value(mmemory[self.get_value(s1) + 32])]
                                # Copy all the contents of the previous sha3 dict and sha3_values
                                sha3_dict2 = copy.deepcopy(sha3_dict)
                                sha3_values2 = copy.deepcopy(sha3_values)
                                sha3_dict2[mmemory[addr // 2]['z3'].as_long()] = []
                                sha3_dict2[mmemory[addr // 2]['z3'].as_long()].append(const_addr)
                                sha3_values2[sm] = []
                                sha3_values2[sm].append(const_addr)
                                addr_read2 = copy.deepcopy(MyGlobals.addr_read)
                                addr_write2 = copy.deepcopy(MyGlobals.addr_write)
                                storage2 = copy.deepcopy(storage)
                                stack2 = copy.deepcopy(stack)
                                trace2 = copy.deepcopy(trace)
                                mmemory2 = copy.deepcopy(mmemory)
                                data2 = copy.deepcopy(data)

                                if MyGlobals.reach_stage == key == 2:
                                    MyGlobals.stack2_all.append(deepcopy(MyGlobals.stack2))
                                    MyGlobals.stack2.append(deepcopy(res))
                                    MyGlobals.mmemory_stack2_all.append(deepcopy(MyGlobals.mmemory_stack2))
                                    MyGlobals.storage_stack2_all.append(deepcopy(MyGlobals.storage_stack2))

                                stack2.append(res)

                                # Activate the sha3 branch
                                MyGlobals.in_sha3 += 1
                                MyGlobals.solution_found = False

                                MyGlobals.s.push();
                                MyGlobals.new_branch = True
                                call_vars = deepcopy(MyGlobals.call_vars)
                                self.execute_one_block(ops, stack2, pos + 1, trace2, storage2, mmemory2, data2,
                                                       configurations, sha3_dict2, sha3_values2, search_op,
                                                       search_function, jumpdepth, calldepth, function_hash,
                                                       find_solution, key)
                                MyGlobals.call_vars = call_vars
                                MyGlobals.s.pop();
                                MyGlobals.addr_read = copy.deepcopy(addr_read2)
                                MyGlobals.addr_write = copy.deepcopy(addr_write2)
                                if MyGlobals.reach_stage == key == 2 and len(MyGlobals.stack2_all) > 1:
                                    MyGlobals.stack2 = MyGlobals.stack2_all.pop();MyGlobals.mmemory_stack2 = MyGlobals.mmemory_stack2_all.pop();MyGlobals.storage_stack2 = MyGlobals.storage_stack2_all.pop()
                                MyGlobals.search_condition_found = False

                                # Deactivate the sha3 branch
                                MyGlobals.in_sha3 -= 1


                    if MyGlobals.in_sha3 == 0:
                        MyGlobals.solution_found = False
                    return

                # If nothing from above then stop
                else:
                    print('\033[95m[-] Unknown %s on line %x \033[0m' % (si['o'], ops[pos]['id']))
                    return
