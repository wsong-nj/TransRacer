from __future__ import print_function
import sys
sys.path.insert(0, '../pkgs')
from global_vars import MyGlobals
from hashlib import *
from z3 import *
from sha3 import *
import opcodes
import script
import json
import execute_instruction
import datetime
import sqlite3
import subprocess
import shlex
import re
import time
from copy import deepcopy
from web3 import Web3
from global_vars import get_storage_value,get_params,set_params,print_params,is_params


''' 
Debug API: All the print functions below are used for pretty-printing/debugginga
'''

# Print execution stack during runtime.
def print_stack(stack):
	print('\033[90m------------------------------------- STACK -------------------------------------')
	for s in stack[::-1]:
		if 'z3' in s:
			if is_bv_value( simplify(s['z3'])): print('%10s : %4x  : %x' % (s['type'],s['step'],simplify(s['z3']).as_long() ) )
			else: print('%10s : %4x  : %s' % (s['type'],s['step'], simplify(s['z3']) ) )
		else:
			print('%10s : %4x  ' % (s['type'],s['step']) )
	print('\033[0m')

# Print global storage of the contract during runtime
def print_storage(storage):
	print('************************************ STORAGE ************************************')
	for fl in storage:
		for s in storage[fl]:
			print('\033[91m[ %64x ] \033[0m : ' % (fl), end='' )        
			if is_bv_value( simplify(s['z3'])): print('%x' % (simplify(s['z3']).as_long() ) )
			else: print('%s' % (simplify(s['z3']) ) )

# Print memory of the contract during runtime.
def print_memory(mmemory):
	print('************************************ MEMORY ************************************')
	for m in mmemory:
		fl = mmemory[m]
		print('\033[91m[ %64x ] \033[0m : ' % (m), end='' )        
		if execute_instruction.is_undefined(fl): print('undefined' )
		elif is_bv_value( simplify(fl['z3'])): print('%x' % (simplify(fl['z3']).as_long() ) )
		else: print('%s' % (simplify(fl['z3']) ) )            

# Print sha3_dict which is used in SHA3 opcode implementation. (Debugging purpose)		
def print_sha3(sha3_dict):
	print('************************************ SHA3 addresses ************************************')
	for m in sha3_dict:
		fl = sha3_dict[m]
		print('\033[91m[ %64x ] \033[0m : ' % (m), end='' )        
		for each in fl:
			if isinstance(each, int):
				print(hex(each).rstrip('L').lstrip('0x') + ' ,')
			
# Print sha3_values which is used in SHA3 opcode implementation. (Debugging purpose)		
def print_sha3_values(sha3_values):
	print('************************************ SHA3 concrete values ************************************')
	for m in sha3_values:
		fl = sha3_values[m]
		print('\033[91m[ %64s ] \033[0m : ' % (m), end='' )        
		for each in fl:
			print(hex(each).rstrip('L').lstrip('0x') + ' ,')

# Print the execution trace.
def print_trace(trace):

	print('++++++++++++++++++++++++++++ Trace ++++++++++++++++++++++++++++')
	for o in trace:
		print('%6x  : %2s : %12s : %s' % (o['id'],o['op'],o['o'] , o['input']) )

# Print contract function names.
def print_function_name(funclist, f=False):
	if not f:
		print('++++++++++++++++++++++++++++ Functions List ++++++++++++++++++++++++++++')
		for function_name, funchash in funclist:
			print('%s %30s : %8s' % (function_name, '\t', funchash) )   

	else:
		f.write('++++++++++++++++++++++++++++ Functions List ++++++++++++++++++++++++++++'+'\n')
		for function_name, funchash in funclist:
			f.write('%s %30s : %8s' % (function_name, '\t', funchash) + '\n')           

# Print the final solution in the raw form {(symbolic variable, value),}
def print_solution(function1, function2, fn1, fn2, sol_dict):

	print('\033[92m ******************* HB: %s , %s : %s , %s  \033[92m *******************\033[0m' % (fn1, fn2, function1, function2))
	
	for key, mydict in sol_dict.items():

		print('\033[93mSolution %s : \033[0m'%(str(key)))
		for each, value in mydict.items():
			print('\nContext for \033[92m %s \033[0m'%(str(each)))

			for lists in value:
				print('%-20s : %s' % (lists[0],str(lists[1])) )

# Print the final nodes output by static analysis.
def print_nodes(nodes, f = False):
	if not f:
		print('++++++++++++++++++++++++++++ Final Nodes ++++++++++++++++++++++++++++')
		for index, node in nodes.items():
		# for node in nodes:
			for func, ctx in node.items():
				print('\033[1m %s : %s \n \033[0m'%(str(index), func))
				for (key, value) in ctx:
					if isinstance(value, int):
						value = hex(value).rstrip('L').lstrip('0x')
					print(key, '%10s'%('\t'), '------->', value, '\n')

	else:
		f.write('++++++++++++++++++++++++++++ Final Nodes ++++++++++++++++++++++++++++'+'\n')
		for index, node in nodes.items():
		# for node in nodes:
			for func, ctx in node.items():
				f.write('%s : %s \n'%(str(index), func)+'\n')
				for (key, value) in ctx:
					if isinstance(value, int):
						value = hex(value).rstrip('L').lstrip('0x')
					f.write(key + '%10s'%('\t')+ ' -------> ' + value + '\n')

# Print the final nodes output by static analysis. (just a variant of previous method used to extract final nodes from a list instead of a dictionary)
def print_nodes_list(nodes, f = False):
	if not f:
		print('++++++++++++++++++++++++++++ Final Nodes ++++++++++++++++++++++++++++')
		index = 0
		for node in nodes:
		# for node in nodes:
			print('\033[1m\n%s : %s  \033[0m'%(str(index), node['name']))
			for key, value in node.items():
				if not key == 'name':
					if isinstance(value, int):
						value = hex(value).rstrip('L').lstrip('0x')
					print('%-15s -------> %s' %(key, value) )
			index+=1		

	else:
		f.write('++++++++++++++++++++++++++++ Final Nodes ++++++++++++++++++++++++++++'+'\n')
		for node in nodes:

			f.write('%s : %s \n'%(str(index), node['name'])+'\n')
			for key, value in node.items():
				if not key == 'name':
					if isinstance(value, int):
						value = hex(value).rstrip('L').lstrip('0x')
					f.write(key + '%10s'%('\t')+ ' -------> ' + value + '\n')	

# Print if an instruction has not been implemented.
def print_notimplemented():
	for key, value in MyGlobals.notimplemented_ins.items():
		print(key + ' :: ' + str(value))			

# Used for debugging purposes.
def safe_subprocess(a1, a2, max_tries, wait_time):

	FNULL = open(os.devnull, 'w')
	try_no = 0
	while True:
		try:
			solc_p = subprocess.Popen(shlex.split(a1 % a2), stdout = subprocess.PIPE, stderr=FNULL)
		except Exception as e:
			print('Exception:', e)
			time.sleep(wait_time)
			try_no +=1
			if try_no >= max_tries:
				print('Cannot pass the exception')
				print('Called subprocess with args:',a1,a2)
				exit(1)
			continue
		break

	return solc_p


'''
Debug API ends.......
'''


'''
Helper functions 
'''

# converts a hexadecimal string to integer.
def convert_hexStr_to_int(hexStr):
	longNum = 0
	if isinstance(hexStr, str):
		longNum = int(hexStr, 16)
	
	return	int(longNum)

# converts an integer into a hexadecimal string.
def convert_int_to_hexStr(number):
	hexStr = ''
	if not isinstance(number, str):
		hexStr += hex(number)

	return hexStr.lstrip('0x').rstrip('L').zfill(40)

# remove the 0x from the string.
def remove0x(string):
	if string[0:2] == '0x':
		string = string[2:]
	
	return string

# This function is used to find blockumber from which the initial contract state has to be chosen.
# by default the state is taken from the blocknumber right after contract creation. If the variable owner_last 
# is set then the state is taken from blocknumber after all the initialization done by owner after conntract creation.
def find_blockNumber(contract_address, owner_last = False):
	dbcon = sqlite3.connect('/mnt/d/mnt_c/contract-main.db')

	# find the owner and contract creation block
	c_details = dbcon.execute('select creator, block from contracts where address='+'"%s"'%(contract_address))
	owner = ''
	c_blocknumber = 0

	for each in c_details:
		owner = each[0]
		c_blocknumber = each[1]

	last_block = c_blocknumber+1
	if owner_last:
		# Find the blocknember of the last owner transaction after creation.
		tx_details = dbcon.execute('select txfrom, block from tx where txto='+ '"%s"'%(contract_address) + ' order by block')

		for each_tx in tx_details:

			if owner == each_tx[0]:
				if each_tx[1] >= last_block: last_block = each_tx[1]
			else:
				break	

	return last_block+1		

# convert the solidity code into bytecode and then produce hashes
def getFuncHashes(sol_file, debug):

	solc_cmd = "solc --optimize --bin-runtime %s"
	solc_cmd1 = 'solc --hashes %s'
	FNULL = open(os.devnull, 'w')
	max_size = -1
	max_code = ''
	max_cname = ''
	
	# handle execption
	max_no_tries = 100
	try_no = 0
	solc_p = safe_subprocess ( solc_cmd , sol_file , 100, 1 )
	solc_out = solc_p.communicate()


	if debug: print(solc_out)


	for (cname, bin_str) in re.findall(r"\n======= (.*?) =======\nBinary of the runtime part: \n(.*?)\n", solc_out[0].decode('utf-8')):
		if len(bin_str)>max_size:
			max_size = len(bin_str)
			max_code = bin_str
			max_cname = cname

	funclist = []        

	try_no = 0
	solc_p1 = safe_subprocess( solc_cmd1 , sol_file, 100, 1 )
	solc_out1 = solc_p1.communicate()
	solc_str = solc_out1[0].decode('utf-8').lstrip('\n').rstrip('\n')

	if not solc_str=='':
		pass
	else:
		print('No solidity code in file\n')    				


	#
	# Get function names and  corresponding hashes with regular expression
	#
	hs = re.findall(r'^[a-fA-F0-9]{8}: .*\)', solc_str, flags=re.MULTILINE)
	for h in hs:
		ars = h.split(':')
		ars[0] = ars[0].replace(' ','')
		ars[1] = ars[1].replace(' ','')
		funclist.append( [ars[1],ars[0]])
	

	if debug: print(funclist)
	return funclist

# Computes hash of input
def get_hash(txt):
	k = md5()
	k.update(txt.encode('utf-8'))
	return int(k.hexdigest(),16)

# get the function hashes heuristically instead of using any solidity API.
def get_func_hashes(binfile):

	complete_disasm = script.disasm(binfile, 0)

	disasm = []

	for key, value in complete_disasm.items():
		disasm  = value[0]

	funclist = []
	for i in range(0, len(disasm)-4):
		if(disasm[i][1]=='PUSH4'):
			hexc = disasm[i][-1]
			if(disasm[i+2][1]=='EQ'):
				if('PUSH' in disasm[i+3][1]):
					if('JUMPI'==disasm[i+4][1]):
						funclist.append([i, hexc])
			elif(disasm[i+1][1]=='EQ'):
				if('PUSH' in disasm[i+2][1]):
					if('JUMPI'==disasm[i+3][1]):
						funclist.append([i-1, hexc])
	return funclist		

# returns True when a solution should be accepted. This function filters out the duplicate and unwanted solutions.
def solution_filter(solution, function1, function2):
	keys = []
	for key, value in solution.items():
		if 'inputlength' in key:
			keys.append(key)
		
	for each_key in keys:
		solution.pop(each_key, None)

	if not solution in MyGlobals.solution_dict[(function1, function2)] and len(MyGlobals.solution_dict[(function1, function2)]) < MyGlobals.max_solutions:

		if len(MyGlobals.solution_dict[(function1, function2)]) ==  MyGlobals.max_solutions-1:
			found = False
			
			for lists in MyGlobals.solution_dict[(function1, function2)]:
				for key, value in lists.items():
					if 'CALLER' in key:
						if key in solution:
							if solution[key] == value and value in MyGlobals.st['caller']: 
								found = True
								break
			if found: return False

		return True

	return False

def set_balances_bd(call_var, contract_address, nodes): #for balance difference
	max_balance=-1
	default_addr = '7' * 40
	for index in MyGlobals.st['caller']:
		set_params_bd(0, 'balance', index, 10 ** 22)
	for index in call_var:
		set_params_bd(0,'balance',index[2],10**18)
	if not call_var:
		set_params_bd(0,'balance', default_addr, 10 ** 22)
	set_params_bd(0,'balance', contract_address, 10 ** 20)

def set_params_bd(actual_key,param, input, value):
	if not is_bv(input):
		input=hex(int(str(input),16))[2:]
		# input=Web3.toChecksumAddress(input)[2:]
		if actual_key==0:
			MyGlobals.bals_1[str(input)] = value
			MyGlobals.bals_2[str(input)] = value
		elif actual_key<3 and actual_key>0:
			MyGlobals.bals_1[str(input)] = value
		elif actual_key<5 and actual_key>2:
			MyGlobals.bals_2[str(input)] = value
	else:
		if actual_key==0:
			MyGlobals.bals_1[input] = value
			MyGlobals.bals_2[input] = value
		elif actual_key<3 and actual_key>0:
			MyGlobals.bals_1[input] = value
		elif actual_key<5 and actual_key>2:
			MyGlobals.bals_2[input] = value

def get_params_bd(actual_key,param, input):

	if not is_bv(input):
		input=hex(int(str(input),16))[2:]
	key=input
	if actual_key==0:
		print('wrong actual_key')
	elif actual_key<3 and actual_key>0:
		if key in MyGlobals.bals_1:
			return MyGlobals.bals_1[key]
		elif param == 'balance':
			set_params_bd(actual_key,'balance', key, 10 ** 22)
			return 10 ** 22
		else:
			print('need to produce')
	elif actual_key<5 and actual_key>2:
		if key in MyGlobals.bals_2:
			return MyGlobals.bals_2[key]
		elif param == 'balance':
			set_params_bd(actual_key, 'balance', key, 10 ** 22)
			return 10 ** 22
		else:
			print('need to produce')


def send_ether_bd(actual_key,addr_from, addr_to, amount):
	if not isinstance(addr_from, str) and not is_bv(addr_from):
		addr_from=str(addr_from)
		if addr_from[:2] == '0x': addr_to = addr_to[2:].rstrip('L')
	if not isinstance(addr_to, str) and not is_bv(addr_to):
		addr_to=str(addr_to)
		if addr_to[:2] == '0x': addr_to = addr_to[2:].rstrip('L')
	# Update contract balance
	from_balance = get_params_bd(actual_key,'balance',addr_from)
	to_balance = get_params_bd(actual_key,'balance',addr_to)
	if isinstance(amount, str):
		amount=int(amount,16)
	from_balance -= amount
	to_balance += amount
	set_params_bd( actual_key,'balance', addr_from, from_balance)
	set_params_bd( actual_key, 'balance', addr_to, to_balance)
	return True

def clear_rw_addr(addrs):
	if (-1,-1) in addrs:
		addrs.remove((-1,-1))
	if (-2, -2) in addrs:
		addrs.remove((-2, -2))
	for i in range(1,5):
		for j in range(2):
			var=(i,j)
			if var in addrs:
				addrs.remove(var)


def add_additional_conditions( solver, sha3_values):
	for sym_var, concrete_val in sha3_values.items():

		if len(concrete_val) == 1:
			temp_conc = BitVecVal(int(concrete_val[0]), 256)
			temp_sym = BitVec(sym_var, 256)
			solver.add(temp_sym == temp_conc)

		elif len(concrete_val) > 1:
			p = BitVec('p', 256)
			formula = BitVecVal(0, 256)
			temp_sym = BitVec(sym_var, 256)

			for each_value in concrete_val:
				each_value = BitVecVal(int(each_value), 256)
				formula = (simplify(formula) | simplify(
					If(temp_sym == each_value, BitVecVal(1, 256), BitVecVal(0, 256))))

			print(formula, 'in formula\n')
			solver.add(formula == BitVecVal(1, 256))

		else:
			print('Not able to add conditions\n')
	return


# Determines the TX inputs i.e., solves the symbolic constraints to give solutions of nodes.
def get_function_calls( calldepth, key, function_hash, function1, function2, debug ,sha3_values,j_path=None):

	global s, d, no_function_calls, function_calls

	MyGlobals.num_solver_calls+=1
	time1 = datetime.datetime.now()	

	temp_solver = Solver()
	temp_solver.set("timeout", 1000)
	add_additional_conditions(temp_solver,sha3_values)

	addr_write = deepcopy(MyGlobals.addr_write)
	addr_read = deepcopy(MyGlobals.addr_read)
	clear_rw_addr(addr_write)
	clear_rw_addr(addr_read)
	r_func1 = set()
	r_func2 = set()
	w_func1 = set()
	w_func2 = set()

	for kk in addr_read:
		if kk[0] == 1 or kk[0] == 4:
			r_func1.add(kk[1])
		else:
			r_func2.add(kk[1])
	for kk in addr_write:
		if kk[0] == 1 or kk[0] == 4:
			w_func1.add(kk[1])
		else:
			w_func2.add(kk[1])
	if not ((r_func1 & w_func2) or (r_func2 & w_func1) or (w_func1 & w_func2)) and function1 not in MyGlobals.funcs_involve_call and function2 not in MyGlobals.funcs_involve_call:

		return


	if key ==1:
		temp_solver.add(MyGlobals.s.assertions())

	if key == 2:
		temp_solver.add(MyGlobals.s1.assertions())
		temp_solver.add(MyGlobals.s.assertions())

	if key == 3:
		temp_solver.add(MyGlobals.s1.assertions())
		temp_solver.add(MyGlobals.s.assertions())

	elif key == 4:
		temp_solver.add(MyGlobals.s2.assertions())
		temp_solver.add(MyGlobals.s.assertions())	
	
	satisfied = False	
	if temp_solver in MyGlobals.solver_configurations:
		satisfied = MyGlobals.solver_configurations[temp_solver]
		temp_solver.check()
	else:

		if temp_solver.check() == sat:
			satisfied = True
			MyGlobals.solver_configurations[temp_solver] = satisfied

		else:
			satisfied = False
			MyGlobals.solver_configurations[temp_solver] = satisfied

	if key== 4 and satisfied:
		all_rws=((r_func1 & w_func2) | (r_func2 & w_func1) | (w_func1 & w_func2))
		inst_func1=set()
		inst_func2 = set()
		for rw in all_rws:
			if rw in MyGlobals.m.rwaddr2id:
				if rw in r_func1 | w_func1:
					for elem in MyGlobals.m.rwaddr2id[rw]:
						if elem[0] in [1,4]:
							inst_func1.add(elem[1])
				if rw in r_func2 | w_func2:
					for elem in MyGlobals.m.rwaddr2id[rw]:
						if elem[0] in [2,3]:
							inst_func2.add(elem[1])

		inst_pair=(inst_func1,inst_func2)
		MyGlobals.m.inst_pair=inst_pair

		w_order1= {}; w_order2= {}
		for kk in addr_write:
			if kk[0]==1 or kk[0]==2:
				w_order1[kk[1]]=kk[2]['z3']
			if kk[0]==3 or kk[0]==4:
				w_order2[kk[1]]=kk[2]['z3']

		p_hash = hash(str(j_path))
		if p_hash in MyGlobals.path_hashs:
			return
		k1 = set(w_order1.keys());
		k2 = set(w_order2.keys())
		if k1 & k2:
			temp_solver2 = Solver();temp_solver2.set("timeout", 1000)
			temp_solver2.add(temp_solver.assertions())
			m = [];str_list=[]
			intsc_w = k1 & k2
			for j in intsc_w:
				str_eq=str(simplify(w_order1[j] != w_order2[j]))
				if str_eq not in str_list:
					str_list.append(str_eq)
					m.append(w_order1[j] != w_order2[j])


			temp_solver2.add(Or(m))
			if temp_solver2.check()==sat:
				temp_solver=temp_solver2
				MyGlobals.dr_bug_sd.append((function1, function2,inst_pair))#sd: storage difference
				MyGlobals.path_hashs.add(p_hash)
				print('dr_bug_sd detected')

		#turn call_vars into unique
		first_two_elem = [];j0=0;
		temp3 = {}
		for ind in MyGlobals.call_vars:
			first_two_elem.append(ind[:2])
			temp3[ind[:2]]=j0
			j0=j0+1
		temp4=[];l3_v=list(temp3.values())
		for j2 in l3_v:
			temp4.append(MyGlobals.call_vars[j2])

		MyGlobals.call_vars=deepcopy(temp4)
		contract_address=hex(int(MyGlobals.contract_addr,16)).lstrip('0x')
		# set_balances_bd(MyGlobals.call_vars,contract_address,1)
		for elem in MyGlobals.call_vars:
			send_ether_bd(elem[1],contract_address,elem[2],elem[3])

		temp=deepcopy(MyGlobals.bals_1)
		for j in temp:
			if isinstance(j,str):
				new_k,new_v=BitVecVal(int(j,16),256),temp[j]
				MyGlobals.bals_1.pop(j)
				MyGlobals.bals_1[new_k]=new_v
		temp=deepcopy(MyGlobals.bals_2)
		for j in temp:
			if isinstance(j,str):
				new_k,new_v=BitVecVal(int(j,16),256),temp[j]
				MyGlobals.bals_2.pop(j)
				MyGlobals.bals_2[new_k]=new_v

		sol_call = []
		for elem1 in MyGlobals.bals_1:
			temp_solver3 = Solver();temp_solver3.set("timeout", 1000)
			for elem2 in MyGlobals.bals_2:
				temp_solver3.add(Or(elem1!=elem2, MyGlobals.bals_1[elem1]!=MyGlobals.bals_2[elem2]))
			temp_solver3.add(temp_solver.assertions())
			if temp_solver3.check() == sat:

				MyGlobals.dr_bug_bd.append((function1, function2,inst_pair))#bd: balance difference
				MyGlobals.path_hashs.add(p_hash)
				print('dr_bug_bd detected')
				temp_solver=temp_solver3
				break

		satisfied = True
		MyGlobals.solver_configurations[temp_solver] = satisfied

		MyGlobals.solver_configurations[temp_solver] = satisfied


	if satisfied:
		time2 = datetime.datetime.now()
		MyGlobals.total_time_solver+=(time2-time1).total_seconds()

		m = temp_solver.model()

		if debug: print('\nSolution:')
		sol = {}
		for d in m:
			if debug: print('%s -> %x' % (d,m[d].as_long() ) )
			sol[str(d)] = '%x' % m[d].as_long()

		# Extracting the function inputs
		function_inputs = {}
		functionarr = [function1, function2]
		# Get separate calldepth inputs
		if debug: print(sol)

		for cd in range(1,3):
			function_hash = functionarr[cd-1]

			# Find next free
			next_free = 0
			for f in range(100):
				if ('input'+str(cd)+'['+str(4+32*f)+']'+'-'+function_hash) in sol or ('input'+str(cd)+'['+str(4+32*f)+']'+'-'+function_hash+'d') in sol:
					next_free = 32*f + 32

			# Fix weird addresses
			for f in range(100):
				addr = 'input'+str(cd)+'['+str(4+32*f)+']'+'-'+ function_hash+'d'
				if addr in sol:
					old_address = int(sol[addr],16)
					del sol[addr]
					sol[addr[:-1]] =  '%x'% next_free

					for offset in range(100):
						check_address = 'input'+str(cd)+'['+('%x'%(4+old_address + 32*offset))+']' + '-'+function_hash
						if check_address in sol:
							sol['input'+str(cd)+'['+'%d'%(4+int(next_free)) +']' +'-'+ function_hash] = sol[check_address]
							del sol[check_address]
							next_free += 32


			# Produce the input of the call
			tmp_one = {}
			for addr in sol:
				if addr.find('input'+str(cd)+'[') >= 0:
					tmp_one[addr] = sol[addr]

			# Function arguments
			max_seen = 4
			function_inputs[cd] = function_hash
			for offset in range(100):
				addr = 'input'+str(cd)+'['+'%d'%(4+offset*32)+']' + '-' + function_hash
				if addr in tmp_one:
					function_inputs[cd] = function_inputs[cd] + '%064x' % int(tmp_one[addr],16)
					max_seen = 4+(offset+1)*32
					del tmp_one[addr]
				else:
					function_inputs[cd] = function_inputs[cd] + '%064x' % 0

			function_inputs[cd] = function_inputs[cd][:2*max_seen]

			if len(tmp_one) > 0:
				print('Some addresses are larger')
				print(tmp_one)
				return False

		for num in range(1, 3):
			if num ==1:
				sol['input'+'-'+function1] = function_inputs[num]	
			if num ==2:
				sol['input'+'-'+function2] = function_inputs[num]
		if function1 == function2:
			for num in range(1, 3) :
				if num ==1:
					sol['input'+'-1-'+function1] = function_inputs[num]
				if num ==2:
					sol['input'+'-2-'+function2] = function_inputs[num]
		return sol
	


	else:
		time2 = datetime.datetime.now()
		MyGlobals.total_time_solver+=(time2-time1).total_seconds()
		return False


