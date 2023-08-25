from __future__ import print_function
from sys import *
from op_list import *
from op_parse import *
from op_exec import get_storage_value, get_params, set_params, clear_params, print_stack, print_storage, execute, print_balances, get_balances, same_balance, send_ether,st_con
import glob
import os
import time
import sys
sys.path.insert(0, '../SE')
sys.path.insert(0,'../pkgs')
from global_vars import MyGlobals
import copy
import itertools
import random
import re
import datetime

temp_storage = {}

PATH_REPORTS = 'races/'


def execute_one_function( contract_address, code , tx_caller, tx_input, tx_value, storage, debug, st_blocknumber, read_from_blockchain = False):
	global temp_storage

	stack   = []
	mmemory = {}
	data = {}

	set_params('call_data_size','',len(tx_input))
	set_params('call_data_load','',tx_input)
	set_params('call_value','',tx_value)
	set_params('caller','',tx_caller)
	set_params('origin','',tx_caller)
	
	if not send_ether( hex(tx_caller).rstrip('L').lstrip('0x'), contract_address.lstrip('0x'), tx_value):
		print('Cannot execute function because the caller does not have enough Ether')
		return False, False
	
	# Execute the next block of operations
	first = True
	pos = 0
	newpos = pos
	
	while (first or newpos != pos):

		first = False
		pos = newpos    
					
		# If no more code, then stop
		if pos >= len(code) or pos < 0:
			if debug:
				print('\033[94m[+] Reached bad/end of execution\033[0m')
				print_stack( stack )
			return False, False

		if debug: print('%3x : %16s : %s' % (code[pos]['id'], code[pos]['o'], code[pos]['input']) )

	
		# Check if the current op is one of the stop code
		if code[pos]['o'] == 'STOP' or code[pos]['o'] == 'RETURN' :

			return True, False

		# Check if the current op is one of the stop code
		if code[pos]['o'] == 'SUICIDE' :
			return True, True

		# Execute the next instruction
		stack, newpos, ret, mmemory = execute( code, stack, pos, storage, temp_storage, mmemory, data,  st_blocknumber, debug, read_from_blockchain  )
		# If it returned True, it means the execution should halt
		if ret: 
			if debug: print('Reached halt statement on %3x : %16s : %s' % (code[pos]['id'], code[pos]['o'], code[pos]['input']) )
			return False, False
	
		# If program counter did not move then 
		if pos == newpos:
			print('\033[95m[-] Unknown %s on line %x \033[0m' % (code[pos]['o'],code[pos]['id']) )
			exit(1)
			return False, False

	



def check_one_trace( contract_address, trace, storage, code, debug, read_from_blockchain, st_blocknumber):

	# Each function in the trace is defined by
	# name - the name of the functions
	# tx_input  - input data (include function hash)
	# tx_caller - sender 
	# tx_value  - msg.value
	# params - set of parameters that should be set (usually block number, etc)
	# each is defined with:
	#   0 - parameter
	#   1 - input
	#   2 - value

	e = True
	#extra params that could vary for every node
	blocknumber  = 0
	timestamp = 0
	blockhash = 0
	if MyGlobals.sol:
		if MyGlobals.newpair:
			st_con.st={}
			temp_storage.clear()
			MyGlobals.newpair = False
	else:
		st_con.st={}
		temp_storage.clear()
	for t in trace:

		if 'tx_blocknumber' in t:
			blocknumber = int(t['tx_blocknumber'], 16)

		if 'tx_timestamp' in t:
			timestamp = int(t['tx_timestamp'], 16)

		if 'tx_blockhash' in t:
			blockhash = t['tx_blockhash']

		if not 'tx_value' in t:
			t['tx_value'] = 0


		set_params('balance', t['tx_caller'], 10 ** 22)
		set_params('balance', contract_address, 10 ** 18)

		set_params('blocknumber', '', blocknumber)
		set_params('timestamp', '', timestamp)
		set_params('blockhash', '', blockhash)
		set_params('contract_address', '', contract_address)

		if MyGlobals.sol:
			if MyGlobals.balance_f:
				for elem in MyGlobals.balance_f:
					set_params('balance', elem, MyGlobals.balance_f[elem])
			else:
				pair=MyGlobals.pair
				node_dict=MyGlobals.sol
				node0={};node1={}
				for elem in node_dict[pair[0]]:
					node0[elem[0]] = elem[1]
				for elem in node_dict[pair[1]]:
					node1[elem[0]] = elem[1]
				set_balances([0,1],contract_address.lstrip('0x').lower(),[node0,node1])

		tx_value = t['tx_value']
		if isinstance(tx_value, str):
			tx_value = int(tx_value, 16)

		tx_caller  =    int(t['tx_caller'], 16)

		if 'storage' in t and t['storage']:
			for sto,val in t['storage'].items():
				storage[sto]=t['storage'][sto]
		next_exec, is_killed = execute_one_function( contract_address, code , tx_caller, t['tx_input'], tx_value, storage, debug, st_blocknumber, read_from_blockchain )
		if MyGlobals.sol: MyGlobals.balance_f=get_balances()
		if is_killed:
			return True
		e = e and next_exec
		if not e: return False

	return True


def set_balances(trace, contract_address, nodes):

	# For all the users in the trace we give an initial equal balance of 10**22 and 
	# for the contract we give the max balance encountered any of the nodes of that trace.
	max_balance = -1
	default_addr = '7'*40

	for index in trace:
		if 'tx_caller' in nodes[index]:
			# print('I am here\n')
			set_params('balance', nodes[index]['tx_caller'].lstrip('0x').lower(), 10**22)
		else:
			nodes[index]['tx_caller'] = default_addr
			set_params('balance', default_addr, 10**22)

		if 'tx_balance' in nodes[index]:
			if nodes[index]['tx_balance'] > max_balance:
				max_balance = nodes[index]['tx_balance']

	if max_balance == -1:
		max_balance = 10**18

	set_params('balance', contract_address, max_balance)
