import sys

import requests

sys.path.insert(0, '../pkgs')
import argparse
import glob
import os
import math
import time
import datetime
from z3 import *
import checking_races
from checking_races import RaceDetector
from global_vars import MyGlobals, initialize_params
import misc
from misc import get_func_hashes, print_function_name, find_blockNumber, getFuncHashes, print_function_name, \
    print_nodes, print_nodes_list, print_notimplemented, remove0x
from os import path
from itertools import product
import sys
from web3 import Web3, HTTPProvider
import glob
import ast
from copy import deepcopy
from generate_input import gen
import requests
import json
from get_initial_storage import get_initial_storage

def initialize_datastructures():
    MyGlobals.functions[:] = []
    MyGlobals.symbolic_vars[:] = []
    MyGlobals.function_calls.clear()
    MyGlobals.datastructures.clear()
    MyGlobals.funcvardata.clear()
    MyGlobals.sha3vardata.clear()
    MyGlobals.solution_dict.clear()

    MyGlobals.new_key_w = True
    MyGlobals.new_key_r = True
    MyGlobals.w_overall = {}

    # new_branch=False
    MyGlobals.addr_read = []
    MyGlobals.addr_write = []
    MyGlobals.new_branch = True

    MyGlobals.solution_dict_stage2 = {}
    MyGlobals.storage_temp = {}
    MyGlobals.stage2_actived = False
    MyGlobals.pair = ()
    MyGlobals.reach_stage = 0
    MyGlobals.large_contract = False
    MyGlobals.too_short_contract = False
    MyGlobals.sstore_set = []
    MyGlobals.st = {}
    MyGlobals.solver_configurations = {}
    MyGlobals.solution_found = False
    MyGlobals.in_sha3 = 0
    MyGlobals.num_solver_calls = 0
    MyGlobals.total_time_solver = 0
    MyGlobals.notimplemented_ins = {}
    MyGlobals.storage_change_dict = {}
    MyGlobals.cr_exist = {}
    MyGlobals.dr_bug_bd = []
    MyGlobals.dr_bug_sd = []
    MyGlobals.round_num = 0
    MyGlobals.all_causal_pair = []
    MyGlobals.solution_dict_stage2 = {}

    MyGlobals.trace_for_funcs = {}
    MyGlobals.storage_info = {}
    MyGlobals.stage_record = {}
    MyGlobals.function_pairs_list = []
    MyGlobals.impfuncs = []
    MyGlobals.t_record = []
    MyGlobals.concrete_total = [0, 0]
    MyGlobals.round_record = []
    MyGlobals.extra_pair = []
    MyGlobals.dr_pos = {}
    MyGlobals.multi_dr = []
    MyGlobals.addr2val = {}
    MyGlobals.input_types = {}
    MyGlobals.addrs = []
    MyGlobals.funcs_involve_call = set()
    MyGlobals.func_hash2abi = {}
    MyGlobals.m.resetme()

    MyGlobals.path_hashs = set()
    MyGlobals.terminate_stage = 2
    MyGlobals.ind0 = 0
    MyGlobals.feasible_jumpdest = {}
    MyGlobals.start_addr_2_end_inst = {}
    MyGlobals.initial_storage={}
    MyGlobals.m.callable_funcs=set()


'''
First it calls the wHBFinder object to obtain concrete events 
and wHB relations between them. These events are then fuzzed to 
find EO bugs.
'''

def race_check(c_address,owner,agency_account0='',init_storage_path='',api_key=''):

    c_address = c_address
    owner=owner

    initialize_datastructures()
    c_address = Web3.toChecksumAddress(c_address)
    # Initialize remaining private global parameters.
    initialize_params(c_address)

    get_state_failed = True
    if init_storage_path:
        with open (init_storage_path,'r') as fi:
            r=fi.read()
        MyGlobals.initial_storage=ast.literal_eval(r)
    elif api_key:
        Tx_API = "https://api.etherscan.io/api?module=account&action=txlist&address=" + c_address + "&apikey="+api_key
        r1 = requests.get(Tx_API, verify=False, headers={'Connection': 'close'})
        TxData = json.loads(r1.text)
        Tx0 = TxData['result'][0]
        MyGlobals.initial_storage, get_state_failed = get_initial_storage(owner, Tx0['input'])

        if get_state_failed:
            print('cannot obtain initial storage automatically, please provide this')
            exit(0)
    else:
        print('no abi key or initial storage provided')
        exit(0)

    debug = MyGlobals.debug
    debug1 = MyGlobals.debug1


    g = gen()
    func_info={}
    try:
        func_info,MyGlobals.input_types,all_types,func_hash2abi=g.get_read_only_funcs(c_address,apikey = "KBCESDYK43S1CCSDIXS6QQYBW8626PF9IV")#my key
        MyGlobals.sz = g.cal_sz(all_types)
        MyGlobals.func_hash2abi=func_hash2abi
    except Exception as e:
        MyGlobals.sz={}
        MyGlobals.func_hash2abi={}

    if not func_info:
        print('no function info found')
        exit(0)


    MyGlobals.contract_addr = c_address
    if MyGlobals.contract_addr[:2] == '0x':
        MyGlobals.contract_addr = MyGlobals.contract_addr[2:]
    if len(c_address) < 1:  print('\033[91m[-] Contract address is incorrect %s \033[0m' % c_address)

    # find the compiled code from the local blockchain.
    if agency_account0:
        web3 = Web3(HTTPProvider(agency_account0))
    else:
        web3 = Web3(HTTPProvider("https://withered-purple-valley.discover.quiknode.pro/4d3d5c466dcf22813d75d328362dec3033c52180/"))#default key, better use your own key
    compiled_code = web3.eth.getCode(c_address)

    # get the function hashes from the Solidity code
    funclist1 = []

    # Get the function hashes in the specific order as in bytecode.
    compiled_code = str(hex(int.from_bytes(compiled_code, byteorder='big')))

    funclist = get_func_hashes(compiled_code)
    funclist_temp = deepcopy(funclist)
    noimpFuncs = set()
    for func in funclist_temp:
        if func[1] in func_info and func_info[func[1]][1] in ['view', 'pure']:
            noimpFuncs.add(func[1])
            funclist.remove(func)


    # Match bytecode hashes to solidity function names
    funclist2 = []
    for f in funclist:
        fnd = False
        for f1 in funclist1:
            if f1[1] == f[1]:
                funclist2.append((f1[0], f1[1]))
                fnd = True
                break
        if not fnd:
            funclist2.append((f[1], f[1]))

    if len(funclist2) == 0:
        print('Something wrong with the contract \n')

    MyGlobals.functions = copy.deepcopy(funclist2)
    if '11111111' in MyGlobals.func_hash2abi and "'payable': True" in MyGlobals.func_hash2abi['11111111']:
        MyGlobals.functions.append(['11111111', '11111111'])
    found_fallback = False
    for each_pair in funclist2:
        if each_pair == '11111111':
            found_fallback = True
            break
    if found_fallback:
        funclist2.append(['fallback()', '22222222'])
    else:
        funclist2.append(['fallback()', '11111111'])

    MyGlobals.st['caller'].insert(0, Web3.toChecksumAddress(owner)[2:])

    code = compiled_code.replace('\n', '').replace('\r', '').replace(' ', '').lstrip('0x')
    time0 = datetime.datetime.now()
    MyGlobals.Time_checkpoint_HB = datetime.datetime.now()
    c_address = Web3.toChecksumAddress(c_address)

    t_start = datetime.datetime.now()
    RD = RaceDetector(code, c_address, owner, debug, funclist2, noimpFuncs, MyGlobals.read_from_blockchain, web3)
    data_race_set,evidence  = RD.begin_iteration()  # c_address,code
    t_finish = datetime.datetime.now()


    print('races:',data_race_set)
    print('witness:',evidence)
    print('race_bug_sd:',MyGlobals.dr_bug_sd)
    print('race_bug_bd:',MyGlobals.dr_bug_bd)
    print('time:',(t_finish - t_start).total_seconds())



    with open('../reports/time_cost/' + c_address + '.txt', 'w') as f_w:
        f_w.write(str((t_finish - t_start).total_seconds()) + '\n')

    filename = '../reports/race_bugs/' + c_address + '.txt'
    with open(filename, 'w') as f_w:
        f_w.write('dr_bug_sd:' + str(MyGlobals.dr_bug_sd) + '\n')
        f_w.write('dr_bug_bd:' + str(MyGlobals.dr_bug_bd) + '\n')

    bf = {}
    for p_hash, v in MyGlobals.m.bestfit.items():
        func = MyGlobals.m.path_hash2func_hash[p_hash]
        bf[(p_hash, func)] = v
    if bf:
        filename = '../reports/deps/' + c_address + '.txt'
        with open(filename, 'w') as f_w:
            f_w.write('deps:' + str(bf) + "\n")

    filename = '../reports/races/' + c_address + '.txt'
    with open(filename, 'w') as f:
        f.write('data_race_set:' + str(list(set(data_race_set))) + "\n")
        f.write('evidence:' + str(evidence) + "\n")

parser = argparse.ArgumentParser()

parser.add_argument("--addr",					type=str, help="Provide address of the contract", action='store', nargs=1)
parser.add_argument("--owner",					type=str, help="Provide owner of the contract", action='store', nargs=1)
parser.add_argument("--agency_account",			type=str, help="Specific the account to access ethereum", action='store', nargs=1)
parser.add_argument("--maxTimePerPair",			type=str, help="Specific the max process time for a function pair", action='store', nargs=1)
parser.add_argument("--maxTimeOut",			    type=str, help="Specific the max process time for a contract", action='store', nargs=1)
parser.add_argument("--init_storage_path",			type=str, help="Specific init_storage info", action='store', nargs=1)
parser.add_argument("--api_key",			    type=str, help="Specific etherscan api_key", action='store', nargs=1)
args = parser.parse_args()

if args.maxTimePerPair:
    MyGlobals.ONE_PAIR_TIMEOUT = int(args.maxTimePerPair[0])
if args.maxTimeOut:
    MyGlobals.ONE_CONTRACT_TIMEOUT = int(args.maxTimeOut[0])

if args.addr:
    if  args.owner:
        if args.init_storage_path:
            path=args.init_storage_path[0]
        else:
            path=None
        race_check(args.addr[0], args.owner[0],args.agency_account[0],path,args.api_key[0])
    else:
        print("Please provide the addr and owner\n")
        exit(0)
else:
    print("Please provide the addr and owner\n")
    exit(0)