from web3 import Web3
import copy
from z3 import *
import datetime


def optimize_hb(hb_list):
	simplified_hb = []

	for item in hb_list:
		if item not in simplified_hb:
			temp = ()
			temp += (item[1], )
			temp += (item[0], )

			if not temp in hb_list:
				simplified_hb.append(copy.deepcopy(item))
	return simplified_hb			

# Read storage value
def get_storage_value( address, index, read_from_blockchain = False ):

	if read_from_blockchain:
		web3 = Web3(Web3.HTTPProvider("https://withered-purple-valley.discover.quiknode.pro/4d3d5c466dcf22813d75d328362dec3033c52180/"))
		if MyGlobals.STORAGE_AT_BLOCK >= 0:
			value = web3.eth.getStorageAt( Web3.toChecksumAddress(address), index, MyGlobals.STORAGE_AT_BLOCK )
		else:
			value = web3.eth.getStorageAt( Web3.toChecksumAddress(address), index )
		return value
	else:
		return '0'.zfill(64)

# Get value 
def get_params(param, input):

	if (param+str(input)) in MyGlobals.st:
		return MyGlobals.st[param+str(input)]
	else:
		print('need to set the parameters: %s ' % (param+str(input) ) )
		exit(4)

# Is set
def is_params(param,input):
	return (param+str(input)) in MyGlobals.st 

# Set parameter
def set_params(param, input, value):
	global st
	MyGlobals.st[param+str(input)] = value		

# Create a dict of paramters
# def initialize_params(read_from_blockchain, c_address, nsolutions):
def initialize_params(c_address):

	# Set (dummy) values for parameters often used in the contracts
	global st

	MyGlobals.st = {}
	MyGlobals.st['my_address'] = ('6' * 40).zfill(64)
	MyGlobals.st['contract_address'] = c_address
	MyGlobals.st['contract_balance'] = '7' * 64
	MyGlobals.st['gas'] = ('765432').zfill(64)
	MyGlobals.st['gas_limit'] = ('%x' % 5000000).zfill(64)
	MyGlobals.st['gas_price'] = ('123').zfill(64)
	MyGlobals.st['time_stamp'] = ('%x' % 0x7687878).zfill(64)
	MyGlobals.st['block_number'] = ('545454').zfill(64)
	MyGlobals.st['caller'] = [('22' * 20).zfill(40)]

def print_params():
	for s in MyGlobals.st:
		print('%20s : %s' % (s, str(MyGlobals.st[s])))

def update_global_datastructures(stack, storage, sha3_dict, sha3_values, data) :
	MyGlobals.datastructures['stack'] = copy.deepcopy(stack)
	MyGlobals.datastructures['storage'] = copy.deepcopy(storage)
	MyGlobals.datastructures['sha3_dict'] = copy.deepcopy(sha3_dict)
	MyGlobals.datastructures['data'] = copy.deepcopy(data)
	MyGlobals.datastructures['sha3_values'] = copy.deepcopy(sha3_values)


'''

Memoization using solver configurations.

'''
def create_configuration( stack, mmemory, storage):
	nc = {}
	nc['stack']   = copy.deepcopy(stack)
	nc['mmemory'] = copy.deepcopy(mmemory)
	nc['storage'] = copy.deepcopy(storage)
	return nc
	
def add_configuration( step, configurations, nc):
	if step in configurations: configurations[step].append( nc )
	else:configurations[step] = [nc]
	

def configuration_exist(step, configurations, nc):
	if step not in configurations:
		return False
	
	found = False
	for os in configurations[step]:

		# Compare stack
		if os['stack'] != nc['stack'] : continue
		
		# Compare mmemory
		if os['mmemory'] != nc['mmemory']: continue

		# Compare storage
		if( os['storage'] != nc['storage'] ):continue
			
		found = True
		break
		
	return found 
	
def seen_configuration( configurations, ops, position, stack, mmemory, storage):

		# Check if configuration exist
		op = ops[position]['o']
		step = ops[position]['id']
		nc = create_configuration( stack, mmemory, storage)
		if configuration_exist(step, configurations, nc): 
			return True
		else:
			add_configuration( step, configurations, nc)
				
		return False


class h_maps(object):
	def __init__(self):
		self.func_hash2path_hash = {}
		self.path_hash2func_hash = {}

		self.path_hash2indv_hash = {}  # path hash to indv hash
		self.hash2path = {}  # path hash to path
		self.hash2path_list = {}
		self.bestfit={}
		self.path_ind2state={}
		self.abn_id_2_addr={}
		self.func_of_sorted_paths=[]

		p_temp={}
		self.func2pcs={}
		self.feasible_paths_valid=set()
		self.feasible_paths_dict_valid={}
		# self.feasible_paths_valid_for_nested_round=[]
		self.infeasible_paths_valid=set()
		self.infeasible_paths=set()
		self.pcs_of_sorted_paths={}

		self.activated_paths=list()
		self.activated_paths_nested=set()
		self.activated_paths_fd=set()
		self.bestfit = {}
		self.bestfit_state={}
		self.max_jump_num={}

		self.rs=dict()
		self.ws = dict()
		self.rs_temp=set()
		self.ws_temp = set()
		self.rs_added=set()
		self.ws_added=set()#added during dep check
		self.sha_v2slot=dict()
		self.covered_prefixs=set()
		self.triggered_ws={}
		self.triggered_rs={}

		self.rs_temp_id=set()
		self.ws_temp_id = set()
		self.rs_added_id=set()
		self.ws_added_id=set()#added during dep check
		self.triggered_ws_id={}
		self.triggered_rs_id={}
		self.rwaddr2id={}
		self.inst_pair=()
		self.inst_pairs=[]

		self.may_feasible_paths=set()
		self.callable_funcs=set()
	def resetme(self):
		self.func_hash2path_hash = {}
		self.path_hash2func_hash = {}

		self.path_hash2indv_hash = {}  # path hash to indv hash
		self.hash2path = {}  # path hash to path
		self.hash2path_list = {}
		self.bestfit={}
		self.path_ind2state={}
		self.abn_id_2_addr={}
		self.func_of_sorted_paths=[]

		p_temp={}
		self.func2pcs={}
		self.feasible_paths_valid=set()
		self.feasible_paths_dict_valid={}
		# self.feasible_paths_valid_for_nested_round=[]
		self.infeasible_paths_valid=set()
		self.infeasible_paths=set()
		self.pcs_of_sorted_paths={}

		self.activated_paths=list()
		self.activated_paths_nested=set()
		self.activated_paths_fd=set()
		self.bestfit = {}
		self.bestfit_state={}
		self.max_jump_num={}

		self.rs=dict()
		self.ws = dict()
		self.rs_temp=set()
		self.ws_temp = set()
		self.rs_added=set()
		self.ws_added=set()#added during dep check
		self.sha_v2slot=dict()
		self.covered_prefixs=set()
		self.triggered_ws={}
		self.triggered_rs={}

		self.rs_temp_id=set()
		self.ws_temp_id = set()
		self.rs_added_id=set()
		self.ws_added_id=set()#added during dep check
		self.triggered_ws_id={}
		self.triggered_rs_id={}
		self.rwaddr2id={}
		self.inst_pair=()
		self.inst_pairs=[]

		self.may_feasible_paths=set()
'''
Object initialized during runtime. This contains global context.
'''
class MyGlobals(object):
	new_key_w = True
	new_key_r = True
	addrs=[]
	input_types={}
	# for race detection
	last_key=0
	last_key_w=0
	addr_read = []
	addr_write=[]
	new_branch=True;branch_count=0
	branch_ended=False
	branch_point=[0]
	branch_point_w=[0]
	solution_dict_stage2={}
	multi_state_activate=True
	max_round=3
	storage_temp={}
	stage2_actived=False
	cr_exist={}
	accounts_to_access_ethereum=["https://mainnet.infura.io/v3/e67c4e1f139d4940a53bc61120bc3bf5"]

	pair=()
	reach_stage=0
	read_set=EmptySet(IntSort())
	write_set=EmptySet(IntSort())
	enforce_stage_change_activated=False
	sstore_set=[]
	storage_change_dict={}
	STORAGE_AT_BLOCK = -1

	#for R/W conflict
	round_num=0
	call_vars=[]
	contract_addr='0x'
	bals_1={}
	bals_2 = {}
	dr_bug_bd=[]
	dr_bug_sd=[]
	new_key=True
	key_stack=[]
	current_key=[]

	#record info for debug and report
	trace_for_funcs={}
	initial_storage={}
	storage_info={}
	stage_record={}
	impfuncs=[]
	function_pairs_list = []
	stack_record=[]
	t_record=[]
	concrete_total=[0,0]
	round_record=[]
	extra_pair=[]
	large_contract=False
	too_short_contract=False
	path_hashs=set()
	#record info for quick search
	terminate_stage=2
	ind0=0
	m=h_maps()
	feasible_jumpdest={}
	start_addr_2_end_inst={}
	end_op=''
	#for concrete execution
	newpair=True
	concrete_read=set()
	concrete_write=set()
	balance_f={}
	sol={}

	addr2val={}
	dr_pos={}
	# = 4350000

	set_storage_symbolic = False
	jumpi_switch = False

	MAX_JUMP_DEPTH 			= 50					# path length in CFG
	MAX_CALL_DEPTH 			= 1						# different function calls to the contract
	MAX_VISITED_NODES      	= 2000					# sum of all paths in search of one contract

	MIN_CODE_SIZE = 4
	MAX_CODE_SIZE = 15000


	ETHER_LOCK_GOOD_IF_CAN_CALL = True

	st = {}
	sz={}
	#for multi-dependence
	des_s = Solver()
	checked_list = {}
	stack2 = []
	stack2_all=[[]]
	path = [0, 0, 0, 0]
	paths = [0]
	funcs_involve_call=set()
	func_hash2abi={}

	storage_stack2={}
	storage_stack2_all=[[]]
	mmemory_stack2= {}
	mmemory_stack2_all = [[]]

	j_c=[]
	pos_set=set()
	multi_dr=[]
	mul_dr_suspend = False
	#
	# Z3 solver
	# 
	SOLVER_TIMEOUT = 1000		#timeout
	s = Solver()
	s1 = Solver()
	s2 = Solver()
	s1_temp = Solver()
	s2_temp = Solver()
	s.set("timeout", SOLVER_TIMEOUT)
	solver_configurations = {}

	search_condition_found = False
	solution_found = False
	in_sha3 = 0
	stop_search = False
	visited_nodes = 0

	fast_search = True	
	good_jump_positions = []

	last_eq_step = -1
	last_eq_func = -1
	num_functions = -1
	functions = []

	symbolic_vars = []
	no_function_calls = 0
	function_calls = {}

	max_solutions = 3
	max_jumpdepth_in_normal_search = 600

	datastructures = {}
	# The datastructure which stores all global variables that a function could change
	funcvardata = {}
	sha3vardata = {}
	solution_dict = {}

	ONE_CONTRACT_TIMEOUT = 120 * 60
	Time_checkpoint_HB = datetime.datetime.now()
	ONE_PAIR_TIMEOUT = 20 * 60
	Time_checkpoint = datetime.datetime.now()

	num_solver_calls = 0
	total_time_solver = 0

	notimplemented_ins = {}

	debug = False
	debug1 = False
	criteria = 1
	read_from_blockchain = True
	bp=False
def clear_globals():

	MyGlobals.s.reset() 
	MyGlobals.s1.reset()
	MyGlobals.s2.reset()
	MyGlobals.s.set("timeout", MyGlobals.SOLVER_TIMEOUT)
	MyGlobals.s1.set("timeout", MyGlobals.SOLVER_TIMEOUT)
	MyGlobals.s2.set("timeout", MyGlobals.SOLVER_TIMEOUT)


	MyGlobals.s1_temp.reset()
	MyGlobals.s2_temp.reset()

	MyGlobals.search_condition_found = False
	MyGlobals.stop_search = False
	MyGlobals.visited_nodes = 0
	MyGlobals.no_function_calls = 0
	MyGlobals.function_calls = {}





