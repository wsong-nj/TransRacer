# TransRacer

A symbolic analysis tool that detects transaction races for Ethereum smart contracts.



## Dependencies:
Try to install with follow command. If failed, try to manually access from the corresponding website.

cd TransRacer

cd SE

pip install -r requirements.txt
`	`
### Z3 solver
Install Z3 package from [here](https://pypi.org/project/z3-solver/#files)

### web3 suit
Install web3 package from [here](https://pypi.org/project/web3/#files)

### Infura account
Acquire Infura from [here](https://infura.io/)

### Etherscan api key
Acquire api key from [here](https://etherscan.io/)

### Contract initial storage
Acquire contract initial storage from [here](https://etherscan.io/)
If this item is missed, TransRacer will attempt to access the contract's initial storage by deploying the contract on a private network.


## Run TransRacer
Make sure you can connect to the internet before running TransRacer.

After the TransRacer. zip is downloaded and the python environment is configured, one can run TransRacer with follow command. 

cd /SE && python main.py --addr [Contract address]  --owner [Owner address]  --agency_account [Infura account] --init_storage_path [initial storage file path] --api_key [api key]


## Quick test  Contract DistractedBoyfriend
cd /SE && python main.py --addr 0x351016D3eC753Db8E98a783CF51c8D6a4a8af151  --owner 0x4a3D25D58930f7b04E85E7946852fC2d8Fd59489  --agency_account https://mainnet.infura.io/v3/e67c4e1f139d4940a53bc61120bc3bf5 --api_key WTZ5E69T1SKACPGYF29W6ZG6CE3123APIU


The output of TransRacer is stored in a report file, which includes the following sub-files:

The "races" file provides information on function pairs that can lead to races and their corresponding witness transactions.

The "race bugs" file lists function pairs that can lead to storage and balance differences.

The "deps" file presents the found function dependencies.

The "time_cost" file reports the time duration spent by TransRacer on testing each contract.


To run ETHRacer, follow these steps:
1) Download the code from their GitHub repository: https://github.com/aashishkolluri/Ethracer
2) Install the required dependencies: web3, pysha3, solc, z3-solver.
3) Obtain the initial storage of the contract from [here](https://etherscan.io/) 
4) Configure the test state of ETHRacer to match the initial contract state using the following steps:
   1) Replace the code in the first 'if' branch of the get_storage_value function in the files HB/values.py, fuzzer/op_exe.py, and fuzzer/param.py with the following code snippet:
          
          if index in initial_storage:
               value = initial_storage[index]
          else:
               value = 0
          return value.to_bytes(32, byteorder='big')
   2) Replace the code at lines 514~524 of fuzzer/op_exe.py with the following code snippet:
   
          if index in initial_storage:
               value = initial_storage[index]
          else:
               value = 0
   Note: The variable initial_storage is the initial storage obtained in step 3
5) Run ETHRacer using the following command: cd /ethracer/HB && python main.py --checkone [Contract source code] [Contract address] --blockchain --owner [Owner address]

To run Oyente, follow these steps:
1) Open a Docker container and run the following command: docker pull luongnguyen/oyente && docker run -i -t luongnguyen/oyente
2) Copy the test contract (test.sol) to the container and run the following command: cd /oyente/oyente && python oyente.py -s test.sol

To run Securify, follow these steps:
1) Download the code from their GitHub repository: https://github.com/eth-sri/securify2
2) Build a Docker container using this command: sudo docker build -t securify .
3) Run Securify using the following command: sudo docker run -it -v <contract-dir-full-path>:/share securify /share/test.sol
Note: Replace <contract-dir-full-path> with the full path of the directory containing the contract to be analyzed.

To run Sailfish, follow these steps:
1) Install Sailfish on an Ubuntu OS using the command lines provided in this file: https://github.com/ucsb-seclab/sailfish/blob/master/docker/Dockerfile
2) Run Sailfish using the following command: python contractlint.py -c ../../test_cases/reentrancy/mutex_fp_prunning_non_reentrant.sol -o <path/to/output-dir> -r range -p DAO,TOD -oo -sv cvc4
Note: Replace <path/to/output-dir> with the path to the desired output directory.



