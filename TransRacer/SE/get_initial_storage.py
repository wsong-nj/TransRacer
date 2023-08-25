
from eth_utils import encode_hex, decode_hex, to_canonical_address, ValidationError
from evm import InstrumentedEVM
from utils import settings
# import evm
# import utils

def get_initial_storage(address,deployement_bytecode):
    blockchain_state = []
    instrumented_evm = InstrumentedEVM(settings.RPC_HOST, settings.RPC_PORT)

    instrumented_evm.set_vm_by_name(settings.EVM_VERSION)
    instrumented_evm.accounts.append(instrumented_evm.create_fake_account(address))
    result = instrumented_evm.deploy_contract(instrumented_evm.accounts[0],deployement_bytecode)
    if result.is_error:
        return {},True
    else:
        if instrumented_evm.chain.chaindb.db.wrapped_db.kv_store['storage'].values():
            return list(instrumented_evm.chain.chaindb.db.wrapped_db.kv_store['storage'].values())[0],False
        else:
            return {},False
