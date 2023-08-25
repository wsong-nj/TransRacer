#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import random
import collections
import re
from eth_abi import encode_abi
import ast
import requests
from Crypto.Hash import keccak
from copy import deepcopy

UINT_MAX = {
    1: int("0xff", 16),
    2: int("0xffff", 16),
    3: int("0xffffff", 16),
    4: int("0xffffffff", 16),
    5: int("0xffffffffff", 16),
    6: int("0xffffffffffff", 16),
    7: int("0xffffffffffffff", 16),
    8: int("0xffffffffffffffff", 16),
    9: int("0xffffffffffffffffff", 16),
    10: int("0xffffffffffffffffffff", 16),
    11: int("0xffffffffffffffffffffff", 16),
    12: int("0xffffffffffffffffffffffff", 16),
    13: int("0xffffffffffffffffffffffffff", 16),
    14: int("0xffffffffffffffffffffffffffff", 16),
    15: int("0xffffffffffffffffffffffffffffff", 16),
    16: int("0xffffffffffffffffffffffffffffffff", 16),
    17: int("0xffffffffffffffffffffffffffffffffff", 16),
    18: int("0xffffffffffffffffffffffffffffffffffff", 16),
    19: int("0xffffffffffffffffffffffffffffffffffffff", 16),
    20: int("0xffffffffffffffffffffffffffffffffffffffff", 16),
    21: int("0xffffffffffffffffffffffffffffffffffffffffff", 16),
    22: int("0xffffffffffffffffffffffffffffffffffffffffffff", 16),
    23: int("0xffffffffffffffffffffffffffffffffffffffffffffff", 16),
    24: int("0xffffffffffffffffffffffffffffffffffffffffffffffff", 16),
    25: int("0xffffffffffffffffffffffffffffffffffffffffffffffffff", 16),
    26: int("0xffffffffffffffffffffffffffffffffffffffffffffffffffff", 16),
    27: int("0xffffffffffffffffffffffffffffffffffffffffffffffffffffff", 16),
    28: int("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff", 16),
    29: int("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff", 16),
    30: int("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff", 16),
    31: int("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff", 16),
    32: int("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff", 16)
}

INT_MAX = {
    1: int("0x7f", 16),
    2: int("0x7fff", 16),
    3: int("0x7fffff", 16),
    4: int("0x7fffffff", 16),
    5: int("0x7fffffffff", 16),
    6: int("0x7fffffffffff", 16),
    7: int("0x7fffffffffffff", 16),
    8: int("0x7fffffffffffffff", 16),
    9: int("0x7fffffffffffffffff", 16),
    10: int("0x7fffffffffffffffffff", 16),
    11: int("0x7fffffffffffffffffffff", 16),
    12: int("0x7fffffffffffffffffffffff", 16),
    13: int("0x7fffffffffffffffffffffffff", 16),
    14: int("0x7fffffffffffffffffffffffffff", 16),
    15: int("0x7fffffffffffffffffffffffffffff", 16),
    16: int("0x7fffffffffffffffffffffffffffffff", 16),
    17: int("0x7fffffffffffffffffffffffffffffffff", 16),
    18: int("0x7fffffffffffffffffffffffffffffffffff", 16),
    19: int("0x7fffffffffffffffffffffffffffffffffffff", 16),
    20: int("0x7fffffffffffffffffffffffffffffffffffffff", 16),
    21: int("0x7fffffffffffffffffffffffffffffffffffffffff", 16),
    22: int("0x7fffffffffffffffffffffffffffffffffffffffffff", 16),
    23: int("0x7fffffffffffffffffffffffffffffffffffffffffffff", 16),
    24: int("0x7fffffffffffffffffffffffffffffffffffffffffffffff", 16),
    25: int("0x7fffffffffffffffffffffffffffffffffffffffffffffffff", 16),
    26: int("0x7fffffffffffffffffffffffffffffffffffffffffffffffffff", 16),
    27: int("0x7fffffffffffffffffffffffffffffffffffffffffffffffffffff", 16),
    28: int("0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffff", 16),
    29: int("0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffff", 16),
    30: int("0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff", 16),
    31: int("0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff", 16),
    32: int("0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff", 16)
}

INT_MIN = {
    1: int("-0x80", 16),
    2: int("-0x8000", 16),
    3: int("-0x800000", 16),
    4: int("-0x80000000", 16),
    5: int("-0x8000000000", 16),
    6: int("-0x800000000000", 16),
    7: int("-0x80000000000000", 16),
    8: int("-0x8000000000000000", 16),
    9: int("-0x800000000000000000", 16),
    10: int("-0x80000000000000000000", 16),
    11: int("-0x8000000000000000000000", 16),
    12: int("-0x800000000000000000000000", 16),
    13: int("-0x80000000000000000000000000", 16),
    14: int("-0x8000000000000000000000000000", 16),
    15: int("-0x800000000000000000000000000000", 16),
    16: int("-0x80000000000000000000000000000000", 16),
    17: int("-0x8000000000000000000000000000000000", 16),
    18: int("-0x800000000000000000000000000000000000", 16),
    19: int("-0x80000000000000000000000000000000000000", 16),
    20: int("-0x8000000000000000000000000000000000000000", 16),
    21: int("-0x800000000000000000000000000000000000000000", 16),
    22: int("-0x80000000000000000000000000000000000000000000", 16),
    23: int("-0x8000000000000000000000000000000000000000000000", 16),
    24: int("-0x800000000000000000000000000000000000000000000000", 16),
    25: int("-0x80000000000000000000000000000000000000000000000000", 16),
    26: int("-0x8000000000000000000000000000000000000000000000000000", 16),
    27: int("-0x800000000000000000000000000000000000000000000000000000", 16),
    28: int("-0x80000000000000000000000000000000000000000000000000000000", 16),
    29: int("-0x8000000000000000000000000000000000000000000000000000000000", 16),
    30: int("-0x800000000000000000000000000000000000000000000000000000000000", 16),
    31: int("-0x80000000000000000000000000000000000000000000000000000000000000", 16),
    32: int("-0x8000000000000000000000000000000000000000000000000000000000000000", 16)
}

MAX_RING_BUFFER_LENGTH = 10
MAX_ARRAY_LENGTH = 1


class gen:
    def __init__(self):
        self.name = "g"
        self.accounts = "0x4a3D25D58930f7b04E85E7946852fC2d8Fd59489"

    def get_read_only_funcs(self, c_address,apikey ):

        url = "https://api.etherscan.io/api?module=contract&action=getabi&address=" + c_address + "&apikey=" + apikey
        rr = requests.get(url)
        results = ast.literal_eval(rr.text)

        func_info = {};
        input_types = {};
        input_types_all = {}
        if 'status' in results and results['status'] == '1':
            abi_result = results['result']
            abi_result = abi_result.replace("true", "True")
            abi_result = abi_result.replace("false", "False")
            abi_result = ast.literal_eval(abi_result)
            func_hash2abi = {}
            for i, elem in enumerate(abi_result):
                try:
                    str_params = ""
                    if elem['type'] in ["fallback", "constructor"]:
                        if elem['type'] == "fallback":
                            if 'stateMutability' in elem:
                                if elem['stateMutability'] == 'payable':
                                    func_hash2abi['11111111'] = "'payable': True"
                                else:
                                    func_hash2abi['11111111'] = "'payable': False"
                            elif "'payable': True" in elem:
                                func_hash2abi['11111111'] = "'payable': True"
                            else:
                                func_hash2abi['11111111'] = "'payable': False"
                        continue
                    if 'inputs' in elem:
                        for j, input in enumerate(elem["inputs"]):
                            if input:  # input might be empty
                                str_params += input["type"] + ","

                            else:
                                continue
                    if str_params:
                        str0 = elem["name"] + "(" + str_params[:-1] + ")"
                    elif "name" in elem:  # in case elem in constructor
                        str0 = elem["name"] + "(" + str_params + ")"
                    else:
                        continue
                    keccak_hash = keccak.new(digest_bits=256)
                    hh = keccak_hash.update(str0.encode('utf-8')).hexdigest()

                    if 'stateMutability' in elem:
                        func_info[hh[:8]] = (str, elem['stateMutability'])
                        func_hash2abi[hh[:8]] = deepcopy(elem)
                        input_types, input_types_all = self.get_input_type(func_hash2abi)
                    elif 'constant' in elem:
                        if elem['constant']:
                            func_info[hh[:8]] = (str, 'view')
                        else:
                            if elem['type'] == 'fallback':
                                func_info[hh[:8]] = (str, 'payable')
                            else:
                                func_info[hh[:8]] = (str, 'nonpayable')
                        func_hash2abi[hh[:8]] = deepcopy(elem)
                        input_types, input_types_all = self.get_input_type(func_hash2abi)

                except Exception as e:
                    print(e)
        return func_info, input_types, input_types_all, func_hash2abi

    def get_input_type(self, func_hash2abi: dict):
        input_types = {}
        input_types_all = {}
        for k, v in func_hash2abi.items():
            input_types[k] = {}
            input_types_all[k] = []
            if 'inputs' in v:
                inputs = v['inputs']
                bk = False
                for i, elem in enumerate(inputs):
                    str0 = elem['type']
                    input_types_all[k].append(str0)

                for i, elem in enumerate(inputs):
                    str0 = elem['type']
                    if (str0.find('uint') > -1 or str0.find('addr') > -1 or str0.find('bool') > -1) and not str0.find(
                            "[") > -1 and not bk:
                        input_types[k][4 + i * 32] = str0
                    else:
                        bk = True
            else:
                continue
        return input_types, input_types_all

    def generate_random_arguments(self, function, interface):
        if function == "fallback":
            return ""
        function, argument_types = self.get_random_function_with_argument_types()
        arguments = [function]
        for index in range(len(argument_types)):
            arguments.append(self.get_random_argument(argument_types[index], function, index))

        argument_types = [argument_type.replace(" storage", "").replace(" memory", "") for argument_type in
                          interface[function]]
        data = ""

        data += encode_abi(argument_types, arguments).hex()

        return arguments

    def get_random_argument(self, type, function, argument_index):
        # Boolean
        if type.startswith("bool"):
            # Array
            if "[" in type and "]" in type:
                sizes = self._get_array_sizes(argument_index, function, type)
                array = []
                for _ in range(sizes[0]):
                    if random.randint(0, 1) == 0:
                        array.append(False)
                    else:
                        array.append(True)
                return array
            # Single value
            else:
                if random.randint(0, 1) == 0:
                    return False
                return True

        # Unsigned integer
        elif type.startswith("uint"):
            bytes = int(int(type.replace("uint", "").split("[")[0]) / 8)
            # Array
            if "[" in type and "]" in type:
                sizes = self._get_array_sizes(argument_index, function, type)
                array = []
                for _ in range(sizes[0]):
                    array.append(self.get_random_unsigned_integer(0, UINT_MAX[bytes]))

                return array
            # Single value
            else:
                return self.get_random_unsigned_integer(0, UINT_MAX[bytes])

        # Signed integer
        elif type.startswith("int"):
            bytes = int(int(type.replace("int", "").split("[")[0]) / 8)
            # Array
            if "[" in type and "]" in type:
                sizes = self._get_array_sizes(argument_index, function, type)
                array = []
                for _ in range(sizes[0]):
                    array.append(self.get_random_signed_integer(INT_MIN[bytes], INT_MAX[bytes]))
                return array
            # Single value
            else:
                return self.get_random_signed_integer(INT_MIN[bytes], INT_MAX[bytes])

        # Address
        elif type.startswith("address"):
            # Array
            if "[" in type and "]" in type:
                sizes = self._get_array_sizes(argument_index, function, type)
                array = []
                for _ in range(sizes[0]):
                    array.append(self.accounts)
                return array
            # Single value
            else:
                return self.accounts

        # String
        elif type.startswith("string"):
            # Array
            if "[" in type and "]" in type:
                sizes = self._get_array_sizes(argument_index, function, type)
                array = []
                for _ in range(sizes[0]):
                    array.append(self.get_string(random.randint(0, MAX_ARRAY_LENGTH)))
                return array
            # Single value
            else:

                return self.get_string(random.randint(0, 1))

        # Bytes1 ... Bytes32
        elif type.startswith("bytes1") or \
                type.startswith("bytes2") or \
                type.startswith("bytes3") or \
                type.startswith("bytes4") or \
                type.startswith("bytes5") or \
                type.startswith("bytes6") or \
                type.startswith("bytes7") or \
                type.startswith("bytes8") or \
                type.startswith("bytes9") or \
                type.startswith("bytes10") or \
                type.startswith("bytes11") or \
                type.startswith("bytes12") or \
                type.startswith("bytes13") or \
                type.startswith("bytes14") or \
                type.startswith("bytes15") or \
                type.startswith("bytes16") or \
                type.startswith("bytes17") or \
                type.startswith("bytes18") or \
                type.startswith("bytes19") or \
                type.startswith("bytes20") or \
                type.startswith("bytes21") or \
                type.startswith("bytes22") or \
                type.startswith("bytes23") or \
                type.startswith("bytes24") or \
                type.startswith("bytes25") or \
                type.startswith("bytes26") or \
                type.startswith("bytes27") or \
                type.startswith("bytes28") or \
                type.startswith("bytes29") or \
                type.startswith("bytes30") or \
                type.startswith("bytes31") or \
                type.startswith("bytes32"):
            length = int(type.replace("bytes", "").split("[")[0])
            # Array
            if "[" in type and "]" in type:
                sizes = self._get_array_sizes(argument_index, function, type)
                array = []
                for _ in range(sizes[0]):
                    array.append(self.get_random_bytes(length))
                return array
            # Single value
            else:
                return self.get_random_bytes(random.randint(0, length))

        # Bytes
        elif type.startswith("bytes"):
            # Array
            if "[" in type and "]" in type:
                sizes = self._get_array_sizes(argument_index, function, type)
                array = []
                for _ in range(sizes[0]):
                    array.append(self.get_random_bytes(random.randint(0, MAX_ARRAY_LENGTH)))
                return array
            # Single value
            else:
                return self.get_random_bytes(0)
        # Unknown type
        else:
            print('unknown type')

    def _get_array_sizes(self, argument_index, function, type):
        sizes = []
        for size in re.compile(r"\[(.*?)\]").findall(type):
            # Dynamic array
            if size == "":
                sizes.append(random.randint(0, MAX_ARRAY_LENGTH))
            # Fixed size array
            else:
                sizes.append(int(size))
        return sizes

    @staticmethod
    def get_random_unsigned_integer(min, max):
        seed = int(random.uniform(-2, 2))
        if seed == -1:
            return random.choice([min, min + 1, min + 2])
        elif seed == 1:
            return random.choice([max, max - 1, max - 2])
        else:
            return random.randint(min, max)

    @staticmethod
    def get_random_signed_integer(min, max):
        seed = int(random.uniform(-2, 2))
        if seed == -1:
            return random.choice([0, -1, min, min + 1])
        elif seed == 1:
            return random.choice([0, 1, max, max - 1])
        else:
            return random.randint(min, max)

    @staticmethod
    def get_string(length):
        return ''.join('A' for _ in range(length))

    @staticmethod
    def get_random_bytes(length):
        return bytearray(random.getrandbits(8) for _ in range(length))

    def cal_sz(self, input_types_all):
        sz = {}
        for k, v in input_types_all.items():
            if not k == "[]":
                func = k
                argument_types = v
                arguments = []
                for index in range(len(argument_types)):
                    arguments.append(self.get_random_argument(argument_types[index], func, index))
                argument_types = [argument_type.replace(" storage", "").replace(" memory", "") for argument_type in
                                  argument_types]
                data = deepcopy(func)
                data += encode_abi(argument_types, arguments).hex()
                l = len(str(data))
                sz[func] = l / 2


        return sz

    def convert_arguments_to_int(self, arguments):
        arguments_int = []
        for arg in arguments:
            if isinstance(arg, int):
                arguments_int.append(arg)
            elif isinstance(arg, str):
                try:
                    arg_int = int(arg, 16)
                    arguments_int.append(arg_int)
                except:
                    continue
            elif type(arg) == type(bytearray(random.getrandbits(8) for _ in range(2))):
                arg_int = int(arg.hex(), 16)
                arguments_int.append(arg_int)
            elif isinstance(arg, list):
                for elem in arg:
                    if isinstance(elem, int):
                        arguments_int.append(arg)
                    elif isinstance(elem, str):
                        try:
                            elem_int = int(elem, 16)
                            arguments_int.append(elem_int)
                        except:
                            continue
                    elif type(elem) == type(bytearray(random.getrandbits(8) for _ in range(2))):
                        elem_int = int(elem.hex(), 16)
                        arguments_int.append(elem_int)
                    else:
                        continue
            else:
                continue
        return arguments_int
