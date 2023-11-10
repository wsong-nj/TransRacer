from __future__ import print_function
import glob
import re
import ast
from copy import deepcopy

addr2name={'0x895eECA517d3E9ddb66f9Ae8D9c293fd3A30Ddb9': 'MATOX', '0x898cae9474B6Ddd35d1C4fe95f33Dc269158FF1a': 'ChickenFarmer', '0x90b12b97a52451f38090f49BcE8Bc2962ddE4902': 'TokensWarContract', '0x98F777fb9139576902Bf7f35956ca015Ddc1569F': 'ETJ', '0xa82b0eE3daeAC02A5f63Df48db34Bd474C5F8aF7': 'Scale', '0xA94C128a138504E1F81d727cc21bcB9AE6581015': 'Freedom', '0xC6DfBE173A9E6aBB1ac7b1e9d9d774a7E831299C': 'INRD', '0xdD1AcE2f45962e4C1297c784009478865e3B13bE': 'Viewly', '0xF530DF1CB7dF51Ba9CDAB09e7c7294176778A16E': 'EnchantedShop', '0xF670c19e19135079Ac72C1FBc7bE98C6E0Ff27C0': 'Char', '0xf685A139061Fa157cbDaed8299Ed43864140cCd6': 'NinjaKittyUnit', '0xF771Cd3EA4AfBb55e1b2b85E3B9E2388F0Fd43B8': 'CSTK_CLT', '0xfc5772c279bb3A0Bed4219C0De484DeFF3ed2241': 'LendConnect', '0xFCA5a587B7D6e747737031b0E9D5EabC90ad7e68': 'grip', '0xfd1e80508F243E64CE234eA88A5Fd2827c71D4b7': 'MediBloc', '0xffd4E8a619D5fce622DD5B2E8C0A6B0f54Ca93E8': 'CelebrityMarket', '0x037d67c29f19a5451c731312a4C02043143c61cA': 'RADIUM', '0x039F5050dE4908f9b5ddF40A4F3Aa3f329086387': 'EthernetCash', '0x08c507046E12cd1538741D067D28411f2B922062': 'ProofOfReview', '0x08d32b0da63e2C3bcF8019c9c5d849d7a9d791e6': 'Dentacoin', '0x09A80172ED7335660327cD664876b5df6FE06108': 'OMPxContract', '0x0a354862C6F0C6044Afb50fD922f3e918d235e8C': 'ROD', '0x0bb5EAC8854EB42908f601e037cC9E711b174B2e': 'BMUS', '0x0Bd0f26Aaff2cDc0fC1341e4E42cE502bFbF3fAB': 'BrownChipMain', '0x11e62440475536fA49C0A42c83b6E2C9AF84Ae3A': 'PlayCash', '0x12b2028D5eCb59a7172c3d784F8938040E234FB6': 'HSD', '0x13a517751318ccE71A524006b16F7930b3515cCF': 'Sota', '0x15A664416E42766A6cC0a1221d9C088548a6E731': 'WEBN', '0x16B87CA39b3501F3f318F65780a305E20d6fcd52': 'LAAR', '0x17C8d8b7659141273a1c2223030C89b96713a44a': 'Xpense', '0x41b909cd4CdA90f04d0Aaf4097727544FD8AE47a': 'XCTCrowdSale', '0x432555E5c898F83fC5F00dF631BD9c2801FeA289': 'HubrisOne', '0x4d55eE29f3806C6feb424ba5948d660586bD51d3': 'BB', '0x6eaCB6f95b8119AA92D2D394F0A04aD83Fe42091': 'Crowdsale', '0x6EC8a24CaBdc339A06a172F8223ea557055aDAa5': 'Genaro', '0x747616C4a19bD9bF1e2b6c8A77D206eA1f9C6018': 'CityToken', '0x7AD38d200CFFa2b1606931c104cDE833872EBb7f': 'GOG', '0x7d4b8Cce0591C9044a22ee543533b72E976E36C3': 'ChangeBank', '0x7fecA982557Fe5519EB331d3Af5B538b6c166Fa9': 'Yihaa', '0x814F67fA286f7572B041D041b1D99b432c9155Ee': 'Dragon', '0x832b345692B3DAF1294776763DBc69c993526b40': 'UNTY', '0x848ae4cC01C97297cDb4465Bc06b8BCDf27996bA': 'BitcoinBlue', '0x879ED52d9D9f80Be3194A6d6BA51C34Bf1836e03': 'COW','0xD7CD762F3ebC2C9A3D9BCf0133e06d04C59a1F7D': 'Simmitri', '0xe019681c8a189184826Fe17f86c1725e2940c4Ce': 'RippleAlpha', '0xEBed6DA3e9355F1AA402f976C054DB7bc16Be7E0': 'IgfContract', '0x2062b7b18d631e8ae808E178F69b1bfbDff5D545': 'MADANA', '0x36DAECfc172Fd44a165fb93BE5569E72B09CeeA2': 'Winsshar', '0x7C6C3b4e91923F080d6CC847A68d7330400a95d7': 'UniondaoDollarToken', '0x7d03b834E1F302547E40f1DEf6BFF774c3386526': 'Aavio'}
names_ordred=['XCTCrowdSale', 'BitcoinBlue', 'RADIUM', 'BMUS', 'RippleAlpha', 'PlayCash', 'Xpense', 'BB', 'WEBN', 'CelebrityMarket', 'NinjaKittyUnit', 'COW', 'UNTY', 'ChangeBank', 'Aavio', 'Freedom', 'ETJ', 'HubrisOne', 'MADANA', 'GOG', 'MediBloc', 'Simmitri', 'Winsshar', 'ProofOfReview', 'HSD', 'LendConnect', 'ChickenFarmer', 'EnchantedShop', 'MATOX', 'Dragon', 'EthernetCash', 'OMPxContract', 'Sota', 'Viewly', 'Crowdsale', 'Char', 'CityToken', 'ROD', 'BrownChipMain', 'grip', 'TokensWarContract', 'Dentacoin', 'LAAR', 'INRD', 'UniondaoDollarToken', 'Genaro', 'CSTK_CLT', 'Yihaa', 'IgfContract', 'Scale']
def is_elem_of(elem,r3_set_elem):
    for elem2 in r3_set_elem:
        if elem == elem2:
            return True
    return False

def de_repeat(l):
    l_first_two=[]
    for elem in l:
        l_first_two.append((elem[0],elem[1]))

    l_last_two=[]
    for elem in l:
        l_last_two.append((elem[2][0],elem[2][1]))
    reported=[]

    l1=deepcopy(l)
    l2=deepcopy(l_first_two)
    for i,elem in enumerate(l):
        elem_v=(elem[1],elem[0])

        for j,elem2 in enumerate(l_last_two):
            if j>i:
                reported.append(elem2)
        if elem[1]==elem[0]:
            if l1.count(elem)>1:
                if i < len(l_last_two):
                    if is_elem_of(l_last_two[i], reported):
                        l1.remove(elem)
                        l2.remove((elem[0], elem[1]))
                else:
                    l1.remove(elem)
                    l2.remove((elem[0], elem[1]))
        elif  elem_v in l2:
            if i<len(l_last_two):
                if is_elem_of(l_last_two[i],reported):
                    l1.remove(elem)
                    l2.remove((elem[0], elem[1]))
            else:
                l1.remove(elem)
                l2.remove((elem[0], elem[1]))
        else:
            continue
    return l1
def de_repeat_v0(l,r3_set_elem):
    l1=deepcopy(l)
    reported = []
    for i,elem in enumerate(l):
        elem_v=(elem[1],elem[0])

        for j,elem2 in enumerate(r3_set_elem):
            if j>i:
                reported.append(elem2)
        if elem[1]==elem[0]:
            if l1.count(elem)>1:
                if i < len(r3_set_elem):
                    if is_elem_of(r3_set_elem[i], reported):
                        l1.remove(elem)
                else:
                    l1.remove(elem)
        elif  elem_v in l1:
            if i<len(r3_set_elem):
                if is_elem_of(r3_set_elem[i],reported):
                    l1.remove(elem)

            else:
                l1.remove(elem)
        else:
            continue
    return l1
total=0
addr2dep_num={}
addr2dep_funcs={}
fd=0
for fn in glob.glob('../reports_50/deps/*.txt'):
    addr=fn[-4-42:-4]
    with open(fn,'r') as fnn:
        r1=fnn.readline()
        r1_d=ast.literal_eval(r1[len('deps:'):])
        dep=set()

        for k,v in r1_d.items():
            if v:
                dep.add(k[1])
                fd+=len(v)
        name=addr2name[addr]
        num=len(dep)
        total+=num
        addr2dep_num[addr]=num

        addr2dep_funcs[addr]=dep

total=0
addr2race_num={}
for fn in glob.glob('../reports_50/races/*.txt'):
    addr=fn[-4-42:-4]
    TR_i_ini = set()
    TR_d_ini = set()
    TR_i_up = set()
    TR_d_up = set()
    with open(fn,'r') as fnn:
        r1=fnn.readline()
        r1_l=ast.literal_eval(r1[len('data_race_set:'):])
        r2=fnn.readline()
        r3=fnn.readline()
        try:
            r3_l=ast.literal_eval(r3[len('inst_pairs_race:'):])
        except:
            print()
        r3_set_elem=[]
        try:
            for elem in r3_l:
                if str(elem).count('[]')>=1:
                    r3_set_elem.append(set())
                    continue
                if elem:
                    if str(elem).count('[')==1 and elem[0]:
                        r3_set_elem.append(elem[0][0]|elem[0][1])
                    else :
                        elem2=elem[0]
                        if elem2:
                            if str(elem2).count('[') == 1 and elem2[0]:
                                r3_set_elem.append(elem2[0][0] | elem2[0][1])
                        else:
                            continue
                else:
                    continue
        except:
            print()

        r1_l_de=set(de_repeat_v0(r1_l,r3_set_elem))
        num=len(r1_l_de)
        total+=num
        name=addr2name[addr]
        dep_funcs=addr2dep_funcs[addr]
        reported=[]
        for i,elem in enumerate(r1_l):
            pair=r1_l[i]

            p0=pair[0]
            p1=pair[1]
            if not r3_set_elem[i]:
                reported.append(r3_set_elem[i])
            elif is_elem_of(r3_set_elem[i],reported) :
                continue
            else:
                reported.append(r3_set_elem[i])
            if p0 in dep_funcs or p1 in dep_funcs:
                if p0==p1:
                    TR_i_up.add(pair)
                else:
                    TR_d_up.add(pair)
            else:
                if p0==p1:
                    TR_i_ini.add(pair)
                else:
                    TR_d_ini.add(pair)

        addr2race_num[addr]=[len(TR_i_ini),len(TR_i_up),len(TR_d_ini),len(TR_d_up)]

addr2race_bug_num={}
total=0
for fn in glob.glob('../reports_50/race_bugs/*.txt'):
    addr=fn[-4-42:-4]
    TR_i_ini = []
    TR_d_ini = []
    TR_i_up = []
    TR_d_up = []
    with open(fn,'r') as fnn:
        dep_funcs = addr2dep_funcs[addr]
        r1_l=[]
        r3_l=[]
        r3_set_elem=[]
        for i in range(2):
            r1=fnn.readline()
            r1_l_temp = ast.literal_eval(r1[len('dr_bugs_sd'):].replace('set()', '{}'))
            r1_l.extend(r1_l_temp)

        try:
            for elem in r1_l:
                if str(elem[2][0])=='{}':
                    print()
                r3_set_elem.append(set(elem[2][0]) | set(elem[2][1]))
        except:
            print()

        r1_l_de=de_repeat(r1_l)
        num=len(r1_l_de)
        total+=num
        reported=[]
        for i,tuple0 in enumerate(r1_l):
            p0=tuple0[0]
            p1=tuple0[1]
            pair=(p0,p1)
            if not r3_set_elem[i]:
                reported.append(r3_set_elem[i])
            elif is_elem_of(r3_set_elem[i],reported) :
                continue
            else:
                reported.append(r3_set_elem[i])
            if p0 in dep_funcs or p1 in dep_funcs:
                if p0==p1:
                    TR_i_up.append(pair)
                else:
                    TR_d_up.append(pair)
            else:
                if p0==p1:
                    TR_i_ini.append(pair)
                else:
                    TR_d_ini.append(pair)
        name=addr2name[addr]
        addr2race_bug_num[addr] = [len(set(TR_i_ini)), len(set(TR_i_up)), len(set(TR_d_ini)), len(set(TR_d_up))]

addr2_depnum={'0x0a354862C6F0C6044Afb50fD922f3e918d235e8C': 6, '0x0bb5EAC8854EB42908f601e037cC9E711b174B2e': 2, '0x0Bd0f26Aaff2cDc0fC1341e4E42cE502bFbF3fAB': 0, '0x6eaCB6f95b8119AA92D2D394F0A04aD83Fe42091': 1, '0x6EC8a24CaBdc339A06a172F8223ea557055aDAa5': 0, '0x7AD38d200CFFa2b1606931c104cDE833872EBb7f': 7, '0x7C6C3b4e91923F080d6CC847A68d7330400a95d7': 0, '0x7fecA982557Fe5519EB331d3Af5B538b6c166Fa9': 3, '0x08c507046E12cd1538741D067D28411f2B922062': 3, '0x08d32b0da63e2C3bcF8019c9c5d849d7a9d791e6': 2, '0x09A80172ED7335660327cD664876b5df6FE06108': 1, '0x11e62440475536fA49C0A42c83b6E2C9AF84Ae3A': 3, '0x13a517751318ccE71A524006b16F7930b3515cCF': 5, '0x15A664416E42766A6cC0a1221d9C088548a6E731': 3, '0x16B87CA39b3501F3f318F65780a305E20d6fcd52': 7, '0x17C8d8b7659141273a1c2223030C89b96713a44a': 3, '0xffd4E8a619D5fce622DD5B2E8C0A6B0f54Ca93E8': 1, '0xfd1e80508F243E64CE234eA88A5Fd2827c71D4b7': 4, '0xFCA5a587B7D6e747737031b0E9D5EabC90ad7e68': 4, '0xF771Cd3EA4AfBb55e1b2b85E3B9E2388F0Fd43B8': 6, '0xf685A139061Fa157cbDaed8299Ed43864140cCd6': 0, '0xF670c19e19135079Ac72C1FBc7bE98C6E0Ff27C0': 3, '0xEBed6DA3e9355F1AA402f976C054DB7bc16Be7E0': 7, '0xe019681c8a189184826Fe17f86c1725e2940c4Ce': 3, '0xdD1AcE2f45962e4C1297c784009478865e3B13bE': 0, '0xD7CD762F3ebC2C9A3D9BCf0133e06d04C59a1F7D': 4, '0xC6DfBE173A9E6aBB1ac7b1e9d9d774a7E831299C': 2, '0xA94C128a138504E1F81d727cc21bcB9AE6581015': 1, '0xa82b0eE3daeAC02A5f63Df48db34Bd474C5F8aF7': 10, '0x432555E5c898F83fC5F00dF631BD9c2801FeA289': 2, '0x2062b7b18d631e8ae808E178F69b1bfbDff5D545': 2, '0x98F777fb9139576902Bf7f35956ca015Ddc1569F': 3, '0x879ED52d9D9f80Be3194A6d6BA51C34Bf1836e03': 1, '0x895eECA517d3E9ddb66f9Ae8D9c293fd3A30Ddb9': 3, '0x898cae9474B6Ddd35d1C4fe95f33Dc269158FF1a': 1, '0x7d03b834E1F302547E40f1DEf6BFF774c3386526': 3, '0x90b12b97a52451f38090f49BcE8Bc2962ddE4902': 3, '0x747616C4a19bD9bF1e2b6c8A77D206eA1f9C6018': 4, '0x814F67fA286f7572B041D041b1D99b432c9155Ee': 4, '0x832b345692B3DAF1294776763DBc69c993526b40': 0, '0x848ae4cC01C97297cDb4465Bc06b8BCDf27996bA': 2, '0x12b2028D5eCb59a7172c3d784F8938040E234FB6': 4, '0x36DAECfc172Fd44a165fb93BE5569E72B09CeeA2': 1, '0x037d67c29f19a5451c731312a4C02043143c61cA': 0, '0x4d55eE29f3806C6feb424ba5948d660586bD51d3': 4, '0x039F5050dE4908f9b5ddF40A4F3Aa3f329086387': 3, '0x41b909cd4CdA90f04d0Aaf4097727544FD8AE47a': 0, '0xfc5772c279bb3A0Bed4219C0De484DeFF3ed2241': 0, '0xF530DF1CB7dF51Ba9CDAB09e7c7294176778A16E': 2, '0x7d4b8Cce0591C9044a22ee543533b72E976E36C3': 3}
total0=0
total1=0
addr2race_and_race_bug_num={}
order={}
times=[]
times_d={}
for key,val in addr2name.items():
    ind=names_ordred.index(val)
    with open('../reports_50/time_cost/'+key+'.txt','r') as ff:
        t=ff.readline()
        times_d[ind]=float(t[:-1])
for i in range(50):
    times.append(times_d[i])
total=0
for t in times:
    total+=t


for addr,v in addr2race_bug_num.items():
    v0=addr2race_num[addr]

    v_all=deepcopy(v0)
    v_all.extend(v)

    name=addr2name[addr]
    ind=names_ordred.index(name)

    order[ind]=[addr2name[addr]]
    order[ind].extend([addr2_depnum[addr]])
    order[ind].extend(v_all)
    order[ind].append(int(times[ind]/60*10)/10)

    addr2race_and_race_bug_num[addr]=v_all
    total0+=sum(v0)
    total1+=sum(v)

addr2name={'0x895eECA517d3E9ddb66f9Ae8D9c293fd3A30Ddb9': 'MATOX', '0x898cae9474B6Ddd35d1C4fe95f33Dc269158FF1a': 'ChickenFarmer', '0x90b12b97a52451f38090f49BcE8Bc2962ddE4902': 'TokensWarContract', '0x98F777fb9139576902Bf7f35956ca015Ddc1569F': 'ETJ', '0xa82b0eE3daeAC02A5f63Df48db34Bd474C5F8aF7': 'Scale', '0xA94C128a138504E1F81d727cc21bcB9AE6581015': 'Freedom', '0xC6DfBE173A9E6aBB1ac7b1e9d9d774a7E831299C': 'INRD', '0xdD1AcE2f45962e4C1297c784009478865e3B13bE': 'Viewly', '0xF530DF1CB7dF51Ba9CDAB09e7c7294176778A16E': 'EnchantedShop', '0xF670c19e19135079Ac72C1FBc7bE98C6E0Ff27C0': 'Char', '0xf685A139061Fa157cbDaed8299Ed43864140cCd6': 'NinjaKittyUnit', '0xF771Cd3EA4AfBb55e1b2b85E3B9E2388F0Fd43B8': 'CSTK_CLT', '0xfc5772c279bb3A0Bed4219C0De484DeFF3ed2241': 'LendConnect', '0xFCA5a587B7D6e747737031b0E9D5EabC90ad7e68': 'grip', '0xfd1e80508F243E64CE234eA88A5Fd2827c71D4b7': 'MediBloc', '0xffd4E8a619D5fce622DD5B2E8C0A6B0f54Ca93E8': 'CelebrityMarket', '0x037d67c29f19a5451c731312a4C02043143c61cA': 'RADIUM', '0x039F5050dE4908f9b5ddF40A4F3Aa3f329086387': 'EthernetCash', '0x08c507046E12cd1538741D067D28411f2B922062': 'ProofOfReview', '0x08d32b0da63e2C3bcF8019c9c5d849d7a9d791e6': 'Dentacoin', '0x09A80172ED7335660327cD664876b5df6FE06108': 'OMPxContract', '0x0a354862C6F0C6044Afb50fD922f3e918d235e8C': 'ROD', '0x0bb5EAC8854EB42908f601e037cC9E711b174B2e': 'BMUS', '0x0Bd0f26Aaff2cDc0fC1341e4E42cE502bFbF3fAB': 'BrownChipMain', '0x11e62440475536fA49C0A42c83b6E2C9AF84Ae3A': 'PlayCash', '0x12b2028D5eCb59a7172c3d784F8938040E234FB6': 'HSD', '0x13a517751318ccE71A524006b16F7930b3515cCF': 'Sota', '0x15A664416E42766A6cC0a1221d9C088548a6E731': 'WEBN', '0x16B87CA39b3501F3f318F65780a305E20d6fcd52': 'LAAR', '0x17C8d8b7659141273a1c2223030C89b96713a44a': 'Xpense', '0x41b909cd4CdA90f04d0Aaf4097727544FD8AE47a': 'XCTCrowdSale', '0x432555E5c898F83fC5F00dF631BD9c2801FeA289': 'HubrisOne', '0x4d55eE29f3806C6feb424ba5948d660586bD51d3': 'BB', '0x6eaCB6f95b8119AA92D2D394F0A04aD83Fe42091': 'Crowdsale', '0x6EC8a24CaBdc339A06a172F8223ea557055aDAa5': 'Genaro', '0x747616C4a19bD9bF1e2b6c8A77D206eA1f9C6018': 'CityToken', '0x7AD38d200CFFa2b1606931c104cDE833872EBb7f': 'GOG', '0x7d4b8Cce0591C9044a22ee543533b72E976E36C3': 'ChangeBank', '0x7fecA982557Fe5519EB331d3Af5B538b6c166Fa9': 'Yihaa', '0x814F67fA286f7572B041D041b1D99b432c9155Ee': 'Dragon', '0x832b345692B3DAF1294776763DBc69c993526b40': 'UNTY', '0x848ae4cC01C97297cDb4465Bc06b8BCDf27996bA': 'BitcoinBlue', '0x879ED52d9D9f80Be3194A6d6BA51C34Bf1836e03': 'COW','0xD7CD762F3ebC2C9A3D9BCf0133e06d04C59a1F7D': 'Simmitri', '0xe019681c8a189184826Fe17f86c1725e2940c4Ce': 'RippleAlpha', '0xEBed6DA3e9355F1AA402f976C054DB7bc16Be7E0': 'IgfContract', '0x2062b7b18d631e8ae808E178F69b1bfbDff5D545': 'MADANA', '0x36DAECfc172Fd44a165fb93BE5569E72B09CeeA2': 'Winsshar', '0x7C6C3b4e91923F080d6CC847A68d7330400a95d7': 'UniondaoDollarToken', '0x7d03b834E1F302547E40f1DEf6BFF774c3386526': 'Aavio'}
names_ordred=['XCTCrowdSale', 'BitcoinBlue', 'RADIUM', 'BMUS', 'RippleAlpha', 'PlayCash', 'Xpense', 'BB', 'WEBN', 'CelebrityMarket', 'NinjaKittyUnit', 'COW', 'UNTY', 'ChangeBank', 'Aavio', 'Freedom', 'ETJ', 'HubrisOne', 'MADANA', 'GOG', 'MediBloc', 'Simmitri', 'Winsshar', 'ProofOfReview', 'HSD', 'LendConnect', 'ChickenFarmer', 'EnchantedShop', 'MATOX', 'Dragon', 'EthernetCash', 'OMPxContract', 'Sota', 'Viewly', 'Crowdsale', 'Char', 'CityToken', 'ROD', 'BrownChipMain', 'grip', 'TokensWarContract', 'Dentacoin', 'LAAR', 'INRD', 'UniondaoDollarToken', 'Genaro', 'CSTK_CLT', 'Yihaa', 'IgfContract', 'Scale']
num=0
pair_num_ordered={}
pair_ordered={}
for fn in glob.glob('/home/cyma/pycharm_project/TransRacer/TransRacer/reports/callable_funcs/*.txt'):
    addr=fn[-42-4:-4]
    if addr in addr2name:
        name=addr2name[addr]
        num+=1
        ind=names_ordred.index(name)
        with open(fn,'r') as fnn:
            r1=fnn.readline()
            r2=fnn.readline()
            r3 = fnn.readline()
            all_funcs=ast.literal_eval(r3[len('function_pairs_list:'):])
            pair_num_ordered[ind]=len(all_funcs)
            pair_ordered[ind]=all_funcs
covs={}
failed_d={}
n2cov_str0={}
for addr,name in addr2name.items():
    ind=names_ordred.index(name)
    try:
        with open('../reports_50/callable_funcs/'+addr+'.txt','r') as fr:
            rr=fr.readline()
            funcs=ast.literal_eval(rr[len('callable funcs:'):])
            num=0
            all_funcs=pair_ordered[ind]
            failed=set()
            for elem in all_funcs:
                if elem[0] in funcs and elem[1] in funcs:
                    num+=1
                else:
                    failed.add(elem)

            cov=num/len(all_funcs)
            cov_str=int(num/len(all_funcs)*1000)/10
            n2cov_str0[name] = str(num) + '/' + str(len(all_funcs)) + '=' +str(cov_str)+"%"
            covs[ind]=cov
            failed_d[ind]=failed
    except:
        print()
print(covs)
print(sum(covs.values())/50)
cov_str0_ordered=[]
for i in range(50):
    if i in covs:
        cov_str0_ordered.append(str(int(covs[i]*100*10)/10))

# print('covs:',covs)

for i in range(50):
    order[i].append(cov_str0_ordered[i])
    str0=''
    for i_th,k in enumerate(order[i]):
        str0=str0+str(k)+" "

    print(str0)

n0=0;n1=0;n2=0;n3=0
for addr,nums in addr2race_num.items():
    n0+=nums[0]
    n1 += nums[1]
    n2 += nums[2]
    n3 += nums[3]
print('races:',n0,n1,n2,n3)
print('total:',n0+n1+n2+n3)
n0=0;n1=0;n2=0;n3=0
for addr,nums in addr2race_bug_num.items():
    n0+=nums[0]
    n1 += nums[1]
    n2 += nums[2]
    n3 += nums[3]

print('race_bugs:',n0,n1,n2,n3)
print('total:',n0+n1+n2+n3)
print('average covs:',sum(covs.values())/50)
print('total time',int(total/60*10)/10)
print('average time',int(total/60*10)/10/50)