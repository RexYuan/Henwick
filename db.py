from time import time
from itertools import combinations
from random import shuffle
from functools import reduce
from multiprocessing import Pool

import pymysql.cursors

insert_command = """
    INSERT INTO people (
    C010_GENDER       , C020_AGE                , C031_TAIWANESE   ,
    C032_NATIONALITY  , C040_FOREIGN_WORKER     , C050_MARRIAGE    ,
    C060_REL_HEAD     , C071_ED_STATUS          , C072_EDUCATION   ,
    C073_KINDERGARDEN , C081_6H_CHINESE         , C082_6H_MINNAN   ,
    C083_6H_HAKKA     , C084_6H_ABORIGINAL      , C085_6H_OTHER    ,
    C091_6P_CHINESE   , C092_6P_MINNAN          , C093_6P_HAKKA    ,
    C094_6P_ABORIGINAL, C095_6P_OTHER           , C100_5Y_RESIDENCE,
    C110_MAIN_INCOME  , C121_EMPLOYMENT         , C122_INDUSTRY    ,
    C123_OCCUPATION   , C131_WS_STATUS          , C132_WS_LOCATION ,
    C141_OFFSPRING    , C142_OFFSPRING_RESIDENCE, C151_DIS_EAT     ,
    C152_DIS_BED      , C153_DIS_CLOTHES        , C154_DIS_TOILET  ,
    C155_DIS_SHOWER   , C156_DIS_OWALK          , C157_DIS_CHORE   ,
    C158_DIS_NONE     , C160_ABORIGINAL         , C170_DISABLED)
    VALUES (
    %s, %s, %s,
    %s, %s, %s,
    %s, %s, %s,
    %s, %s, %s,
    %s, %s, %s,
    %s, %s, %s,
    %s, %s, %s,
    %s, %s, %s,
    %s, %s, %s,
    %s, %s, %s,
    %s, %s, %s,
    %s, %s, %s,
    %s, %s, %s)
"""

fields = (
    'C010_GENDER'       , 'C020_AGE'                , 'C031_TAIWANESE'   ,
    'C032_NATIONALITY'  , 'C040_FOREIGN_WORKER'     , 'C050_MARRIAGE'    ,
    'C060_REL_HEAD'     , 'C071_ED_STATUS'          , 'C072_EDUCATION'   ,
    'C073_KINDERGARDEN' , 'C081_6H_CHINESE'         , 'C082_6H_MINNAN'   ,
    'C083_6H_HAKKA'     , 'C084_6H_ABORIGINAL'      , 'C085_6H_OTHER'    ,
    'C091_6P_CHINESE'   , 'C092_6P_MINNAN'          , 'C093_6P_HAKKA'    ,
    'C094_6P_ABORIGINAL', 'C095_6P_OTHER'           , 'C100_5Y_RESIDENCE',
    'C110_MAIN_INCOME'  , 'C121_EMPLOYMENT'         , 'C122_INDUSTRY'    ,
    'C123_OCCUPATION'   , 'C131_WS_STATUS'          , 'C132_WS_LOCATION' ,
    'C141_OFFSPRING'    , 'C142_OFFSPRING_RESIDENCE', 'C151_DIS_EAT'     ,
    'C152_DIS_BED'      , 'C153_DIS_CLOTHES'        , 'C154_DIS_TOILET'  ,
    'C155_DIS_SHOWER'   , 'C156_DIS_OWALK'          , 'C157_DIS_CHORE'   ,
    'C158_DIS_NONE'     , 'C160_ABORIGINAL'         , 'C170_DISABLED')

ordered_fields = [
     ('C010_GENDER', 2), ('C031_TAIWANESE', 2), ('C040_FOREIGN_WORKER', 2),
     ('C081_6H_CHINESE', 2), ('C082_6H_MINNAN', 2), ('C083_6H_HAKKA', 2),
     ('C084_6H_ABORIGINAL', 2), ('C085_6H_OTHER', 2), ('C091_6P_CHINESE', 2),
     ('C092_6P_MINNAN', 2), ('C093_6P_HAKKA', 2), ('C094_6P_ABORIGINAL', 2),
     ('C095_6P_OTHER', 2), ('C151_DIS_EAT', 2), ('C152_DIS_BED', 2),
     ('C153_DIS_CLOTHES', 2), ('C154_DIS_TOILET', 2), ('C155_DIS_SHOWER', 2),
     ('C156_DIS_OWALK', 2), ('C157_DIS_CHORE', 2), ('C158_DIS_NONE', 2),
     ('C073_KINDERGARDEN', 3), ('C110_MAIN_INCOME', 3), ('C121_EMPLOYMENT', 3),
     ('C131_WS_STATUS', 3), ('C160_ABORIGINAL', 3), ('C170_DISABLED', 3),
     ('C132_WS_LOCATION', 4), ('C050_MARRIAGE', 5), ('C071_ED_STATUS', 5),
     ('C142_OFFSPRING_RESIDENCE', 6), ('C141_OFFSPRING', 7), ('C100_5Y_RESIDENCE', 8),
     ('C032_NATIONALITY', 10), ('C072_EDUCATION', 11), ('C060_REL_HEAD', 12),
     ('C020_AGE', 17), ('C123_OCCUPATION', 39), ('C122_INDUSTRY', 80)]

goal_distinct_rows = 1364624

def get_row_count(fields):
    connection = pymysql.connect(host='localhost',
                             user='root',
                             password='',
                             db='census99',
                             cursorclass=pymysql.cursors.DictCursor)
    with connection.cursor() as cursor:
        sql = ("SELECT COUNT(DISTINCT {}"+",{}"*(len(fields)-1)+") FROM people").format(*fields)
        cursor.execute(sql)
        result = cursor.fetchone()
        row_count = list(result.values())[0]
    connection.close()
    if row_count >= goal_distinct_rows:
        print(fields)
        return True
    else:
        return False

if __name__ == '__main__':
    with Pool(processes=3) as pool:
        ret = pool.map(get_row_count, combinations(fields, 38))
        print(any(ret))









'''
p.map(f, [1,2,3])


    ordered_fields = list(reversed(list(map(lambda x:x[0], ordered_fields))))
    froma = ordered_fields
    shuffle(froma)
    choose = 39

    froma = ordered_fields
    choose = 39
    while True:
        max_row = 0
        max_fs = None
        found = False
        for fs in combinations(froma, choose):
            sql = ("SELECT COUNT(DISTINCT {}"+",{}"*(choose-1)+") FROM people").format(*fs)
            cursor.execute(sql)
            result = cursor.fetchone()
            rows = list(result.values())[0]
            #discount[fs] = rows
            if rows > max_row:
                max_row = rows
                max_fs = fs
            if rows >= all_distinct_rows:
                print(choose, "~~~", fs)
                froma = list(fs)
                choose -= 1
                found = True
                break
        if not found:
            ret.append(choose+1)
            print(choose, "~~~ no more")
            break

connection.close()

print(reduce(lambda x,y:x==y,ret),ret)
print(time()-t1)
#print(discount)
#print(max_fs)
#print(max_row)

#####################

with connection.cursor() as cursor:
    for fs in combinations(fields, 3):
        sql = "SELECT COUNT(DISTINCT {}, {}, {}) FROM people".format(*fs)
        cursor.execute(sql)
        result = cursor.fetchone()
        discount[fs] = result["COUNT(DISTINCT {}, {}, {})".format(*fs)]
        if result["COUNT(DISTINCT {}, {}, {})".format(*fs)] > max_row:
            max_row = result["COUNT(DISTINCT {}, {}, {})".format(*fs)]
            max_fs = fs

print(discount)
print(max_fs)
print(max_row)


####################


with open('people.txt') as fp:
    s = fp.readline()
    while s != '':
        T100 = s[0:7]
        T200 = s[7:14]
        FILLER = s[14:15]
        T300 = s[15:16]
        C010 = s[16:17]
        C020 = s[17:19]
        C031 = s[19:20]
        C032 = s[20:21]
        C040 = s[21:22]
        C050 = s[22:23]
        C060 = s[23:25]
        C071 = s[25:26]
        C072 = s[26:28]
        C073 = s[28:29]
        C081 = s[29:30]
        C082 = s[30:31]
        C083 = s[31:32]
        C084 = s[32:33]
        C085 = s[33:34]
        C091 = s[34:35]
        C092 = s[35:36]
        C093 = s[36:37]
        C094 = s[37:38]
        C095 = s[38:39]
        C100 = s[39:40]
        FILLER = s[40:42]
        C110 = s[42:43]
        C121 = s[43:44]
        FILLER = s[44:45]
        C122 = s[45:47]
        C123 = s[47:49]
        C131 = s[49:50]
        C132 = s[50:51]
        FILLER = s[51:53]
        C141 = s[53:54]
        C142 = s[54:55]
        C151 = s[55:56]
        C152 = s[56:57]
        C153 = s[57:58]
        C154 = s[58:59]
        C155 = s[59:60]
        C156 = s[60:61]
        C157 = s[61:62]
        C158 = s[62:63]
        C160 = s[63:64]
        C170 = s[64:65]
        FILLER = s[65:66]
        EX3 = s[66:70]

        args = (
        C010, C020, C031,
        C032, C040, C050,
        C060, C071, C072,
        C073, C081, C082,
        C083, C084, C085,
        C091, C092, C093,
        C094, C095, C100,
        C110, C121, C122,
        C123, C131, C132,
        C141, C142, C151,
        C152, C153, C154,
        C155, C156, C157,
        C158, C160, C170)

        with connection.cursor() as cursor:
            cursor.execute(insert_command, args)

        connection.commit()

        with connection.cursor() as cursor:
            sql = "SELECT C110_MAIN_INCOME, C131_WS_STATUS FROM people"
            cursor.execute(sql)
            result = cursor.fetchall()
            print(result)


        s = fp.readline()
'''
