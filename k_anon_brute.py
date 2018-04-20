
from multiprocessing import Pool
from itertools import combinations, repeat

import pymysql.cursors

from census99_attr import *

def check_fields(fields, goal):
    connection = pymysql.connect(host='localhost',
                                 user='rex',
                                 password='rex',
                                 db='census99',
                                 cursorclass=pymysql.cursors.DictCursor)
    with connection.cursor() as cursor:
        sql = ("SELECT COUNT(DISTINCT {}"+",{}"*(len(fields)-1)+") FROM PEOPLE").format(*fields)
        cursor.execute(sql)
        result = cursor.fetchone()
        row_count = list(result.values())[0]
    connection.close()
    if row_count >= goal:
        return fields
    else:
        return False

if __name__ == '__main__':
    goal = int(max_distinct_rows * 0.1)
    choose = 5
    procs = 30

    print('====> size 5')
    with Pool(processes=procs) as pool:
        ret = pool.starmap(check_fields, zip(combinations(fields, choose), repeat(goal)))
        list(map(print, filter(None, ret)))
        print(any(ret))

    choose = 4
    print('\n\n====> size 4')
    with Pool(processes=procs) as pool:
        ret = pool.starmap(check_fields, zip(combinations(fields, choose), repeat(goal)))
        list(map(print, filter(None, ret)))
        print(any(ret))
