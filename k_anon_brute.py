
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
        sql = ("SELECT COUNT(DISTINCT {}"+",{}"*(len(fields)-1)+") FROM people").format(*fields)
        cursor.execute(sql)
        result = cursor.fetchone()
        row_count = list(result.values())[0]
    connection.close()
    if row_count >= goal:
        return fields
    else:
        return False

if __name__ == '__main__':
    goal = max_distinct_rows
    choose = 39
    with Pool(processes=3) as pool:
        ret = pool.starmap(check_fields, zip(combinations(fields, choose), repeat(goal)))
        print(any(ret))
        list(map(print, filter(None, ret)))
