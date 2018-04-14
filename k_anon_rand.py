
import logging
from multiprocessing import Pool
from itertools import combinations, repeat, islice, count
from random import shuffle
from time import time

import pymysql.cursors

from census99_attr import *

def min_qid(id, fields, goal):
    t1 = time()

    logger = logging.getLogger("query[{:0>2}]".format(id))
    logger.setLevel(logging.INFO)

    status_fh = logging.FileHandler('k_status.txt')
    status_sh = logging.StreamHandler()

    status_fh.setLevel(logging.INFO)
    status_sh.setLevel(logging.INFO)

    status_formatter = logging.Formatter('[%(levelname)s] %(asctime)s : %(name)s : %(message)s')
    status_fh.setFormatter(status_formatter)
    status_sh.setFormatter(status_formatter)

    logger.addHandler(status_fh)
    logger.addHandler(status_sh)

    connection = pymysql.connect(host='localhost',
                                 user='rex',
                                 password='rex',
                                 db='census99',
                                 cursorclass=pymysql.cursors.DictCursor)

    with connection.cursor() as cursor:
        froma = fields
        choose = 39

        while True:
            found = False
            logger.info(choose)

            for fs in combinations(froma, choose):
                sql = ("SELECT COUNT(DISTINCT {}"+",{}"*(choose-1)+") FROM people").format(*fs)
                cursor.execute(sql)
                result = cursor.fetchone()
                row_count = list(result.values())[0]

                if row_count >= goal:
                    froma = fs
                    choose -= 1
                    found = True
                    break

            if not found:
                break

    connection.close()
    logger.critical("Time: "+str(time()-t1))
    return choose+1

def shuffled(fields):
    tmp = list(fields)
    while True:
        yield tmp
        shuffle(tmp)

if __name__ == '__main__':
    goal = max_distinct_rows * 0.5
    trials = 3
    with Pool(processes=3) as pool:
        ret = pool.starmap(min_qid, zip(count(1), islice(shuffled(fields), trials), repeat(goal)))
        print(list(filter(None, ret)))
