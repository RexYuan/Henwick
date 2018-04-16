
import logging
import sys
from multiprocessing import Pool
from itertools import combinations, repeat, islice, count
from random import shuffle
from time import time
from operator import mul

import pymysql.cursors

from census99_attr import *

status_path = 'k_status.txt'
log_path = 'k_log.txt'

def min_qid(trial, fields, goal):
    t1 = time()

    logger = logging.getLogger("goal[{:>7}]:trial[{:>2}]".format(goal, trial))
    logger.setLevel(logging.DEBUG)

    status_fh = logging.FileHandler(status_path)
    status_sh = logging.StreamHandler()

    status_fh.setLevel(logging.INFO)
    status_sh.setLevel(logging.DEBUG)

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
            logger.debug(choose)

            for fs in combinations(froma, choose):
                sql = ("SELECT COUNT(DISTINCT {}"+",{}"*(choose-1)+") FROM PEOPLE").format(*fs)
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
    logger.info("Time: "+str(time()-t1))
    return choose+1

def shuffled(fields):
    tmp = list(fields)
    while True:
        yield tmp.copy()
        shuffle(tmp)

if __name__ == '__main__':
    goal = max_distinct_rows
    facts = [0.1, 0.25, 0.5, 0.75, 1]
    goals = map(int, map(mul, facts, repeat(goal)))

    trials = 300

    procs = 3

    for goal in goals:
        tt = time()

        logger = logging.getLogger("goal[{:>7}]".format(goal))
        logger.setLevel(logging.DEBUG)

        status_fh = logging.FileHandler(log_path)
        status_sh = logging.StreamHandler()

        status_fh.setLevel(logging.INFO)
        status_sh.setLevel(logging.DEBUG)

        status_formatter = logging.Formatter('[%(levelname)s] %(asctime)s : %(name)s : %(message)s')
        status_fh.setFormatter(status_formatter)
        status_sh.setFormatter(status_formatter)

        logger.addHandler(status_fh)
        logger.addHandler(status_sh)

        def ex_log_handler(type, value, tb):
            logger.exception("Uncaught exception: {}".format(str(value)))
        sys.excepthook = ex_log_handler

        logger.info("Starting...")

        with Pool(processes=procs) as pool:
            ret = pool.starmap(min_qid, zip(count(1), islice(shuffled(fields), trials), repeat(goal)))
            logger.critical(ret)

        logger.info("Time: "+str(time()-tt))
