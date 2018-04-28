
import logging
import sys
import pickle
from multiprocessing import Pool
from itertools import repeat, islice
from time import time

import pymysql.cursors

from census99_attr import *

log_path = '../catlog'
pickle_path = '../ret.p'

def get_value(fields):
    connection = pymysql.connect(host='localhost',
                                 user='rex',
                                 password='rex',
                                 db='census99',
                                 cursorclass=pymysql.cursors.DictCursor)

    with connection.cursor() as cursor:
        sql = ("SELECT DISTINCT {}"+",{}"*(len(fields)-1)+" FROM PEOPLE").format(*fields)
        cursor.execute(sql)
        result = cursor.fetchone()

        while result:
            yield result
            result = cursor.fetchone()

    connection.close()

def get_row(fvalues):
    clause = ''
    for f, v in fvalues.items():
        clause += " {}={} AND".format(f, v)
    clause = clause[1:-4]

    while True:
        try:
            connection = pymysql.connect(host='localhost',
                                         user='rex',
                                         password='rex',
                                         db='census99',
                                         cursorclass=pymysql.cursors.DictCursor)

            with connection.cursor() as cursor:
                sql = ("SELECT COUNT(*) FROM PEOPLE WHERE {}").format(clause)
                cursor.execute(sql)
                result = cursor.fetchone()
                row_count = list(result.values())[0]

            connection.close()
        except:
            continue
        break
    #print(connection.open, flush=True)

    logger = logging.getLogger("field[{}]".format(fvalues))
    logger.setLevel(logging.DEBUG)

    status_fh = logging.FileHandler(log_path)
    status_sh = logging.StreamHandler()

    status_fh.setLevel(logging.INFO)
    status_sh.setLevel(logging.DEBUG)

    status_formatter = logging.Formatter('[%(levelname)s] %(asctime)s : %(name)s : %(message)s')
    status_fh.setFormatter(status_formatter)
    status_sh.setFormatter(status_formatter)

    logger.addHandler(status_fh)
    #logger.addHandler(status_sh)

    logger.info(str(row_count))

    return row_count

if __name__ == '__main__':
    fields = [('C020_AGE', 'C060_REL_HEAD', 'C072_EDUCATION', 'C122_INDUSTRY', 'C123_OCCUPATION')]

    procs = 30

    for field in fields:
        tt = time()

        with Pool(processes=procs) as pool:
            ret = pool.map(get_row, get_value(field),10)
            pickle.dump(ret, open(pickle_path, "wb"))

        print("Time: "+str(time()-tt))
