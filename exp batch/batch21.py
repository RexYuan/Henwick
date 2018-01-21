from poset_cover import poset_cover

import logging
import os

from random import choice
from time import time

# 15 minutes
timeout = 900000
# status dir path
status_path = '../'
# trial dir path
trial_path = '../trials/'
# batch numbering (1~9)
batch = 21
# element count (6,8,10)
ele_count = 8
# linearization count (60,80,100)
lin_count = 50

overall_logger = logging.getLogger('batch '+str(batch))
overall_logger.setLevel(logging.INFO)

status_fh = logging.FileHandler(status_path+'status.txt')
status_fh.setLevel(logging.INFO)
status_formatter = logging.Formatter('[%(levelname)s] %(asctime)s : %(name)s : %(message)s')
status_fh.setFormatter(status_formatter)
overall_logger.addHandler(status_fh)

logger = logging.getLogger('poset_cover')
logger.setLevel(logging.DEBUG)

timeout_fh = logging.FileHandler(status_path+'timeout_log.txt')
timeout_fh.setLevel(logging.WARNING)
logger.addHandler(timeout_fh)

# run a batch of 50 trials
for trial in range(50*(batch-1)+1, 50*batch+1):
    os.makedirs(os.path.dirname(trial_path+"trial_{:0>3}/log.txt".format(trial)), exist_ok=True)

    log_fh = logging.FileHandler(trial_path+"trial_{:0>3}/log.txt".format(trial))
    log_fh.setLevel(logging.DEBUG)
    log_formatter = logging.Formatter('[%(levelname)s] %(asctime)s : %(message)s')
    log_fh.setFormatter(log_formatter)
    logger.addHandler(log_fh)

    n = ele_count # the number of elements
    y = lin_count # the number of linearizations

    s = list(map(str,range(n)))
    lins = [''.join(s)]
    while len(lins) < y:
        ext = list(choice(lins))
        swap = choice(list(range(n-1)))
        s = s[:swap]+[s[swap+1]]+[s[swap]]+s[swap+2:]
        if ''.join(s) not in lins:
            lins.append(''.join(s))

    ret = poset_cover(lins, timeout=timeout, runaway_timeout=True, render=True, dir=trial_path+"trial_{:0>3}".format(trial))
    if ret == None:
        overall_logger.info('Trial '+str(trial)+' timed out.')
    else:
        overall_logger.info('Trial '+str(trial)+' done.')

    logger.removeHandler(log_fh)
