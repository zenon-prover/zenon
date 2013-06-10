#!/usr/bin/env python

import resource, sys, os

TIMEOUT = 1
resource.setrlimit(resource.RLIMIT_CPU, (TIMEOUT, TIMEOUT))
os.execvp(sys.argv[1], sys.argv[1:])
