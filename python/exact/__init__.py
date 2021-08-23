# This file is part of the Exact program
#
# Copyright (c) 2021 Jo Devriendt, KU Leuven
#
# Exact is distributed under the terms of the MIT License.
# You should have received a copy of the MIT License along with Exact.
# See the file LICENSE.

__version__ = "0.3.1"
__author__ = 'Jo Devriendt'

import os

file_dir = os.path.dirname(__file__)

import cppyy
cppyy.include(file_dir+'/headers/Exact.hpp')
cppyy.load_library(file_dir+'/libExact')

from cppyy.gbl import Exact
