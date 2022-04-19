# This file is part of Exact.
#
# Copyright (c) 2022 Jo Devriendt
#
# Exact is free software: you can redistribute it and/or modify it under
# the terms of the GNU Affero General Public License version 3 as
# published by the Free Software Foundation.
#
# Exact is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE. See the GNU Affero General Public
# License version 3 for more details.
#
# You should have received a copy of the GNU Affero General Public
# License version 3 along with Exact. See the file used_licenses/COPYING
# or run with the flag --license=AGPLv3. If not, see
# <https://www.gnu.org/licenses/>.

#######################################################################

# This file is part of the Exact program
#
# Copyright (c) 2021 Jo Devriendt, KU Leuven
#
# Exact is distributed under the terms of the MIT License.
# You should have received a copy of the MIT License along with Exact.
# See the file LICENSE.


from setuptools import setup

setup(
    name='Exact',
    version = "0.5.1",
    description='A Python interface to Exact',
    url='https://gitlab.com/JoD/exact',
    author='Jo Devriendt',
    license='AGPLv3',
    packages=['exact'],
    package_dir={'exact': 'exact'},
    package_data={'exact': ['libExact.so','headers/*.hpp','headers/*/*.hpp']},
    install_requires=['cppyy'],

    classifiers=[
        'Development Status :: 1 - Planning',
        'License :: OSI Approved :: GNU Affero General Public License v3',
        'Operating System :: POSIX :: Linux',
        'Programming Language :: Python :: 3',
    ],
)
