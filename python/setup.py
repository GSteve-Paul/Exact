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
    version='0.2.1',
    description='A Python interface to Exact',
    url='https://gitlab.com/JoD/exact',
    author='Jo Devriendt',
    license='MIT',
    packages=['exact'],
    package_dir={'exact': 'exact'},
    package_data={'exact': ['libExact.so','headers/*.hpp','headers/*/*.hpp']},
    install_requires=['cppyy'],

    classifiers=[
        'Development Status :: 1 - Planning',
        'License :: OSI Approved :: MIT License',
        'Operating System :: POSIX :: Linux',
        'Programming Language :: Python :: 3',
    ],
)
