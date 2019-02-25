# Source: https://windelbouwman.wordpress.com/2013/07/24/profile-python-unittest/

import cProfile
import unittest
import pstats
 
if __name__ == '__main__':
    suite = unittest.TestLoader().discover('.', pattern='*_test.py')
    def runtests():
        unittest.TextTestRunner().run(suite)
    s = cProfile.run('runtests()',sort='cumtime')
