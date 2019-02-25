# Author: Bohua Zhan

import unittest

from util import unionfind

class UnionFindTest(unittest.TestCase):
    def testUnionFind(self):
        uf = unionfind.UnionFind()
        for i in range(10):
            uf.insert(i)
        uf.union(0,1)
        uf.union(2,3)
        uf.union(4,5)
        uf.union(6,7)
        uf.union(8,9)
        uf.union(0,2)
        uf.union(4,6)
        self.assertEqual(uf.find(0), uf.find(3))
        self.assertNotEqual(uf.find(0), uf.find(5))
        uf.union(0,4)
        self.assertEqual(uf.find(0), uf.find(5))
        self.assertNotEqual(uf.find(0), uf.find(8))

    def testForceFirst(self):
        uf = unionfind.UnionFind()
        for i in range(3):
            uf.insert(i)
        uf.union(1,2)
        self.assertEqual(uf.find(2), 1)
        uf.union(0,1,force_first=True)
        self.assertEqual(uf.find(2), 0)


if __name__ == "__main__":
    unittest.main()
