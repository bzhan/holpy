# Author: Bohua Zhan

"""Implementation of the union-find data structure."""

class UnionFind():
    """Union-find data structure."""

    def __init__(self):
        """Initialize an empty union-find data structure."""
        # Map from node to parent of that node. If the node is the root,
        # the value is None.
        self.parents = dict()

        # Map from node to size of subtree based at that node.
        self.size = dict()

    def __str__(self):
        res = ""
        for k, v in self.parents.items():
            res += str(k) + ": " + str(v) + "\n"
        return res 

    def has_key(self, item):
        """Whether the data structure has the given item as key."""
        return item in self.parents

    def insert(self, item):
        """Insert a new element."""
        assert item not in self.parents, "insert: item already in union-find."

        self.parents[item] = None
        self.size[item] = 1

    def find(self, item):
        """Find the representative of the element. Perform path-compression
        along the way.

        """
        assert item in self.parents, "find: item not in union-find."

        path = []
        while self.parents[item] != None:
            path.append(item)
            item = self.parents[item]

        for i in path:
            self.parents[i] = item

        return item

    def union(self, item1, item2, force_first=False):
        """Join the classes for the two items.
        
        If force_first is set to True, the root of item1 becomes the
        root of the whole tree even if the subtree at item2 is larger.
        
        """

        item1 = self.find(item1)
        item2 = self.find(item2)

        # Ensure the tree at item1 is larger or equal to tree at item2.
        if not force_first and self.size[item1] < self.size[item2]:
            item1, item2 = item2, item1

        self.parents[item2] = item1
        self.size[item1] += self.size[item2]
        self.size[item2] = None
