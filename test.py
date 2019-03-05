# Source: https://windelbouwman.wordpress.com/2013/07/24/profile-python-unittest/

# import cProfile
# import unittest
# import pstats
#
# if __name__ == '__main__':
#     suite = unittest.TestLoader().discover('.', pattern='*_test.py')
#     def runtests():
#         unittest.TextTestRunner().run(suite)
#     s = cProfile.run('runtests()',sort='cumtime')
#
# nums = [1,1,2,3,4,5,5,5,7,8,5,3]
# def list_set(nums):
#     a=0
#     for i, v in enumerate(nums):
#         if v in nums[i+1:]:
#             a += 1
#         for i in range(a):
#             nums.remove(v)
#         break
#     for i, v in enumerate(nums):
#         if v not in nums[i+1:]:
#             continue
#         else:
#             list_set(nums)
#     print(nums)


# list_set(nums)
# list = [1,2,3]
# print(list[0:2])
def test(nums):
    if nums == []:
        return 0
    for i, v in enumerate(nums):
        if i == len(nums) - 1:
            break
        for j, k in enumerate(nums[i+1:]):
            if k != v:
                nums = nums[0:i+1] + nums[i+1:][j:]
                break
            else:
                if j == len(nums[i+1:])-1:
                    nums = nums[0:i+1]
                    break
                continue

    return nums
        # for j, k in enumerate(nums[i+1:]):
        #     if k != v:
        #         nums = nums[i+1:][k-1:]
        #         break
        #     else:
        #         if j == len(nums[i + 1:]) - 1:
        #             nums = nums[0:i + 1]
        #             break
        # return nums
nums=[1,1,2,2,2,2,2,3,4,4,4,4,4]
print(test(nums))