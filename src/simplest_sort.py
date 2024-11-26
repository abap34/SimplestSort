def simplest_sort(arr):
    n = len(arr)
    for i in range(n):
        for j in range(n):
            if arr[i] < arr[j]:
                arr[i], arr[j] = arr[j], arr[i]

    return arr


print(simplest_sort([1, 6, 8, 3, 5, 2, 9]))
