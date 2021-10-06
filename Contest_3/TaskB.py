s = input()
n = len(s)
dp = [[0 for _ in range(n)] for _ in range(n)]
if s[0] == '(' or s[0] == '?':
	dp[0][1] = 1
for i in range(1, n):
	if s[i] == '?':
		dp[i][0] = dp[i - 1][1]
		for j in range(1, n - 1):
			dp[i][j] = dp[i - 1][j - 1] + dp[i - 1][j + 1]
		dp[i][n - 1] = dp[i - 1][n - 2]
	elif s[i] == ')':
		for j in range(0, n - 1):
			dp[i][j] = dp[i - 1][j + 1]
	else:
		for j in range(1, n):
			dp[i][j] = dp[i - 1][j - 1]
print(dp[n - 1][0])