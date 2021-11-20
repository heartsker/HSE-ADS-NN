/*
 * Created by heartsker.
 * Do not judge strictly.
 */

//  ----------------    INCLUDES    ----------------    //

#include <iostream>
#include <fstream>
#include <iomanip>
#include <cmath>
#include <string>
#include <vector>
#include <set>
#include <map>
#include <unordered_set>
#include <unordered_map>
#include <queue>
#include <deque>
#include <algorithm>
#include <tuple>

using namespace std;

//  ----------------    TYPEDEFS    ----------------    //

typedef long long ll;
typedef long double ld;
typedef pair<ll, ll> ii;
typedef pair<ld, ld> dd;
typedef vector<ll> vi;
typedef vector<ld> vd;
typedef vector<bool> vb;
typedef vector<string> vs;
typedef vector<ii> vii;
typedef vector<dd> vdd;
typedef vector<vi> vvi;
typedef vector<vb> vvb;
typedef set<ll> si;
typedef set<string> ss;
typedef map<ll, ll> mii;
typedef map<string, ll> msi;
typedef map<ll, string> mis;
typedef map<ll, vi> mivi;
typedef queue<ll> qi;
typedef queue<ii> qii;

//  ----------------    MACROS      ----------------    //

#define forin(x) for (auto &t : (x))
#define fori(x) for (ll i = 0; i < (x); i++)
#define forj(x) for (ll j = 0; j < (x); j++)
#define xfor(i, a, b) for (ll i = (a); (i) < (b); (i)++)
#define xford(i, a, b) for (ll i = (a); (i) >= (b); (i)--)
#define improve(a, b) a = max((ll)(a), (ll)(b))
#define deprove(a, b) a = min((ll)(a), (ll)(b))
#define is_2_power(x) ((x) && (!((x) & ((x) - 1)))
#define sqr(x) ((x) * (x))
#define uniq(x) ((x).resize(unique(all(x)) - (x).begin()))
#define fastIO() ios::sync_with_stdio(false); In.tie(NULL); Out.tie(NULL)
#define dbg(x) cout << (#x) << " --> " << (x) << endl
#define get_time { (clock() / (double) CLOCKS_PER_SEC) }
#define in(x) forin(x) In >> t
#define out(x) forin(x) Out << t << ' '
#define precision(x) Out << fixed << setprecision(x);
#define all(x) (x).begin(), (x).end()
#define dosort(x) sort(all(x))
#define doreverse(x) reverse(all(x))
#define doperm(x) next_permutation(all(x))
#define get(x) ll x; In >> (x)
#define prt(x) Out << (x)
#define endl '\n'
#define sz size()
#define min3(a, b, c) min(ll(a), min(ll(b), ll(c)))
#define max3(a, b, c) max(ll(a), max(ll(b), ll(c)))
#define abs0(x) max(L0, ll(x))
#define close_int(x) (ll)((ld)(x) + 0.5)
#define fi first
#define se second

//  ----------------    CONSTS      ----------------    //

const ld ZERO = 1e-15;
const ld EPS = 1e-10;
const ll N = 1005;
const ll MOD = 1000000007;
const ll INF9 = 1e9;
const ll INF = 1e18;
const ll L0 = 0;
const ll L1 = 1;
const ld PI = acos(-1);

//  ----------------    FUNCTIONS   ----------------    //

// returns whether the number is prime
bool is_prime(ll n) {
    if (n <= 1) return false;
    ll cnt = 0;
    for (ll i = 2; i * i <= n; i++) cnt += !(n % i);
    return !cnt;
}

// returns (a ^ p) % m
ll modulo_power(ll a, ll p, ll m) {
    ll x = 1;
    ll y = a;
    while (p > 0) {
        if (p & 1) x = (x * y) % m;
        y = (y * y) % m;
        p >>= 1;
    }
    return x % m;
}

// returns (a * b) % m
ll mult(ll a, ll b, ll m = INF) {
    if (!a || !b) return 0;
    if (a & 1) return (b + mult(a-1, b, m)) % m;
    return (mult(a / 2, b, m) * 2) % m;
}

// returns sorted list of all prime divisors of number
vi prime_divisors(ll number) {
    vi divisors;
    if (number % 2 == 0) {
        divisors.push_back(2);
        while (!(number % 2)) number /= 2;
    }
    ll start_number = number;
    for (ll p = 3; p <= number && p * p <= start_number; p += 2) {
        if (number % p) continue;
        divisors.push_back(p);
        while (!(number % p)) number /= p;
    }
    if (number - 1) divisors.push_back(number);
    return divisors;
}

// returns GCD(a, b) [GCD(0, 0) = 1]
ll gcd(ll a, ll b) {
    if (!(a || b)) return 1;
    return (b ? gcd(b, a % b) : a);
}

// returns number of combination for N choose K
ll combinations(ll n, ll k) {
    return (k && n - k) ? combinations(n - 1, k) + combinations(n - 1, k - 1) : 1;
}

// z[i] is length of the longest common prefix and i-th suffix
// z[0] = 0
vi z_func(vi& v) {
    ll n = v.size();
    vi z(n);
    for (ll i=1, l=0, r=0; i<n; ++i) {
        if (i <= r) z[i] = min(r - i + 1, z[i - l]);
        while (i + z[i] < n && v[z[i]] == v[i + z[i]]) ++z[i];
        if (i + z[i] - 1 > r) l = i, r = i + z[i] -1;
    }
    return z;
}

// returns factorisation of number
vii prime_divisors_extended(ll number) {
    vii divisors;
    if (number % 2 == 0) {
        ll cnt = 0;
        while (number % 2 == 0) { number /= 2; ++cnt; }
        if (cnt) divisors.push_back({2, cnt});
    }
    ll start_number = number;
    for (ll p = 3; p <= number && p * p <= start_number; p += 2) {
        ll cnt = 0;
        while (number % p == 0) { number /= p; ++cnt; }
        if (cnt) divisors.push_back({p, cnt});
    }
    if (number != 1) divisors.push_back({number, 1});
    return divisors;
}

// returns list of all divisors of number
vi all_divisors(ll number) {
    vi divisors;
    if (number % 2 == 0) {
        divisors.push_back(2);
        if (4 != number) { divisors.push_back(number / 2); }
    }
    for (ll p = 3; p * p <= number; p += 2) {
        ll t = p;
        if (number % t == 0) {
            divisors.push_back(p);
            if (p * p != number) { divisors.push_back(number / p); }
        }
    }
    return divisors;
}

// returns cycle permutation (1234)->(2341) [step = 1]
void cycle_perm_with_step(string& s, ll step) {
    char f = s[0];
    fori(s.size()) {
        s[i] = s[(i + step) % s.sz];
    }
    s[s.sz - step] = f;
}

// returns cycle permutation (1234)->(2341)
void cycle_perm(string& s) {
    cycle_perm_with_step(s, 1);
}

// returns factorial of N (N!)
ll factorial(ll n) {
    return (n > 1) ? n * factorial(n - 1) : 1;
}

//  ----------------    FILES       ----------------    //

//#define FILEINOUT
#ifdef FILEINOUT
ifstream In("Input.txt");
ofstream Out("Output.txt");
#else
#define In cin
#define Out cout
#endif

//  ----------------    CODE        ----------------    //

inline void solve() {
    string s; In >> s;

    ll n = s.size();

    vi dp(n, 0);
    if (s[0] == '0') {
        Out << 0; return;
    }
    dp[0] = 1;

    xfor(i, 1, n) {
        ll p = s[i - 1] - '0';
        ll d = s[i] - '0';

        ll t = 10 * p + d;

        if (d) dp[i] += dp[i - 1];

        if (0 < t && t < 27 && p) {
            if (i > 1) dp[i] += dp[i - 2];
            else dp[i]++;
        }
    }

    Out << dp[n - 1];

}

signed main() {
    fastIO();
    precision(2);
    setlocale(LC_ALL, "");
    srand(time(nullptr));

    solve();

    return 0;
}