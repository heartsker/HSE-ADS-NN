/*
 * Created by heartsker.
 * Do not judge strictly.
 */

//  ----------------    INCLUDES    ----------------    //

#pragma GCC optimize("Ofast,no-stack-protector")
#pragma GCC target("sse,sse2,sse3,sse3,sse4")
#pragma GCC optimize("unroll-loops")
#pragma GCC optimize("fast-math")

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

typedef short int ll;
typedef pair<ll, ll> ii;

//  ----------------    MACROS      ----------------    //

#define forin(x) for (auto &t : (x))
#define fori(x) for (ll i = 0; i < (x); i++)
#define forj(x) for (ll j = 0; j < (x); j++)
#define xfor(i, a, b) for (ll i = (a); (i) < (b); (i)++)
#define xford(i, a, b) for (ll i = (a); (i) >= (b); (i)--)
#define improve(a, b) a = max((ll)(a), (ll)(b));
#define deprove(a, b) a = min((ll)(a), (ll)(b));
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

const ll N = 500;
const ll INF = 28928;

#define In cin
#define Out cout

//  ----------------    CODE        ----------------    //

bool field[N][N];
int bombs[N][N];
int dist[N][N];
ii from[N][N];

inline void solve() {
    get(n); get(m); get(k);
    char c;

    fori(n) forj(m) {
            In >> c; field[i][j] = c == 'x';
            bombs[i][j] = -INF;
            dist[i][j] = INF;
            from[i][j] = { -1, -1};
        }

    ii start; In >> start.fi >> start.se;
    ii finish; In >> finish.fi >> finish.se;

    dist[start.fi][start.se] = 0;
    bombs[start.fi][start.se] = k;

    queue<ii> q;
    q.push(start);

    ll dx[8] = {-2, -2, -1, -1, 1, 1, 2, 2};
    ll dy[8] = {-1, 1, -2, 2, -2, 2, -1, 1};

    while (!q.empty()) {
        ii now = q.front(); q.pop();

        fori(8) {
            ii t = {now.fi + dx[i], now.se + dy[i]};

            if (!(min(t.fi, t.se) >= 0 && t.fi < n && t.se < m)) continue;

            if (!bombs[now.fi][now.se] && field[t.fi][t.se]) continue;

            if (dist[t.fi][t.se] > dist[now.fi][now.se] + 1 ||
                dist[t.fi][t.se] == dist[now.fi][now.se] + 1 && bombs[t.fi][t.se] < bombs[now.fi][now.se] - field[t.fi][t.se]) {
                from[t.fi][t.se] = now;
                bombs[t.fi][t.se] = bombs[now.fi][now.se] - field[t.fi][t.se];
                dist[t.fi][t.se] = dist[now.fi][now.se] + 1;
                q.push(t);
            }
        }
    }

    if (dist[finish.fi][finish.se] == INF) {
        Out << -1;
    } else {
        Out << dist[finish.fi][finish.se] << endl;
        Out << k - bombs[finish.fi][finish.se] << endl;
        vector<ii> path;
        while (finish.fi >= 0) {
            path.push_back(finish);
            finish = from[finish.fi][finish.se];
        }
        doreverse(path);
        forin(path) Out << t.first << ' ' << t.second << endl;
    }
}

signed main() {
    fastIO();

    solve();

    return 0;
}