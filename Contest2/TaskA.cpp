//
// Created by Daniel Pustotin on 23.09.2021.
//

#include <iostream>
#include <vector>
#include <fstream>
#include <queue>
#include <algorithm>

using namespace std;

typedef long long ll;
typedef pair<ll, ll> ii;
typedef vector<ll> vi;
typedef vector<vi> vvi;
typedef vector<ii> vii;
typedef vector<bool> vb;
typedef vector<vb> vvb;

const ll INF = 4 * 1e18;

//  ----------------    FILES       ----------------    //

//#define FILEINOUT
#ifdef FILEINOUT
ifstream In("Input.txt");
ofstream Out("Output.txt");
#else
#define In cin
#define Out cout
#endif

vii movesDeltas = {
        {-1, -2},
        {-1, 2},
        {-2, -1},
        {-2, 1},
        {1, -2},
        {1, 2},
        {2, -1},
        {2, 1},
};

ll n, m;
vvb field;
ii start;
ii finish;
vector<vector<pair<ll, ii>>> ans;
vvb was;

ll solve() {
    queue<ii> q;
    q.push(start);

    while (!q.empty()) {
        ii t = q.front();
        q.pop();
        for (ii delt : movesDeltas) {
            ii next = {t.first + delt.first, t.second + delt.second };
            if (min(next.first, next.second) < 0 || next.first >= n || next.second >= m ||
                field[next.first][next.second]) {
                continue;
            }
            if (ans[next.first][next.second].first > ans[t.first][t.second].first + 1) {
                ans[next.first][next.second].first = ans[t.first][t.second].first + 1;
                ans[next.first][next.second].second = t;
            }
            if (!was[next.first][next.second]) {
                was[next.first][next.second] = true;
                q.push(next);
            }
        }
    }

    return ans[finish.first][finish.second].first == INF ? -1 : ans[finish.first][finish.second].first;
}

int main() {

    In >> n >> m;
    field = vvb(n, vb());
    was = vvb(n, vb(m, false));

    for (ll i = 0; i < n; i++) {
        ans.push_back({});
        for (ll j = 0; j < m; j++) {
            ans[i].push_back({INF, {-1, -1}});
        }
    }

    for (int i = 0; i < n; i++) {
        for (int j = 0; j < m; j++) {
            char c;
            In >> c;
            field[i].push_back(c == 'x');
        }
    }

    In >> start.first >> start.second;
    In >> finish.first >> finish.second;

    ans[start.first][start.second] = {0, {-1, -1}};

    ll result = solve();
    Out << result;

    if (result != -1) {
        vii path;
        path.push_back(finish);
        while (finish != start) {
            finish = ans[finish.first][finish.second].second;
            path.push_back(finish);
        }
        reverse(path.begin(), path.end());
        for (int i = 0; i < path.size(); i++) {
            Out << endl << path[i].first << ' ' << path[i].second;
        }
    }


    return 0;
}
