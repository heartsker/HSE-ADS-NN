//
// Created by Daniel Pustotin on 27.09.2021.
//

#include <iostream>
#include <vector>
#include <fstream>
#include <tuple>
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

#define FILEINOUT
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

typedef tuple<bool, ll, ll> ans;

ll n, m;
vvb field;
ii finish;

ans dfs(ll moves, ll bombs, ii knight, vvb was) {
    if (bombs < 0) {
        return {false, -1, -1};
    }

    if (knight == finish) {
        return {true, moves, bombs};
    }

    was[knight.first][knight.second] = true;

    ans best = {false, INF, 0};

    for (auto delta: movesDeltas) {
        ii next = {knight.first + delta.first, knight.second + delta.second};
        if (min(next.first, next.second) < 0 || next.first >= n || next.second >= m || was[next.first][next.second]) {
            continue;
        }

        ans nextAns = dfs(moves + 1, bombs - field[next.first][next.second], next, was);
        if (get<0>(nextAns)) {
            if (get<1>(nextAns) < get<1>(best) || get<1>(nextAns) == get<1>(best) && get<2>(nextAns) > get<2>(best)) {
                best = nextAns;
            }
        }
    }

    return best;
}

int main() {

    ll bombs;
    In >> n >> m >> bombs;
    field = vvb(n, vb());
    ii knight;

    for (int i = 0; i < n; i++) {
        for (int j = 0; j < m; j++) {
            char c;
            In >> c;
            if (c == 'k') knight = {i, j};
            if (c == 'e') finish = {i, j};
            field[i].push_back(c == '1');
        }
    }

    vvb was(n, vb(m, false));

    ans answer = dfs(0, bombs, knight, was);

    if (get<0>(answer)) {
        Out << "Moves: " << get<1>(answer) << endl;
        Out << "Bombs left: " << get<2>(answer) << endl;
    } else {
        Out << "No way to reach exit!" << endl;
    }
    return 0;
}
