#include "classic.h"
#include "propositions.hpp"
#include "generators.hpp"
#include "paths.hpp"

int TS;

namespace helpers {

    void print() {
        cerr << "TS " << TS << '\n';
        cerr << n << '\n';
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++)
                cerr << g[i][j] << ' ';
            cerr << '\n';
        }
        cerr << '\n';
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++)
                if (i != j && g[i][j])
                    cerr << i + 1 << ' ' << j + 1 << '\n';
        }
    }

    namespace scc_counting {

        bool vis[15];

        vector<int> ord;

        void dfs(int v) {
            vis[v] = 1;
            for (int i = 0; i < n; i++)
                if (g[v][i] && !vis[i])
                    dfs(i);
            ord.push_back(v);
        }

        int scc_size;

        void back_dfs(int v) {
            vis[v] = 1;
            scc_size++;
            for (int i = 0; i < n; i++)
                if (g[i][v] && !vis[i])
                    back_dfs(i);
        }

        int count_scc() {
            ord.clear();
            memset(vis, 0, sizeof(vis));
            for (int i = 0; i < n; i++)
                if (!vis[i])
                    dfs(i);
            reverse(all(ord));
            memset(vis, 0, sizeof(vis));
            int scc_count = 0;
            for (int v: ord)
                if (!vis[v]) {
                    scc_size = 0;
                    back_dfs(v);
                    if (scc_size > 0)
                        scc_count++;
                }
            return scc_count;
        }

    }
}

#define USE_HEURISTIC true

// TODO
//  write split exists checker
//  if we find proposition for which split always exists, this is really useful

// TODO
//  ускорить через факт что pi задается как множество ребер, которое покрывает все циклы
//  за 2^m (быстрее на практике)


ll tot;
int mx, cnt;

void run() {
    if (1) {
        auto covers = propositions::get_cover_discrete_Mplus_Nminus(g, g, nullopt);
        propositions::get_minimal_sets(covers);
        for (int A = 1; A < (1 << n) - 1; A++) {
            Matrix backward_G = g;
            int bad_B = 0;
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    if ((A & (1 << i)) && (A & (1 << j)) == 0) {
                        backward_G[i][j] = 0;
                        if (g[j][i]) {
                            bad_B |= (1 << j);
                        }
                    }
            vector<int> bad_covers;
            for (int m : covers) {
                bool inside_A = (m & A) == m;
                bool inside_B = (m & ~A) == m;
                bool f1 = (!inside_A && !inside_B);
                bool f2 = (inside_B && (m & bad_B));
                f2 = 0;
                if (f1 || f2)
                    bad_covers.push_back(m);
            }
            if (propositions::get_cover_discrete_Mplus_Nminus(backward_G, g, bad_covers).empty())
                return;
        }
        helpers::print();
        cerr << "min V\n";
        for (int i : covers)
            cerr << bitset<n>(i) << '\n';
        assert(0);
    }
    if (1) {
//        auto [covers, nc] = propositions::get_cover_discrete_Mplus_Nminus(g, g, {});
        auto covers = propositions::get_cover_discrete_Mplus_Nminus(g, g, {});
        vector<int> nc{};
        bool dn = 1;
        for (auto x : {covers, nc}) {
            int res = 0;
            for (int i : x)
                res |= i;
            if (res != (1 << n) - 1)
                dn = 0;
        }
        if (dn) {
            helpers::print();
            cerr << "min V\n";
            for (int i : covers)
                cerr << bitset<n>(i) << '\n';
            cerr << "N-(V)\n";
            for (int i : nc)
                cerr << bitset<n>(i) << '\n';
            assert(0);
        }
        return;
    }

#define validator_func propositions::is_discrete_2V_Npluspi_Nminuspi
    if (USE_HEURISTIC) {
#define balance_func propositions::get_discrete_2V_Npluspi_Nminuspi
        array<int, n> pi;
        iota(all(pi), 0);
        cnt++;
        for (int start_id = 0; start_id < 3000; start_id++) {
            shuffle(pi);
            auto cur = balance_func(propositions::get_backward_graph(pi, g), g);
            int bad_counter = 0;

            while (cur > 0) {
                int l = rnd() % n, r = rnd() % n;
                if (l > r)
                    swap(l, r);
                reverse(pi.begin() + l, pi.begin() + r + 1);
                auto new_cur = balance_func(propositions::get_backward_graph(pi, g), g);
                if (new_cur < cur) {
                    cur = new_cur;
                    bad_counter = 0;
                    continue;
                }
                bad_counter++;
                if (bad_counter == n * n)
                    break;
            }
            if (cur == 0) {
                tot += start_id + 1;
                if (mx < start_id + 1) {
                    mx = start_id + 1;
                    cerr << "mx " << mx << '\n';
                }
                assert(validator_func(propositions::get_backward_graph(pi, g), g));
                return;
            }
        }
        cerr << "FAIL HEURISTIC\n";
    }
    for (auto pi : generators::all_gen())
        if (validator_func(propositions::get_backward_graph(pi, g), g)) {
//        if (propositions::is_discrete_Mpluspi_Nminuspi(propositions::get_backward_graph(pi, g), g) &&
//            validator_func(propositions::get_backward_graph(pi, g), g)) {
//                    cerr << "good pi\n";
//                    for (int i : pi)
//                        cerr << i << ' ';
//                    cerr << '\n';
            if (USE_HEURISTIC) {
                cerr << "found valid pi after failing heuristic\n";
            }
            return;
        }
    helpers::print();
    assert(0);
}

#define MAX_EDGE 100000

#define USE_CIN 0
#define cin if(USE_CIN) cin

void read_list_graph(bool read_banned_node) {
    int read_n = n;
    cin >> read_n;
    assert(read_n == n);

    fill(g, 0);
    for (int i = 0; i < n; i++)
        g[i][i] = 1;

    int m;
    cin >> m;
    if (read_banned_node) {
        cin >> banned_node;
        assert(banned_node != 0 && -1 <= banned_node && banned_node <= n);
        if (banned_node > 0)
            banned_node--;
    }
    for (int i = 0; i < m; i++) {
        int v, u;
        cin >> v >> u;
        v--;
        u--;
        g[v][u] = 1;
    }
}

void triple_graph() {
    int n = n / 3;
    for (int t = 1; t < 3; t++)
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                g[i + t * n][j + t * n] = g[i][j];
    g[0][n] = g[n][2 * n] = g[2 * n][0] = 1;
}

void read_graph() {
    int read_n = n;
    cin >> read_n;
    assert(read_n == n);

    for (int i = 0; i < n; i++)
        g[i][i] = 1;

    int m = n * n - n;
    int kf = rnd() % ((m + 1) / 2);

    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++) {
            if (i != j)
                g[i][j] = ((rnd() % m) < kf);
            cin >> g[i][j];
        }
}

void solve_proposition() {

    auto START_TIME = clock();
    TS = 1;
    int next_ts = 10;
    int REAL_TS = 0;
    while (1) {
        if (TS == next_ts) {
            cerr << TS << ' ' << REAL_TS << ' ' << (clock() - START_TIME) / (ld)CLOCKS_PER_SEC / 60 << '\n';
//            cerr << tot / (ld)cnt << '\n';
            next_ts = next_ts * 2;
        }
        TS++;
//        int n = rnd() % 6 + 1;
        read_graph();
//        read_list_graph(false);

        if (helpers::scc_counting::count_scc() != 1)
            continue;
        int edge_count = 0;
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                if (i != j)
                    edge_count += g[i][j];
        if (edge_count >= MAX_EDGE)
            continue;
        REAL_TS++;

        banned_node = 0;
//        if (!paths::run(g, true)) {
//            helpers::print();
//            assert(0);
//        }
        run();

        if (USE_CIN)
            exit(0);
    }
}

void solve() {
    read_list_graph(false);
    paths::run(g, false);

    if (paths::answer_storage::minimum_list.empty()) {
        cout << "no backward set\n";
    } else {
        cerr << "all minimal backward sets\n";
        auto res = paths::answer_storage::get_minimum_list_set();
        ++res;
        for (auto s : res)
            debug(s);
    }
}

int main(int argc, char** argv) {
#ifdef ONPC
    freopen("../a.in", "r", stdin);
//    freopen("../a.out", "w", stdout);
#endif
    ios::sync_with_stdio(0);
    cin.tie(0);
    cout << fixed;
    cout.precision(20);
    cerr << "run starts\n";
    cerr << "n = " << n << '\n';
    cerr << "USE_CIN " << USE_CIN << '\n';
    cerr << "USE_HEURISTIC " << USE_HEURISTIC << '\n';
//    cerr << "VALIDATOR " << #validator_func << '\n';
//    cerr << "HEURISTIC " << ##balance_func << '\n';
    if (argc < 2) {
        cerr << "use default seed\n";
    } else {
        int seed = atoi(argv[1]);
        cerr << "use seed " << seed << '\n';
        rnd = mt19937(seed);
    }
//    solve();
    solve_proposition();
}

