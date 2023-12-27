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

#define USE_HEURISTIC false

// TODO
//  write split exists checker
//  if we find proposition for which split always exists, this is really useful

// TODO
//  ускорить через факт что pi задается как множество ребер, которое покрывает все циклы
//  за 2^m (быстрее на практике)


ll tot;
int mx, cnt;

void run() {
    if (0) {
        // TODO: еще есть куда копать, формально тебе надо чтобы для любого плохого V в (backawrd_G, G)
        // TODO: было плохое подмножество V чисто внутри G[А] или G[B] (с оговоркой)
#define prop propositions::get_cover_discrete_Mplus_Mminus
        auto covers = prop(g, g, nullopt);
        propositions::get_minimal_sets(covers);
        for (int A = 1; A < (1 << n) - 1; A++) {
            Matrix backward_G = g;
            int bad_B = 0;
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    if ((A & (1 << i)) && (~A & (1 << j))) {
                        backward_G[i][j] = 0;
                        if (g[j][i]) {
                            bad_B |= (1 << j);
                        }
                    }
            covers = prop(backward_G, g, nullopt);
            propositions::get_minimal_sets(covers);
            set<int> bad_A_sets, bad_B_sets;
            vector<int> bad_B_supersets(1 << n);
            vector<int> bad_A_supersets(1 << n);
            {
                // only edges in A
                Matrix backward_G{};
                for (int i = 0; i < n; i++)
                    for (int j = 0; j < n; j++)
                        if ((A & (1 << i)) && (A & (1 << j)))
                            backward_G[i][j] = g[i][j];
                auto tmp = prop(backward_G, backward_G, nullopt);
                bad_A_sets = {all(tmp)};
                for (int i : bad_A_sets)
                    bad_A_supersets[i] = 1;
                for (int i = 0; i < (1 << n); i++)
                    for (int j = 0; j < n; j++)
                        if (((1 << j) & i) == 0 && bad_A_supersets[i])
                            bad_A_supersets[i ^ (1 << j)] = 1;

            }
            if (1) {
                // only edges in B
                Matrix backward_G{};
                for (int i = 0; i < n; i++)
                    for (int j = 0; j < n; j++)
                        if ((~A & (1 << i)) && (~A & (1 << j)))
                            backward_G[i][j] = g[i][j];
                auto tmp = prop(backward_G, backward_G, nullopt);
                bad_B_sets = {all(tmp)};
                for (int i : bad_B_sets)
                    bad_B_supersets[i] = 1;
                for (int i = 0; i < (1 << n); i++)
                    for (int j = 0; j < n; j++)
                        if (((1 << j) & i) == 0 && bad_B_supersets[i])
                            bad_B_supersets[i ^ (1 << j)] = 1;
            }
            set<int> has_matching_to_A;
            if (1) {
                // remove edges in B
                Matrix backward_G = g;
                for (int i = 0; i < n; i++)
                    for (int j = 0; j < n; j++)
                        if ((~A & (1 << i)) && (~A & (1 << j)))
                            backward_G[i][j] = 0;
                auto tmp = propositions::get_matching_sets_Mplus(backward_G, nullopt);
                has_matching_to_A = {all(tmp)};
            }
            bool has_bad_set = 0;
            for (int m : covers) {
                bool bad_A_subset = 0;
                if (bad_A_supersets[m & A])
                    bad_A_subset = 1;
                if (0) {
                    int X = (m & A);
                    int i = X;
                    while (i) {
                        if (bad_A_sets.count(i)) {
                            bad_A_subset = 1;
                            break;
                        }
                        i = (i - 1) & X;
                    }
                }
                bool bad_B_subset = 0;
                if (1) {
                    bad_B_subset = 1;
                    int X = (m & ~A);
                    int i = X;
                    bool once = 0;
                    while (1) {
                        if (has_matching_to_A.count(i ^ (m & A))) {
                            once = 1;
                            if (!bad_B_supersets[X ^ i]) {
                                bad_B_subset = 0;
                                break;
                            }
                        }
                        if (i == 0)
                            break;
                        i = (i - 1) & X;
                    }
                    assert(once);
                }
                if (bad_A_subset || bad_B_subset);
                else {
                    has_bad_set = 1;
                    break;
                }
            }
            if (!has_bad_set) {
//                if (rnd() % 1000 == 0)
//                    cerr << A << '\n';
                return;
            }
        }
        helpers::print();
        cerr << "min V\n";
        for (int i : covers)
            cerr << bitset<n>(i) << '\n';
        assert(0);
    }
    if (0) {
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

#define validator_func(a, b) propositions::is_discrete_Mpluspi_Nminus(a, b) && \
                             propositions::is_discrete_test_Nminus(a, b)
    if (USE_HEURISTIC) {
#define balance_func(a, b) propositions::get_discrete_Mpluspi_Mminus(a, b) + \
                           propositions::get_discrete_test_Mminus(a, b)
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
//        if (propositions::is_discrete_Mpluspi_Mminus(propositions::get_backward_graph(pi, g), g) &&
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

#define MAX_EDGE 10000

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

const clock_t delay = CLOCKS_PER_SEC * 60 * 60 * 4;
//const clock_t delay = CLOCKS_PER_SEC * 10;

void print_time() {
    auto now = chrono::system_clock::to_time_t(chrono::system_clock::now());
    cerr << ctime(&now) << '\n';
}

void solve_proposition() {
    auto START_TIME = clock();
    auto last_update = clock();
    TS = 1;
    int next_ts = 10;
    int REAL_TS = 0;
    while (1) {
        if (TS == next_ts || (clock() - last_update) >= delay) {
            cerr << TS << ' ' << REAL_TS << ' ' << (clock() - START_TIME) / (ld)CLOCKS_PER_SEC / 60 << '\n';
            print_time();
//            cerr << tot / (ld)cnt << '\n';
            next_ts = next_ts * 2;
            last_update = clock();
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

