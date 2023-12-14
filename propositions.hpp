#pragma once

#include "classic.h"

namespace propositions {

#define PRINT_FUNCTION_NAME_MACRO static bool printed = 0; if (!printed) {cerr << "calling " << __FUNCTION__ << '\n'; printed = 1;}

    Matrix graph, backward_graph;

    array<int, MAX_GRAPH_SIZE> upward_mask, backward_mask;

    namespace khun {
        Matrix khun_graph;
        array<int, MAX_GRAPH_SIZE> mt;
        array<bool, MAX_GRAPH_SIZE> vis;

        bool dfs_mt(int v) {
            vis[v] = true;
            for (int u = n - 1; u >= 0; u--)
                if (khun_graph[v][u]) {
                    if (mt[u] == -1 || (!vis[mt[u]] && dfs_mt(mt[u]))) {
                        mt[u] = v;
                        mt[v] = u;
                        return 1;
                    }
                }
            return 0;
        }

        int get_matching_size(int mask) {
            auto can_augment = [&](int v) {
                if (!dfs_mt(v))
                    return false;
                fill(vis, false);
                return true;
            };
            int mat_size = 0;
            fill(vis, false);
            fill(mt, -1);
            for (int i = 0; i < n; i++)
                if ((1 << i) & mask)
                    if (can_augment(i)) {
                        mat_size++;
                    }
            return mat_size;
        }
    }

    void initialize() {
        fill(graph, 0);
        fill(backward_graph, 0);
        fill(khun::khun_graph, 0);
        fill(upward_mask, 0);
        fill(backward_mask, 0);
    }

    namespace bitonic_stuff {

        int bad_counter[(1 << MAX_GRAPH_SIZE) + 10];

        // failed attempt to speedup verifier:
        // for every prefix of pi
        // remove edges from prefix to suffix
        // V is good if |N^+(V)| < 2|V| or |N^-(V)| >= 2|V|
        // pi is good if for every V, for at least one prefix of pi, V is good
        // FAIL: n=6 TS small
        bool is_good_pi_to_prefixes_remove_cut(array<int, n> const &pi, Matrix G) {
            memset(bad_counter, 0, sizeof(int) * (1 << n));
            for (int len = 0; len < n; len++) {
                int prefix_mask = 0;
                for (int i = 0; i < len; i++)
                    prefix_mask |= (1 << pi[i]);
                for (int i = 0; i < n; i++) {
                    upward_mask[i] = 0;
                    for (int j = 0; j < n; j++)
                        if (G[i][j])
                            if (((1 << i) & prefix_mask) && ((1 << j) & prefix_mask) == 0);
                            else upward_mask[i] |= (1 << j);
                    backward_mask[i] = 0;
                    for (int j = 0; j < n; j++)
                        if (G[j][i])
                            backward_mask[i] |= (1 << j);
                }
                for (int mask = (1 << n) - 1; mask > 0; mask--) {
                    int msz = popcnt(mask);
                    if (popcnt(mask) * 2 > n)
                        continue;
                    int X = mask, Y = mask;
                    for (int i = 0; i < n; i++)
                        if ((1 << i) & mask) {
                            X |= upward_mask[i];
                            Y |= backward_mask[i];
                        }
                    if (popcnt(X) >= msz * 2 && popcnt(Y) < msz * 2) {
                        bad_counter[mask]++;
                    }
                    continue;

                }
            }
            for (int i = 0; i < (1 << n); i++)
                if (bad_counter[i] == n)
                    return 0;
            return 1;
        }

        // failed attempt to speedup verifier:
        // given some subset, called prefix
        // remove edges from prefix to suffix
        // V is good if |N^+(V)| < 2|V| or |N^-(V)| >= 2|V|
        // prefix is good if all V are good
        // NOTE: very weak, always breaks lol
        bool is_good_prefix_remove_cut(int prefix_mask, Matrix G) {
            for (int i = 0; i < n; i++) {
                upward_mask[i] = 0;
                for (int j = 0; j < n; j++)
                    if (G[i][j])
                        if (((1 << i) & prefix_mask) && ((1 << j) & prefix_mask) == 0);
                        else upward_mask[i] |= (1 << j);
                backward_mask[i] = 0;
                for (int j = 0; j < n; j++)
                    if (G[j][i])
                        backward_mask[i] |= (1 << j);
            }
            for (int mask = (1 << n) - 1; mask > 0; mask--) {
                int msz = popcnt(mask);
                if (popcnt(mask) * 2 > n)
                    continue;
                int X = mask, Y = mask;
                for (int i = 0; i < n; i++)
                    if ((1 << i) & mask) {
                        X |= upward_mask[i];
                        Y |= backward_mask[i];
                    }
                if (popcnt(X) >= msz * 2 && popcnt(Y) < msz * 2) {
                    return 0;
                }
                continue;
            }
            return 1;
        }

    }


    Matrix get_backward_graph(array<int, n> const &pi, Matrix G) {
        Matrix b{};
        fill(b, 0);
        for (int i = 0; i < n; i++)
            for (int j = 0; j < i; j++)
                if (G[pi[i]][pi[j]]) {
                    b[pi[i]][pi[j]] = 1;
                }
        return b;
    }

    void enumerate_graph(array<int, n> const &pi, Matrix G) {
        backward_graph = get_backward_graph(pi, G);
        graph = G;
    }

    void fill_graph(Matrix backward_G, Matrix G) {
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++) {
                if (backward_G[i][j])
                    assert(i != j && G[i][j]);
            }
        graph = G;
        backward_graph = backward_G;
    }

    void fill_backward_upward_masks(const bool backward_prefix_only, const bool upward_prefix_only) {
        for (int i = 0; i < n; i++) {
            upward_mask[i] = 0;
            backward_mask[i] = 0;
            for (int j = 0; j < n; j++) {
                if (upward_prefix_only) {
                    if (backward_graph[i][j])
                        upward_mask[i] |= (1 << j);
                } else {
                    if (graph[i][j])
                        upward_mask[i] |= (1 << j);
                }
                if (backward_prefix_only) {
                    if (graph[j][i] && !backward_graph[j][i])
                        backward_mask[i] |= (1 << j);
                } else {
                    if (graph[j][i])
                        backward_mask[i] |= (1 << j);
                }
            }
        }
    }

    void get_upward_backward_masks(int mask, int &upward, int &backward) {
        upward = mask;
        backward = mask;
        for (int i = 0; i < n; i++)
            if ((1 << i) & mask) {
                upward |= upward_mask[i];
                backward |= backward_mask[i];
            }
    }

    // V is good if min(|N^+_pi(V)|, 2|V|) <= |N^-(V)|
    // balance = sum_V max(0, min(|N^+_pi(V)|, 2|V|) - |N^-(V)|)
    int get_restricted2V_Npluspi_Nminus(array<int, n> const &pi, Matrix G) {
        PRINT_FUNCTION_NAME_MACRO
        initialize();
        enumerate_graph(pi, G);
        fill_backward_upward_masks(false, true);
        int balance = 0;
        for (int mask = (1 << n) - 1; mask > 0; mask--) {
            int msz = popcnt(mask);
            int upward, backward;
            get_upward_backward_masks(mask, upward, backward);
            balance += max(0, min(2 * msz, popcnt(upward)) - popcnt(backward));
        }
        return balance;
    }

    // V is good if min(|N^+_pi(V)|, 2|V|) <= |N^-(V)|
    // FAIL: n=8 TS=75943069 (45 mins)
    bool is_continious_restricted2V_Npluspi_Nminus(array<int, n> const &pi, Matrix G) {
        PRINT_FUNCTION_NAME_MACRO
        initialize();
        enumerate_graph(pi, G);
        fill_backward_upward_masks(false, true);
        for (int mask = (1 << n) - 1; mask > 0; mask--) {
            int msz = popcnt(mask);
            int upward, backward;
            get_upward_backward_masks(mask, upward, backward);
            if (min(2 * msz, popcnt(upward)) > popcnt(backward))
                return 0;
        }
        return 1;
    }



    // V is good if |N^+_pi(V)| < 2|V| or |N^-_pi(V)| >= 2|V|
    int get_discrete_2V_Npluspi_Nminuspi(Matrix backward_G, Matrix G) {
        PRINT_FUNCTION_NAME_MACRO
        initialize();
        fill_graph(backward_G, G);
        fill_backward_upward_masks(true, true);
        int balance = 0;
        for (int mask = (1 << n) - 1; mask > 0; mask--) {
            int msz = popcnt(mask);
            int upward, backward;
            get_upward_backward_masks(mask, upward, backward);
            if (popcnt(backward) < msz * 2)
                balance += max(0, popcnt(upward) - (msz * 2 - 1));
        }
        return balance;
    }

    // V is good if |N^+_pi(V)| < 2|V| or |N^-_pi(V)| >= 2|V|
    // didn't fail, tested on n=8 (not 100% certain), n=9 (uncertain), n=10 (very uncertain)
    // n=6 10kk
    // n=7 138kk
    // n=8 44k
    bool is_discrete_2V_Npluspi_Nminuspi(Matrix backward_G, Matrix G) {
        PRINT_FUNCTION_NAME_MACRO
        initialize();
        fill_graph(backward_G, G);
        fill_backward_upward_masks(true, true);
        for (int mask = (1 << n) - 1; mask > 0; mask--) {
            int msz = popcnt(mask);
            int upward, backward;
            get_upward_backward_masks(mask, upward, backward);
            if (popcnt(upward) >= 2 * msz && popcnt(backward) < 2 * msz)
                return 0;
        }
        return 1;
    }

    // V is good if |M^+_pi(V)| <= |N^-_pi(V)| - |V|
    int get_continious_Mpluspi_Nminuspi(Matrix backward_G, Matrix G) {
        PRINT_FUNCTION_NAME_MACRO
        initialize();
        fill_graph(backward_G, G);
        fill_backward_upward_masks(true, true);
        int balance = 0;
        for (int mask = (1 << n) - 1; mask > 0; mask--) {
            int msz = popcnt(mask);
            int upward, backward;
            get_upward_backward_masks(mask, upward, backward);

            // matching_size + |V| <= popcnt(upward) <= popcnt(backward)
            if (popcnt(upward) <= popcnt(backward))
                continue;

            fill(khun::khun_graph, 0);
            for (int i = 0; i < n; i++)
                if ((1 << i) & mask) {
                    for (int j = 0; j < n; j++)
                        if (((1 << j) & mask) == 0)
                            khun::khun_graph[i][j] = backward_graph[i][j];
                }

            int matching_size_outward = khun::get_matching_size(mask);
            balance += max(0, matching_size_outward - (popcnt(backward) - msz));
        }
        return balance;
    }

    // V is good if |M^+_pi(V)| <= |N^-_pi(V)| - |V|
    // works for n=8 and 164 millions samples
    // works for n=9 and 40 millions samples
    // fails even for N^-(V): when V = right part of cut and cut size C < V' and |M(V')| = |V'|
    bool is_continious_Mpluspi_Nminuspi(Matrix backward_G, Matrix G) {
        PRINT_FUNCTION_NAME_MACRO
        initialize();
        fill_graph(backward_G, G);
        fill_backward_upward_masks(true, true);
        for (int mask = (1 << n) - 1; mask > 0; mask--) {
            int msz = popcnt(mask);
            int upward, backward;
            get_upward_backward_masks(mask, upward, backward);

            // matching_size <= popcnt(upward) <= popcnt(backward)
            if (popcnt(upward) <= popcnt(backward))
                continue;

            fill(khun::khun_graph, 0);
            for (int i = 0; i < n; i++)
                if ((1 << i) & mask) {
                    for (int j = 0; j < n; j++)
                        if (((1 << j) & mask) == 0)
                            khun::khun_graph[i][j] = backward_graph[i][j];
                }

            int matching_size_outward = khun::get_matching_size(mask);

            if (matching_size_outward > popcnt(backward) - msz)
                return 0;
        }
        return 1;
    }

    // V is good if |M^+_pi(V)| <= |M^-_pi(V)|
    int get_continious_Mpluspi_Mminuspi(array<int, n> const &pi, Matrix G) {
        PRINT_FUNCTION_NAME_MACRO
        initialize();
        enumerate_graph(pi, G);
        fill_backward_upward_masks(true, true);
        int balance = 0;
        for (int mask = (1 << n) - 1; mask > 0; mask--) {
            int msz = popcnt(mask);
            int upward, backward;
            get_upward_backward_masks(mask, upward, backward);

            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    khun::khun_graph[i][j] = 0;
            for (int i = 0; i < n; i++)
                if ((1 << i) & mask) {
                    for (int j = 0; j < i; j++)
                        if (((1 << j) & mask) == 0 && graph[i][j])
                            khun::khun_graph[i][j] = 1;
                }

            int matching_size_outward = khun::get_matching_size(mask);

            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    khun::khun_graph[i][j] = 0;
            for (int i = 0; i < n; i++)
                if ((1 << i) & mask) {
                    for (int j = 0; j < i; j++)
                        if (((1 << j) & mask) == 0 && graph[j][i])
                            khun::khun_graph[i][j] = 1;
                }

            int matching_size_backward = khun::get_matching_size(mask);

            balance += max(0, matching_size_outward - matching_size_backward);
        }
        return balance;
    }


    // V is good if |M^+_pi(V)| <= |M^-_pi(V)|
    // fails for n=6, example in overleaf
    bool is_continious_Mpluspi_Mminuspi(array<int, n> const &pi, Matrix G) {
        PRINT_FUNCTION_NAME_MACRO
        initialize();
        enumerate_graph(pi, G);
        fill_backward_upward_masks(true, true);
        for (int mask = (1 << n) - 1; mask > 0; mask--) {
            int msz = popcnt(mask);
            int upward, backward;
            get_upward_backward_masks(mask, upward, backward);

            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    khun::khun_graph[i][j] = 0;
            for (int i = 0; i < n; i++)
                if ((1 << i) & mask) {
                    for (int j = 0; j < i; j++)
                        if (((1 << j) & mask) == 0 && graph[i][j])
                            khun::khun_graph[i][j] = 1;
                }

            int matching_size_outward = khun::get_matching_size(mask);

            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    khun::khun_graph[i][j] = 0;
            for (int i = 0; i < n; i++)
                if ((1 << i) & mask) {
                    for (int j = 0; j < i; j++)
                        if (((1 << j) & mask) == 0 && graph[j][i])
                            khun::khun_graph[i][j] = 1;
                }

            int matching_size_backward = khun::get_matching_size(mask);

            if (matching_size_outward > matching_size_backward)
                return 0;
        }
        return 1;
    }

    // V is good if |M^+_pi(V)| < |V| or |M^-_pi(V)| >= |V|
    int get_discrete_Mpluspi_Mminuspi(Matrix backward_G, Matrix G) {
        PRINT_FUNCTION_NAME_MACRO
        initialize();
        fill_graph(backward_G, G);
        fill_backward_upward_masks(true, true);
        int balance = 0;
        for (int mask = (1 << n) - 1; mask > 0; mask--) {
            int msz = popcnt(mask);
            if (msz * 2 > n)
                continue;
            int upward, backward;
            get_upward_backward_masks(mask, upward, backward);

            fill(khun::khun_graph, 0);
            for (int i = 0; i < n; i++)
                if ((1 << i) & mask) {
                    for (int j = 0; j < n; j++)
                        if (((1 << j) & mask) == 0)
                            khun::khun_graph[i][j] = backward_graph[i][j];
                }

            int matching_size_outward = khun::get_matching_size(mask);

            fill(khun::khun_graph, 0);
            for (int i = 0; i < n; i++)
                if ((1 << i) & mask) {
                    for (int j = 0; j < n; j++)
                        if (((1 << j) & mask) == 0)
                            khun::khun_graph[i][j] = (graph[j][i] && !backward_graph[j][i]);
                }

            int matching_size_backward = khun::get_matching_size(mask);

            if (matching_size_backward < msz)
                balance += max(0, matching_size_outward - (msz - 1));

        }
        return balance;
    }

    // V is good if |M^+_pi(V)| < |V| or |M^-_pi(V)| >= |V|
    // works for n=8 and 20 millions samples
    // fail for n=18 if copy graph of size n=6 three times on a cycle
    // graph n=6 found with is_discrete_test
    bool is_discrete_Mpluspi_Mminuspi(Matrix backward_G, Matrix G) {
        PRINT_FUNCTION_NAME_MACRO
        initialize();
        fill_graph(backward_G, G);
        fill_backward_upward_masks(true, true);
        for (int mask = (1 << n) - 1; mask > 0; mask--) {
            int msz = popcnt(mask);
            if (msz * 2 > n)
                continue;

            fill(khun::khun_graph, 0);
            for (int i = 0; i < n; i++)
                if ((1 << i) & mask) {
                    for (int j = 0; j < n; j++)
                        if (((1 << j) & mask) == 0)
                            khun::khun_graph[i][j] = backward_graph[i][j];
                }

            int matching_size_outward = khun::get_matching_size(mask);

            fill(khun::khun_graph, 0);
            for (int i = 0; i < n; i++)
                if ((1 << i) & mask) {
                    for (int j = 0; j < n; j++)
                        if (((1 << j) & mask) == 0)
                            khun::khun_graph[i][j] = (graph[j][i] && !backward_graph[j][i]);
                }

            int matching_size_backward = khun::get_matching_size(mask);

            if (matching_size_backward < msz && matching_size_outward >= msz)
                return 0;
        }
        return 1;
    }

    // V is good if |M^+_pi(V)| < |V| or |N^-_pi(V)| >= 2|V|
    bool is_discrete_Mpluspi_Nminuspi(Matrix backward_G, Matrix G) {
        PRINT_FUNCTION_NAME_MACRO
        initialize();
        fill_graph(backward_G, G);
        fill_backward_upward_masks(true, true);
        for (int mask = (1 << n) - 1; mask > 0; mask--) {
            int upward, backward;
            get_upward_backward_masks(mask, upward, backward);
            int msz = popcnt(mask);

            if (popcnt(upward) - msz < msz)
                continue;

            fill(khun::khun_graph, 0);
            for (int i = 0; i < n; i++)
                if ((1 << i) & mask) {
                    for (int j = 0; j < n; j++)
                        if (((1 << j) & mask) == 0)
                            khun::khun_graph[i][j] = backward_graph[i][j];
                }

            int matching_size_outward = khun::get_matching_size(mask);

            if (matching_size_outward < msz)
                continue;

            if (popcnt(backward) - msz < msz)
                return 0;
        }
        return 1;
    }

    void get_minimal_sets(vector<int> &q) {
        sort(all(q));
        vector<int> aps((1 << n));
        vector<int> g;
        for (int i : q)
            if (!aps[i]) {
                g.push_back(i);
                for (int j = i; j < (1 << n); j = (j + 1) | i) {
                    aps[j] = 1;
                }
            }
        swap(q, g);
    }

    vector<int> get_cover_discrete_Mplus_Nminus(Matrix backward_G, Matrix G, optional<vector<int>> candidate_sets) {
        PRINT_FUNCTION_NAME_MACRO
        initialize();
        graph = G;
        backward_graph = backward_G;
        fill_backward_upward_masks(false, true);
        vector<int> covers;
        if (!candidate_sets.has_value()) {
            vector<int> alls;
            for (int mask = (1 << n) - 1; mask > 0; mask--)
                if (popcnt(mask) * 2 <= n)
                    alls.push_back(mask);
            candidate_sets = alls;
        }
        for (int mask : candidate_sets.value()) {
            int msz = popcnt(mask);
            if (msz * 2 > n)
                continue;

            fill(khun::khun_graph, 0);
            for (int i = 0; i < n; i++)
                if ((1 << i) & mask) {
                    for (int j = 0; j < n; j++)
                        if (((1 << j) & mask) == 0)
                            khun::khun_graph[i][j] = backward_graph[i][j];
                }

            int matching_size_outward = khun::get_matching_size(mask);

            if (matching_size_outward < msz)
                continue;

            int upward, backward;
            get_upward_backward_masks(mask, upward, backward);

            if (popcnt(backward) < 2 * msz)
                covers.emplace_back(mask);
        }
        return covers;
//        get_minimal_sets(covers);
//        auto A = covers;
//        for (int &i : covers) {
//            int upward, backward;
//            get_upward_backward_masks(i, upward, backward);
//            i = (~i & backward);
//        }
//        return A;
    }

    vector<int> get_cover_discrete_Mplus_Mminus(Matrix G) {
        PRINT_FUNCTION_NAME_MACRO
        initialize();
        graph = G;
        vector<int> covers;
        for (int mask = (1 << n) - 1; mask > 0; mask--) {
            int msz = popcnt(mask);
            if (msz * 2 > n)
                continue;

            fill(khun::khun_graph, 0);
            for (int i = 0; i < n; i++)
                if ((1 << i) & mask) {
                    for (int j = 0; j < n; j++)
                        if (((1 << j) & mask) == 0)
                            khun::khun_graph[i][j] = graph[i][j];
                }

            int matching_size_outward = khun::get_matching_size(mask);

            fill(khun::khun_graph, 0);
            for (int i = 0; i < n; i++)
                if ((1 << i) & mask) {
                    for (int j = 0; j < n; j++)
                        if (((1 << j) & mask) == 0)
                            khun::khun_graph[i][j] = graph[j][i];
                }

            int matching_size_backward = khun::get_matching_size(mask);

            if (matching_size_backward < msz && matching_size_outward >= msz)
                covers.emplace_back(mask);
        }
        get_minimal_sets(covers);
        return covers;
    }

    bool is_discrete_Mpluspi_Mminus(Matrix backward_G, Matrix G) {
        PRINT_FUNCTION_NAME_MACRO
        initialize();
        fill_graph(backward_G, G);
        fill_backward_upward_masks(false, false);
        for (int mask = (1 << n) - 1; mask > 0; mask--) {
            int msz = popcnt(mask);
            if (msz * 2 > n)
                continue;

            fill(khun::khun_graph, 0);
            for (int i = 0; i < n; i++)
                if ((1 << i) & mask) {
                    for (int j = 0; j < n; j++)
                        if (((1 << j) & mask) == 0)
                            khun::khun_graph[i][j] = backward_graph[i][j];
                }

            int matching_size_outward = khun::get_matching_size(mask);

            fill(khun::khun_graph, 0);
            for (int i = 0; i < n; i++)
                if ((1 << i) & mask) {
                    for (int j = 0; j < n; j++)
                        if (((1 << j) & mask) == 0)
                            khun::khun_graph[i][j] = graph[j][i];
                }

            int matching_size_backward = khun::get_matching_size(mask);

            if (matching_size_backward < msz && matching_size_outward >= msz)
                return 0;
        }
        return 1;
    }

    // n=6 10kk
    // n=7 17369271
    // n=8 2725050
    bool is_discrete_test_Nminuspi(Matrix backward_G, Matrix G) {
        PRINT_FUNCTION_NAME_MACRO
        assert(banned_node != -1);
        initialize();
        fill_graph(backward_G, G);
        fill_backward_upward_masks(true, true);
        bool f1 = 0, f2 = 0;
        for (int mask = (1 << n) - 1; mask > 0; mask--) {
            if ((1 << banned_node) & mask)
                continue;
            int upward, backward;
            get_upward_backward_masks(mask, upward, backward);
            int msz = popcnt(mask);
            if (!f1) {
                if (popcnt(upward) - msz < msz)
                    continue;
                fill(khun::khun_graph, 0);
                for (int i = 0; i < n; i++)
                    if ((1 << i) & mask) {
                        for (int j = 0; j < n; j++)
                            if (((1 << j) & mask) == 0)
                                khun::khun_graph[i][j] = backward_graph[i][j];
                    }
                int matching_size_outward = khun::get_matching_size(mask);

                if (matching_size_outward < msz)
                    continue;

                if ((backward & (1 << banned_node)) && popcnt(backward) - msz == msz) {
                    f1 = 1;
                }
            }
            if (!f2) {
                if (popcnt(upward & ~(1 << banned_node)) - msz < msz)
                    continue;
                fill(khun::khun_graph, 0);
                for (int i = 0; i < n; i++)
                    if ((1 << i) & mask) {
                        for (int j = 0; j < n; j++)
                            if (((1 << j) & mask) == 0 && j != banned_node)
                                khun::khun_graph[i][j] = backward_graph[i][j];
                    }
                int matching_size_outward = khun::get_matching_size(mask);

                if (matching_size_outward < msz)
                    continue;

                get_upward_backward_masks(mask | (1 << banned_node), upward, backward);
                if (popcnt(backward) - msz - 1 <= msz) {
                    f2 = 1;
                }
            }
            if (f1 && f2)
                return 0;
        }
        return !(f1 && f2);
    }

    // fail n=6
    bool is_discrete_test_Mminuspi(Matrix backward_G, Matrix G) {
        PRINT_FUNCTION_NAME_MACRO
        assert(banned_node != -1);
        initialize();
        fill_graph(backward_G, G);
        fill_backward_upward_masks(true, true);
        bool f1 = 0, f2 = 0;
        for (int mask = (1 << n) - 1; mask > 0; mask--) {
            if ((1 << banned_node) & mask)
                continue;
            if (!f1) {
                int msz = popcnt(mask);
                fill(khun::khun_graph, 0);
                for (int i = 0; i < n; i++)
                    if ((1 << i) & mask) {
                        for (int j = 0; j < n; j++)
                            if (((1 << j) & mask) == 0)
                                khun::khun_graph[i][j] = backward_graph[i][j];
                    }
                int matching_size_outward = khun::get_matching_size(mask);

                if (matching_size_outward < msz)
                    continue;

                fill(khun::khun_graph, 0);
                for (int i = 0; i < n; i++)
                    if ((1 << i) & mask) {
                        for (int j = 0; j < n; j++)
                            if (((1 << j) & mask) == 0 && j != banned_node)
                                khun::khun_graph[i][j] = (graph[j][i] && !backward_graph[j][i]);
                    }

                int matching_size_backward = khun::get_matching_size(mask);
                if (matching_size_backward < msz) {
                    f1 = 1;
                }
            }
            if (!f2) {
                int msz = popcnt(mask);
                fill(khun::khun_graph, 0);
                for (int i = 0; i < n; i++)
                    if ((1 << i) & mask) {
                        for (int j = 0; j < n; j++)
                            if (((1 << j) & mask) == 0 && j != banned_node)
                                khun::khun_graph[i][j] = backward_graph[i][j];
                    }
                int matching_size_outward = khun::get_matching_size(mask);

                if (matching_size_outward < msz)
                    continue;

                fill(khun::khun_graph, 0);
                for (int i = 0; i < n; i++)
                    if (((1 << i) & mask) || i == banned_node) {
                        for (int j = 0; j < n; j++)
                            if (((1 << j) & mask) == 0 && j != banned_node)
                                khun::khun_graph[i][j] = (graph[j][i] && !backward_graph[j][i]);
                    }

                int matching_size_backward = khun::get_matching_size(mask | (1 << banned_node));
                if (matching_size_backward < msz + 1) {
                    f2 = 1;
                }
            }
            if (f1 && f2)
                return 0;
        }
        return !(f1 && f2);
    }

    // n=7 success 40kk
    // n=8 success 3k
    bool is_discrete_test_Mminus(Matrix backward_G, Matrix G) {
        PRINT_FUNCTION_NAME_MACRO
        assert(banned_node != -1);
        initialize();
        fill_graph(backward_G, G);
        fill_backward_upward_masks(true, true);
        bool f1 = 0, f2 = 0;
        for (int mask = (1 << n) - 1; mask > 0; mask--) {
            if ((1 << banned_node) & mask)
                continue;
            if (!f1) {
                int msz = popcnt(mask);
                fill(khun::khun_graph, 0);
                for (int i = 0; i < n; i++)
                    if ((1 << i) & mask) {
                        for (int j = 0; j < n; j++)
                            if (((1 << j) & mask) == 0)
                                khun::khun_graph[i][j] = backward_graph[i][j];
                    }
                int matching_size_outward = khun::get_matching_size(mask);

                if (matching_size_outward < msz)
                    continue;

                fill(khun::khun_graph, 0);
                for (int i = 0; i < n; i++)
                    if ((1 << i) & mask) {
                        for (int j = 0; j < n; j++)
                            if (((1 << j) & mask) == 0 && j != banned_node)
                                khun::khun_graph[i][j] = (graph[j][i]);
                    }

                int matching_size_backward = khun::get_matching_size(mask);
                if (matching_size_backward < msz) {
                    f1 = 1;
                }
            }
            if (!f2) {
                int msz = popcnt(mask);
                fill(khun::khun_graph, 0);
                for (int i = 0; i < n; i++)
                    if ((1 << i) & mask) {
                        for (int j = 0; j < n; j++)
                            if (((1 << j) & mask) == 0 && j != banned_node)
                                khun::khun_graph[i][j] = backward_graph[i][j];
                    }
                int matching_size_outward = khun::get_matching_size(mask);

                if (matching_size_outward < msz)
                    continue;

                fill(khun::khun_graph, 0);
                for (int i = 0; i < n; i++)
                    if (((1 << i) & mask) || i == banned_node) {
                        for (int j = 0; j < n; j++)
                            if (((1 << j) & mask) == 0 && j != banned_node)
                                khun::khun_graph[i][j] = (graph[j][i]);
                    }

                int matching_size_backward = khun::get_matching_size(mask | (1 << banned_node));
                if (matching_size_backward < msz + 1) {
                    f2 = 1;
                }
            }
            if (f1 && f2)
                return 0;
        }
        return !(f1 && f2);
    }


    // V is good if |M^+_pi(V)| <= |M^-(V)|
    int get_continious_Mpluspi_Mminus(Matrix backward_G, Matrix G) {
        PRINT_FUNCTION_NAME_MACRO
        initialize();
        fill_graph(backward_G, G);
        fill_backward_upward_masks(false, true);
        int balance = 0;
        for (int mask = (1 << n) - 1; mask > 0; mask--) {
            int msz = popcnt(mask);
            int upward, backward;
            get_upward_backward_masks(mask, upward, backward);

            fill(khun::khun_graph, 0);
            for (int i = 0; i < n; i++)
                if ((1 << i) & mask) {
                    for (int j = 0; j < n; j++)
                        if (((1 << j) & mask) == 0 && backward_graph[i][j])
                            khun::khun_graph[i][j] = 1;
                }

            int matching_size_outward = khun::get_matching_size(mask);

            fill(khun::khun_graph, 0);
            for (int i = 0; i < n; i++)
                if ((1 << i) & mask) {
                    for (int j = 0; j < n; j++)
                        if (((1 << j) & mask) == 0 && graph[j][i])
                            khun::khun_graph[i][j] = 1;
                }

            int matching_size_backward = khun::get_matching_size(mask);

            balance += max(0, matching_size_outward - matching_size_backward);
        }
        return balance;
    }


    // V is good if |M^+_pi(V)| <= |M^-(V)|
    // FAIL: n=6 TS=29741
    bool is_continious_Mpluspi_Mminus(Matrix backward_G, Matrix G) {
        PRINT_FUNCTION_NAME_MACRO
        initialize();
        fill_graph(backward_G, G);
        fill_backward_upward_masks(false, true);
        for (int mask = (1 << n) - 1; mask > 0; mask--) {
            int msz = popcnt(mask);
            int upward, backward;
            get_upward_backward_masks(mask, upward, backward);

            fill(khun::khun_graph, 0);
            for (int i = 0; i < n; i++)
                if ((1 << i) & mask) {
                    for (int j = 0; j < n; j++)
                        if (((1 << j) & mask) == 0 && backward_graph[i][j])
                            khun::khun_graph[i][j] = 1;
                }

            int matching_size_outward = khun::get_matching_size(mask);

            fill(khun::khun_graph, 0);
            for (int i = 0; i < n; i++)
                if ((1 << i) & mask) {
                    for (int j = 0; j < n; j++)
                        if (((1 << j) & mask) == 0 && graph[j][i])
                            khun::khun_graph[i][j] = 1;
                }

            int matching_size_backward = khun::get_matching_size(mask);

            if (matching_size_outward > matching_size_backward)
                return 0;
        }
        return 1;
    }

    namespace path_validator {

        array<int, MAX_GRAPH_SIZE> parent;

        array<bool, MAX_GRAPH_SIZE> is_end, is_begin, vis;

        bool dfs(int v) {
            if (is_end[v])
                return 1;
            if (v == banned_node)
                return 0;
            if (vis[v])
                return 0;
            vis[v] = 1;
            for (int u = 0; u < n; u++)
                if (graph[v][u] && is_end[u]) {
                    return 1;
                }
            for (int u = 0; u < n; u++)
                if (graph[v][u] && !is_begin[u]) {
                    int w = u;
                    if (parent[w] != -1) {
                        w = parent[w];
                    }
                    if (vis[w])
                        continue;
                    if (dfs(w)) {
                        parent[u] = v;
                        return 1;
                    }
                }
            if (parent[v] != -1) {
                if (dfs(parent[v])) {
                    parent[v] = -1;
                    return 1;
                }
            }
            return 0;
        }

        int get_max_flow(EdgeList const &edge_set, bool early_stopping) {
            fill(all(is_end), 0);
            fill(all(is_begin), 0);
            fill(all(parent), -1);
            for (auto [v, u] : edge_set) {
                is_end[v] = 1;
                is_begin[u] = 1;
            }
            int ans = 0;
            for (auto [v, u] : edge_set) {
                fill(all(vis), 0);
                if (dfs(u))
                    ans++;
                else if (early_stopping)
                    return 0;
            }
            return ans;
        }

        map<EdgeList, bool> cached;

        void initialize() {
            cached.clear();
        }

        bool is_disjoint_set(EdgeList const &edge_set) {
            fill(all(vis), 0);
            for (auto [v, u] : edge_set) {
                if (!EXTREME_ASSUMPTION) {
                    if (vis[v])
                        return 0;
                    vis[v] = 1;
                }
                if (vis[u])
                    return 0;
                vis[u] = 1;
            }
            return 1;
        }

        bool is_valid_set(EdgeList edge_set) {
            if (!is_disjoint_set(edge_set))
                return 1;
            sort(all(edge_set));
            if (cached.count(edge_set))
                return cached[edge_set];
            auto res = (get_max_flow(edge_set, true) == edge_set.size());
            cached[edge_set] = res;
            return res;
        }

        bool is_valid(Matrix const &G, EdgeList backward_list, pair<int, int> new_edge) {
            graph = G;
            for (int mask = 0; mask < (1 << backward_list.size()); mask++) {
                vector<pair<int, int>> cur{new_edge};
                for (int i = 0; i < backward_list.size(); i++)
                    if ((1 << i) & mask)
                        cur.push_back(backward_list[i]);
                if (!is_valid_set(cur)) {
                    return 0;
                }
            }
            return 1;
        }
    }
}

