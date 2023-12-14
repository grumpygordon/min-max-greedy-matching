#pragma once

#include "classic.h"

namespace generators {
    vector<vector<int>> split_gen() {
        assert(n % 2 == 0);
        vector<vector<int>> res;
        vector<int> p(n);
        iota(all(p), 0);
        do {
            iota(p.begin() + n / 2, p.end(), n / 2);
            do {
                res.emplace_back(p);
            } while (next_permutation(p.begin() + n / 2, p.end()));
        } while (next_permutation(p.begin(), p.begin() + n / 2));
        return res;
    }

    vector<vector<int>> rest;

    vector<vector<int>> smart_gen(int g[MAX_GRAPH_SIZE][MAX_GRAPH_SIZE]) {
        rest.clear();
        vector<vector<int>> res;
        vector<int> p(n);
        iota(all(p), 0);
        if (0) {
            vector<int> rem(n, 1), in(n);
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    in[j] += g[i][j];
            for (int it = 0; it < n; it++) {
                int min_deg = INF;
                int v = -1;
                for (int i = 0; i < n; i++)
                    if (rem[i] && in[i] < min_deg) {
                        min_deg = in[i];
                        v = i;
                    }
                assert(v != -1);
                p[it] = v;
                rem[v] = 0;
                for (int i = 0; i < n; i++)
                    in[i] -= g[v][i];
            }
            return {p};
        }
        int min_inv = INF;
        do {
            int inv = 0;
            for (int i = 0; i < n; i++)
                for (int j = i + 1; j < n; j++)
                    inv += g[p[j]][p[i]];// * (j - i);
            if (inv < min_inv) {
                for (auto i: res)
                    rest.emplace_back(i);
                res.clear();
                min_inv = inv;
//            res.emplace_back(p);
            }
//        if (inv == 2) {
//            cerr << "best perm\n";
//            for (int i : p)
//                cerr << i + 1 << ' ';
//            cerr << '\n';
//        }
            if (inv == min_inv)
                res.emplace_back(p);
            else
                rest.emplace_back(p);
        } while (next_permutation(all(p)));
//    cerr << "min inv " << min_inv << '\n';
        return res;
    }


    vector<array<int, n>> all_gen() {
        static vector<array<int, n>> cached_all_gen;
        if (!cached_all_gen.empty())
            return cached_all_gen;
        array<int, n> pi;
        iota(all(pi), 0);
        vector<array<int, n>> res;
        do {
            cached_all_gen.push_back(pi);
        } while (next_permutation(all(pi)));
        return cached_all_gen;
    }

}