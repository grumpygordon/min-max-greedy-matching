#pragma once

#include "classic.h"
#include "propositions.hpp"

namespace paths {

    Matrix graph, backward;

    EdgeList backward_list;

    bool finish;

    namespace cycle_finder {

        array<int, MAX_GRAPH_SIZE> vis;

        vector<int> cycle;

        bool dfs(int v) {
//            cerr << "enter " << v << '\n';
            if (vis[v] == 1) {
                cycle.push_back(v);
                return 1;
            }
            if (vis[v] == 2)
                return 0;
            vis[v] = 1;
            for (int u = 0; u < n; u++)
                if (u != v && graph[v][u] && !backward[v][u])
                    if (dfs(u)) {
                        cycle.push_back(v);
                        return 1;
                    }
            vis[v] = 2;
            return 0;
        }

        vector<int> get_cycle() {
//            cerr << "cycle search ";
            fill(vis, 0);
            cycle.clear();
            for (int i = 0; i < n; i++)
                if (!vis[i]) {
                    if (dfs(i))
                        break;
                }
            // cycle is c_1 c_n ... c_2 c_1 a_i .. a_2 a_1
            // convert it to c_1 .. c_n
            if (!cycle.empty()) {
                while (1) {
                    if (cycle.back() == cycle[0]) {
                        cycle.pop_back();
                        break;
                    }
                    cycle.pop_back();
                }
                reverse(all(cycle));
            }
//            cerr << "found ";
//            debug(cycle);
//            cerr << '\n';
            return cycle;
        }
    }

    namespace answer_storage {
        EdgeList minimum_list;
        set<EdgeList> cached;

        bool find_any;

        void initialize(bool find_any_) {
            find_any = find_any_;
            minimum_list.clear();
            cached.clear();
        }

        void update_answer(EdgeList candidate_list) {
            if(find_any) {
                finish = 1;
                return;
            }
            sort(all(candidate_list));

            if (cached.empty()) {
                cerr << "first answer candidate:\n";
                debug(candidate_list);
            }

            cached.insert(candidate_list);
            if (minimum_list.empty() || minimum_list.size() > candidate_list.size()) {
                cerr << "updated answer with size " << candidate_list.size() << '\n';
                minimum_list = candidate_list;
            }
        }

        // a \subset b
        bool is_subset(EdgeList const &a, EdgeList const &b) {
            set<pair<int, int>> g{all(b)};
            for (auto i : a) {
                if (!g.count(i)) {
                    return 0;
                }
            }
            return 1;
        }

        vector<EdgeList> get_all_list_set() {
            return {all(cached)};
        }

        vector<EdgeList> get_minimal_list_set() {
            set<EdgeList> minimal_set;
            for (auto list : cached) {
                vector<EdgeList> to_remove;
                bool bad = 0;
                for (auto s : minimal_set) {
                    if (is_subset(s, list)) {
                        bad = 1;
                        break;
                    }
                    if (is_subset(list, s)) {
                        to_remove.push_back(s);
                    }
                }
                // bad -> to_remove.empty()
                assert(to_remove.empty() || !bad);
                if (!bad) {
                    for (auto s : to_remove)
                        minimal_set.erase(s);
                    minimal_set.insert(list);
                }
            }
            return vector<EdgeList>{all(minimal_set)};
        }

        vector<EdgeList> get_minimum_list_set() {
            if (cached.empty())
                return {};
            int best = INF;
            for (auto const &list : cached)
                setmin(best, int(list.size()));
            vector<EdgeList> res;
            for (auto const &list : cached)
                if (list.size() == best)
                    res.push_back(list);
            return res;
        }

        vector<EdgeList> get_superset(EdgeList const &list) {
            vector<EdgeList> res;
            for (auto const &s : cached)
                if (is_subset(list, s))
                    res.push_back(s);
            return res;
        }
    }

    void recurse() {
//        cerr << "start recurse\n";
//        for (auto [v, u] : backward_list)
//            cerr << v + 1 << ' ' << u + 1 << '\n';
//        cerr << "list end\n\n";
        auto cycle = cycle_finder::get_cycle();
        if (cycle.empty()) {
            answer_storage::update_answer(backward_list);
            return;
        }
        for (int it = 0; it < cycle.size(); it++) {
            int v = cycle[it];
            int u = cycle[(it + 1) % cycle.size()];
            backward[v][u] = 1;
            if (propositions::is_discrete_Mpluspi_Mminuspi(backward, graph)) {
//            if (propositions::is_discrete_Mpluspi_Mminuspi(backward, graph) && propositions::is_discrete_test(backward, graph)) {
//            if (propositions::path_validator::is_valid(graph, backward_list, {v, u})) {
                backward_list.push_back({v, u});
                recurse();
                backward_list.pop_back();
                if (finish) {
                    backward[v][u] = 0;
                    return;
                }
            }
            backward[v][u] = 0;
        }
    }

    bool run(Matrix const &graph_, bool find_any) {
        finish = 0;
        graph = graph_;
        fill(backward, 0);
        backward_list.clear();
        propositions::path_validator::initialize();
        answer_storage::initialize(find_any);
        recurse();
        if (find_any)
            return finish;
        return !answer_storage::cached.empty();
    }

}

