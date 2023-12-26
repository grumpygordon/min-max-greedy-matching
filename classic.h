#pragma once

#include "print.hpp"
#include <bits/stdc++.h>
#define all(x) (x).begin(), (x).end()
#define fr first
#define sc second
#define m_p make_pair
#define low_bo(a, x) ((int)(lower_bound(a.begin(), a.end(), x) - a.begin()))
#define up_bo(a, x) ((int)(upper_bound(a.begin(), a.end(), x) - a.begin()))
#define unique(a) a.resize(unique(a.begin(), a.end()) - a.begin())
#define popcnt(x) __builtin_popcount(x)
#define shuffle(a) shuffle(a.begin(), a.end(), rnd)

using namespace std;

template<typename T>             vector<T>& operator--            (vector<T> &v){for (auto& i : v) --i;            return  v;}
template<typename T>             vector<T>& operator++            (vector<T> &v){for (auto& i : v) ++i;            return  v;}
template<typename T, typename U> pair<T,U>& operator--           (pair<T, U> &p){--p.first; --p.second;            return  p;}
template<typename T, typename U> pair<T,U>& operator++           (pair<T, U> &p){++p.first; ++p.second;            return  p;}

using ll = long long;

mt19937 rnd(9111225);

template<typename T>
void setmin(T &x, T y) {
    x = min(x, y);
}

template<typename T>
void setmax(T &x, T y) {
    x = max(x, y);
}

#define TIME (clock() * 1.0 / CLOCKS_PER_SEC)

using ld = double;

using uint = unsigned int;
using ull = unsigned long long;

const int MAX_GRAPH_SIZE = 18, INF = (int)1e9 + 100;

const int n = 7;

using Matrix = array<array<int, MAX_GRAPH_SIZE>, MAX_GRAPH_SIZE>;
using EdgeList = vector<pair<int, int>>;

Matrix g;

#define EXTREME_ASSUMPTION false

int banned_node = 0;

template<typename T>
void fill(T &s, T v) {
    s = v;
}

template<typename U, typename T, size_t X>
void fill(array<U, X> &s, T v) {
    for (auto &i : s)
        fill(i, v);
}

//template<typename T, size_t X, size_t Y>
//void fill(array<array<T, X>, Y> &s, T v) {
//    for (auto &i : s)
//        fill(i, v);
//}


//
//template<typename T, typename U, enable_if_t<is_fundamental_v<T>, bool> = true>
//void fill(T &s, U value) {
//    s = value;
//}
//
//template<typename T, typename U, enable_if_t<!is_fundamental_v<T>, bool> = true>
//void fill(T &s, U value) {
//    for (auto &i : s)
//        fill(i, value);
//}
