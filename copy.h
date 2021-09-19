#pragma once
#include <vector>
#include <algorithm>
#include <cassert>

#define ll long long
#define MOD 1000000007

using namespace std;

ll PosMod(ll a) { return a >= 0 ? a : a + MOD; }
ll AddMod(ll a, ll b) { return PosMod((a + b) % MOD); }
ll MultMod(ll a, ll b) { return PosMod((a * b) % MOD); }

// a ^ n
ll powll(ll a, ll n) {
	ll r = 1;
	for (ll b = n; b > 0; b >>= 1, a = MultMod(a, a))
		if (b & 1) r = MultMod(r, a);
	return r;
}

ll InvMod(ll a) { return powll(a, MOD - 2); }
ll Frac(ll a, ll b) { return MultMod(a, InvMod(b)); }
ll gcd(ll a, ll b) { return b ? gcd(b, a % b) : a; }

// fenw tree
ll sum(vector<long long>& treeM, int i) {
	ll ans = 0;
	while (i > 0) {
		ans += treeM[i];
		i -= (i & -i);
	}
	return ans;
}

void update(vector<long long>& treeM, int i, int num) {
	while (i < treeM.size()) {
		treeM[i] += num;
		i += (i & -i);
	}
}

/* -- segment tree -- */
template <class T>
struct segtree {
	int _segR;
	vector<T> _segtree;
	function<T(T, T)> _combine;
	T _defaultValue;

	// initArr: 1 based array
public:
	segtree(vector<T>& initArr, function<T(T, T)> combine, T defaultValue) {
		assert(initArr.size() > 1 && initArr[0] == 0);
		_segR = initArr.size() - 1;
		_segtree = vector<T>(initArr.size() * 4);
		_combine = combine;
		_defaultValue = defaultValue;
		init(1, 1, _segR, initArr);
	}

	T query(int start, int end, int node = 1, int l = 0, int r = 0) {
		if (node == 1) {
			l = 1;
			r = _segR;
		}

		if (start <= l && r <= end)
			return _segtree[node];
		if (r < start || end < l)
			return _defaultValue;
		int m = (l + r) / 2;
		T lVal = query(start, end, 2 * node, l, m);
		T rVal = query(start, end, 2 * node + 1, m + 1, r);
		return _combine(lVal, rVal);
	}

	void update(int index, T delta, int node = 1, int l = 0, int r = 0) {
		if (node == 1) {
			l = 1;
			r = _segR;
		}

		if (l <= index && index <= r) {
			_segtree[node] = _combine(_segtree[node], delta);
		}
		if (index < l || r < index || l == r)
			return;
		int m = (l + r) / 2;
		update(index, delta, 2 * node, l, m);
		update(index, delta, 2 * node + 1, m + 1, r);
	}

private:
	T init(int node, int l, int r, vector<T>& initArr) {
		if (l == r) {
			return _segtree[node] = initArr[l];
		}
		int m = (l + r) / 2;
		T lVal = init(2 * node, l, m, initArr);
		T rVal = init(2 * node + 1, m + 1, r, initArr);
		return _segtree[node] = _combine(lVal, rVal);
	}
};


/* -- segment tree w. lazy propagation -- */
template <class T>
struct lazysegtree {
	int _segR;
	vector<T> _segtree;
	vector<T> _lazy;
	function<T(T, T)> _combine;
	// delta 가 int 번 적용된 값 계산
	function<T(T, int)> _deltaMult;
	T _defaultValue;

public:
	// initArr: 1 based array
	lazysegtree(vector<T>& initArr, function<T(T, T)> combine, function<T(T, int)> lazyDelta, T defaultValue) {
		assert(initArr.size() > 1 && initArr[0] == 0);
		_segR = initArr.size() - 1;
		_combine = combine;
		_deltaMult = lazyDelta;
		_defaultValue = defaultValue;
		_segtree = vector<T>(initArr.size() * 4);
		_lazy = vector<T>(initArr.size() * 4, defaultValue);
		init(1, 1, _segR, initArr);
	}

	T query(int start, int end, int node = 1, int l = 0, int r = 0) {
		if (node == 1) {
			l = 1;
			r = _segR;
		}
		int m = (l + r) / 2;
		if (_lazy[node] != _defaultValue) {
			if (l != r) {
				updateRange(l, m, _lazy[node], node * 2, l, m);
				updateRange(m + 1, r, _lazy[node], node * 2 + 1, m + 1, r);
			}
			_segtree[node] = _combine(_segtree[node], _deltaMult(_lazy[node], r - l + 1));
			_lazy[node] = _defaultValue;
		}

		if (start <= l && r <= end)
			return _segtree[node];
		if (r < start || end < l)
			return _defaultValue;
		T lVal = query(start, end, 2 * node, l, m);
		T rVal = query(start, end, 2 * node + 1, m + 1, r);
		return _combine(lVal, rVal);
	}

	void updateRange(int s, int e, T delta, int node = 1, int l = 0, int r = 0) {
		if (node == 1) {
			l = 1;
			r = _segR;
		}

		if (s <= l && r <= e) {
			_lazy[node] = _combine(_lazy[node], delta);
			return;
		}
		if (e < l || r < s)
			return;

		int len = min(r, e) - max(l, s) + 1;
		_segtree[node] = _combine(_segtree[node], _deltaMult(delta, len));

		int m = (l + r) / 2;
		updateRange(s, e, delta, 2 * node, l, m);
		updateRange(s, e, delta, 2 * node + 1, m + 1, r);
	}

private:
	T init(int node, int l, int r, vector<T>& initArr) {
		if (l == r) {
			return _segtree[node] = initArr[l];
		}
		int m = (l + r) / 2;
		T lVal = init(2 * node, l, m, initArr);
		T rVal = init(2 * node + 1, m + 1, r, initArr);
		return _segtree[node] = _combine(lVal, rVal);
	}
};

// tree that supports LCA
struct tree {
	vector<vector<int>> _adj;
	vector<vector<int>> _pa;
	vector<int> _depth;
	int _n;
	bool _canLCA = false;

public:
	tree(int n) {
		_n = n;
		_adj = vector<vector<int>>(n + 1);
	}

	void connect(int a, int b) {
		_adj[a].push_back(b);
		_adj[b].push_back(a);
	}

	void init_lca(int root) {
		_canLCA = true;
		_depth = vector<int>(_n + 1);

		int lg = 0;
		while ((1 << lg) <= _n) lg++;
		_pa = vector<vector<int>>(_n + 1, vector<int>(lg + 1));

		dfs_lca(root, 0, 0);
		for (int i = 1; i <= lg; i++) {
			for (int node = 1; node <= _n; node++) {
				_pa[node][i] = _pa[_pa[node][i - 1]][i - 1];
			}
		}
	}

	int LCA(int a, int b) {
		assert(_canLCA);
		if (_depth[a] > _depth[b]) swap(a, b); // depth[b] > depth[a]

		for (int j = _pa[0].size() - 1; j >= 0; j--) {
			if (_depth[b] - _depth[a] >= (1 << j)) b = _pa[b][j];
		}

		if (a == b) return a;
		for (int j = _pa[0].size() - 1; j >= 0; j--) {
			if (_pa[a][j] != _pa[b][j]) {
				a = _pa[a][j];
				b = _pa[b][j];
			}
		}
		return _pa[a][0];
	}

private:
	void dfs_lca(int here, int pa, int depth) {
		_pa[here][0] = pa;
		_depth[here] = depth;

		for (int there : _adj[here]) {
			if (there == pa) continue;

			dfs_lca(there, here, depth + 1);
		}
	}
};


namespace atcoder {

	// Implement (union by size) + (path compression)
	// Reference:
	// Zvi Galil and Giuseppe F. Italiano,
	// Data structures and algorithms for disjoint set union problems
	struct dsu {
	public:
		dsu() : _n(0) {}
		explicit dsu(int n) : _n(n), parent_or_size(n, -1) {}

		int merge(int a, int b) {
			assert(0 <= a && a < _n);
			assert(0 <= b && b < _n);
			int x = leader(a), y = leader(b);
			if (x == y) return x;
			if (-parent_or_size[x] < -parent_or_size[y]) std::swap(x, y);
			parent_or_size[x] += parent_or_size[y];
			parent_or_size[y] = x;
			return x;
		}

		bool same(int a, int b) {
			assert(0 <= a && a < _n);
			assert(0 <= b && b < _n);
			return leader(a) == leader(b);
		}

		int leader(int a) {
			assert(0 <= a && a < _n);
			if (parent_or_size[a] < 0) return a;
			return parent_or_size[a] = leader(parent_or_size[a]);
		}

		int size(int a) {
			assert(0 <= a && a < _n);
			return -parent_or_size[leader(a)];
		}

		std::vector<std::vector<int>> groups() {
			std::vector<int> leader_buf(_n), group_size(_n);
			for (int i = 0; i < _n; i++) {
				leader_buf[i] = leader(i);
				group_size[leader_buf[i]]++;
			}
			std::vector<std::vector<int>> result(_n);
			for (int i = 0; i < _n; i++) {
				result[i].reserve(group_size[i]);
			}
			for (int i = 0; i < _n; i++) {
				result[leader_buf[i]].push_back(i);
			}
			result.erase(
				std::remove_if(result.begin(), result.end(),
					[&](const std::vector<int>& v) { return v.empty(); }),
				result.end());
			return result;
		}

	private:
		int _n;
		// root node: -1 * component size
		// otherwise: parent
		std::vector<int> parent_or_size;
	};

}