#include<map>
#include<queue>
#include<vector>
#include<cstdio>
#include<climits>
#include<cassert>
#include<cstring>
#include<string>
#include<iostream>
#include<algorithm>

using namespace std;

const char* TMPFILENAME = "extract.tmp";

FILE* preprocessing() {
	FILE *out = fopen(TMPFILENAME, "w");
	char buf[505];
	while (fgets(buf, sizeof(buf), stdin) != NULL) {
		if (buf[0] != '#') {
			fprintf(out, "%s", buf);
		}
	}
	fclose(out);
	return fopen(TMPFILENAME, "r");
}

typedef int EClassId;

struct ENode {
	string head;
	EClassId eclass;
	vector<EClassId> ch;
	//int cost;
};

struct EClass {
	vector<ENode> enodes;
	bool isEffectful;
};

struct EGraph {
	vector<EClass> eclasses;
};

EGraph read_egraph(FILE* ppin) {
	EGraph g;
	int n;
	fscanf(ppin, "%d", &n);
	g.eclasses.resize(n);
	for (int i = 0; i < n; ++i) {
		int f, m;
		EClass &c = g.eclasses[i];
		fscanf(ppin, "%d%d", &f, &m);
		c.isEffectful = f != 0;	
		c.enodes.resize(m);
		for (int j = 0; j < m; ++j) {
			ENode &n = c.enodes[j];
			char buf[55];
			//handle names with spaces
			fgets(buf, sizeof(buf), ppin);
			fgets(buf, sizeof(buf), ppin);
			assert(strlen(buf) > 1);
			buf[strlen(buf) - 1] = '\0';
			n.head = buf;
			n.eclass = i;
			int l;
			fscanf(ppin, "%d", &l);
			n.ch.resize(l);
			for (int k = 0; k < l; ++k) {
				fscanf(ppin, "%d", &n.ch[k]);
			}
			//scanf("%d", &n.cost);
		}
	}
	return g;
}

void print_egraph(const EGraph &g) {
	int n = g.eclasses.size();
	printf("%d\n", n);
	for (int i = 0; i < n; ++i) {
		const EClass &c = g.eclasses[i];
		int f = c.isEffectful ? 1 : 0,
			m = c.enodes.size();
		printf("%d %d\n", f, m);
		for (int j = 0; j < m; ++j) {
			const ENode &n = c.enodes[j];
			int l = n.ch.size();
			printf("%s\n%d%c", n.head.c_str(), l, l == 0 ? '\n' : ' ');
			for (int k = 0; k < l; ++k) {
				printf("%d%c", n.ch[k], k == l - 1 ? '\n' : ' ');
			}
			//printf("%d\n", n.cost);
		}
	}
}

typedef int ENodeId;

typedef int ExtractionENodeId;

struct ExtractionENode {
	EClassId c;
	ENodeId n;
	vector<ExtractionENodeId> ch;
};

typedef vector<ExtractionENode> Extraction;

bool validExtraction(const EGraph &g, const EClassId root, const Extraction &e) {
	if (e.size() == 0 || e.back().c != root) { // root
		return false;
	}
	for (int i = (int)e.size() - 1; i >= 0; --i) {
		const ExtractionENode &n = e[i];
		if (n.c < 0 || n.c >= g.eclasses.size()) {
			return false;
		}
		if (n.n < 0 || n.n >= g.eclasses[n.c].enodes.size()) {
			return false;
		}
		if (n.ch.size() != g.eclasses[n.c].enodes[n.n].ch.size()) {
			return false;
		}
		for (int j = 0; j < (int)n.ch.size(); ++j) {
			ExtractionENodeId ch = n.ch[j];
			if (ch < 0 || ch >= e.size()) { // child present
				return false;
			}
			if (e[ch].c != g.eclasses[n.c].enodes[n.n].ch[j]) {
				return false;
			}
			if (ch >= i) { // acyclicity
				return false;
			}
		}
	}
	// reachability does not really matter
	// unique choice not required 
	return true;
}

void print_extraction(const EGraph &g, const Extraction &e) {
	for (int i = 0; i < (int)e.size(); ++i) {
		printf("#%d %d%c %d %s%c", i, e[i].c, g.eclasses[e[i].c].isEffectful ? '!' : ' ', e[i].n, g.eclasses[e[i].c].enodes[e[i].n].head.c_str(), e[i].ch.size() == 0 ? '\n' : ' ');
		for (int j = 0; j < (int)e[i].ch.size(); ++j) {
			printf("#%d%c", e[i].ch[j], j == e[i].ch.size() - 1 ? '\n' : ' ');
		}
	}
}

typedef int Cost;

pair<bool, Extraction> NormalGreedyExtraction(const EGraph &g, EClassId root) {
	vector<Cost> dis(g.eclasses.size(), INT_MAX);
	vector<ENodeId> pick(g.eclasses.size(), -1);
	priority_queue<pair<Cost, EClassId>> maxheap;
	for (int i = 0; i < (int)g.eclasses.size(); ++i) {
		for (int j = 0; j < (int)g.eclasses[i].enodes.size(); ++j) {
			if (g.eclasses[i].enodes[j].ch.size() == 0) {
				dis[i] = 1;
				pick[i] = j;
				maxheap.push(make_pair(-dis[i], i));
				break;
			}
		}
	}

	// crazy optimization, don't bother
	vector<vector<pair<EClassId, ENodeId>>> rev_ind(g.eclasses.size());
	vector<vector<pair<int, Cost>>> counters(g.eclasses.size());
	for (EClassId i = 0; i < (int)g.eclasses.size(); ++i) {
		counters[i].resize(g.eclasses[i].enodes.size());
		for (ENodeId j = 0; j < (int)g.eclasses[i].enodes.size(); ++j) {
			counters[i][j] = make_pair(g.eclasses[i].enodes[j].ch.size(), 1);
			for (int k = 0; k < (int)g.eclasses[i].enodes[j].ch.size(); ++k) {
				rev_ind[g.eclasses[i].enodes[j].ch[k]].push_back(make_pair(i, j));
			}
		}
	}

	while (maxheap.size() > 0) {
		Cost d = -maxheap.top().first;
		EClassId i = maxheap.top().second;
		maxheap.pop();
		if (d == dis[i]) {
			for (int j = 0; j < (int)rev_ind[i].size(); ++j) {
				EClassId vc = rev_ind[i][j].first;
				ENodeId vn = rev_ind[i][j].second;
				--counters[vc][vn].first;
				counters[vc][vn].second += dis[i];
				if (counters[vc][vn].first == 0 && counters[vc][vn].second < dis[vc]) {
					dis[vc] = counters[vc][vn].second;
					pick[vc] = vn;
					maxheap.push(make_pair(-dis[vc], vc));
				}
			}
		}
	}

	if (dis[root] == INT_MAX) {
		return make_pair(false, Extraction());
	}

	vector<bool> inExtraction(g.eclasses.size(), false);
	queue<EClassId> q;
	inExtraction[root] = true;
	q.push(root);
	vector<pair<Cost, EClassId>> ord;
	while (q.size() > 0) {
		EClassId c = q.front();
		ord.push_back(make_pair(dis[c], c));
		q.pop();
		for (int i = 0; i < (int)g.eclasses[c].enodes[pick[c]].ch.size(); ++i) {
			EClassId chc = g.eclasses[c].enodes[pick[c]].ch[i];
			if (!inExtraction[chc]) {
				inExtraction[chc] = true;
				q.push(chc);
			}
		}
	}
	sort(ord.begin(), ord.end());

	Extraction e;
	vector<ExtractionENodeId> idmap(g.eclasses.size(), -1);
	for (int i = 0; i < (int)ord.size(); ++i) {
		ExtractionENode n;
		n.c = ord[i].second;
		n.n = pick[n.c];
		for (int j = 0; j < (int)g.eclasses[n.c].enodes[n.n].ch.size(); ++j) {
			n.ch.push_back(idmap[g.eclasses[n.c].enodes[n.n].ch[j]]);
		}
		e.push_back(n);
		idmap[n.c] = i;
	}
	assert(validExtraction(g, root, e));
	return make_pair(true, e);
}

struct SubEGraphMap {
	vector<EClassId> eclassmp;
	map<EClassId, EClassId> inv;
	vector<vector<int>> nsubregion;
};

pair<EGraph, SubEGraphMap> createRegionEGraph(const EGraph &g, const EClassId region_root) {
	SubEGraphMap mp;
	queue<EClassId> q;
	q.push(region_root);
	mp.inv[region_root] = 0;
	mp.eclassmp.push_back(region_root);
	mp.nsubregion.push_back(vector<int>(g.eclasses[region_root].enodes.size(), 0));
	while (q.size() > 0) {
		EClassId u = q.front();
		q.pop();
		assert(mp.nsubregion[mp.inv[u]].size() == g.eclasses[u].enodes.size());
		for (int i = 0; i < (int)g.eclasses[u].enodes.size(); ++i) {
			bool subregionchild = false;
			for (int j = 0; j < (int)g.eclasses[u].enodes[i].ch.size(); ++j) {
				EClassId v = g.eclasses[u].enodes[i].ch[j];
				if (g.eclasses[v].isEffectful) {
					if (subregionchild) {
						mp.nsubregion[mp.inv[u]][i]++;
						continue;
					}
					subregionchild = true;
				}
				if (!mp.inv.count(v)) {
					mp.inv[v] = mp.eclassmp.size();
					mp.eclassmp.push_back(v);
					mp.nsubregion.push_back(vector<int>(g.eclasses[v].enodes.size(), 0));
					q.push(v);
				}
			}
		}
	}
	EGraph gr;
	for (int i = 0; i < (int)mp.eclassmp.size(); ++i) {
		EClass c;
		c.isEffectful = g.eclasses[mp.eclassmp[i]].isEffectful;
		c.enodes.resize(g.eclasses[mp.eclassmp[i]].enodes.size());
		for (int j = 0; j < (int)g.eclasses[mp.eclassmp[i]].enodes.size(); ++j) {
			bool subregionchild = false;
			c.enodes[j].eclass = i;
			c.enodes[j].head = g.eclasses[mp.eclassmp[i]].enodes[j].head;
			for (int k = 0; k < (int)g.eclasses[mp.eclassmp[i]].enodes[j].ch.size(); ++k) {
				EClassId cp = g.eclasses[mp.eclassmp[i]].enodes[j].ch[k];
				if (g.eclasses[cp].isEffectful) {
					if (subregionchild) {
						continue;
					}
					subregionchild = true;
				}
				c.enodes[j].ch.push_back(mp.inv[cp]);
			}
		}
		gr.eclasses.push_back(c);
	}
	return make_pair(gr, mp);
}

bool checkLinearRegionRec(const EGraph &g, const EClassId root, const Extraction &e) {
	// cout << "Checking region linearity: " << root << endl;
	// Find statewalk and subregions
	vector<ExtractionENodeId> statewalk;
	vector<ExtractionENodeId> subregions;
	vector<bool> vis(e.size(), false);
	vector<bool> onpath(e.size(), false);
	queue<ExtractionENodeId> q;
	statewalk.push_back(root);
	onpath[root] = true;
	for (int i = 0; i < (int)statewalk.size(); ++i) {
		int u = statewalk[i];
		int nxt = -1;
		for (int j = 0; j < (int)e[u].ch.size(); ++j) {
			if (g.eclasses[e[e[u].ch[j]].c].isEffectful) {
				if (nxt == -1) {
					nxt = e[u].ch[j];
					statewalk.push_back(nxt);
					onpath[nxt] = true;
				} else {
					subregions.push_back(e[u].ch[j]);
				}
			} else {
				if (!vis[e[u].ch[j]]) {
					vis[e[u].ch[j]] = true;
					q.push(e[u].ch[j]);
				}
			}
		}
	}
	// Check pure enodes only depend on the effectful walk in this region
	while (q.size()) {
		int u = q.front();
		q.pop();
		for (int i = 0; i < (int)e[u].ch.size(); ++i) {
			int v = e[u].ch[i];
			// assuming pure enodes can only have one effectful child
			if (g.eclasses[e[v].c].isEffectful) {
				if (!onpath[v]) {
					// using a effectul enode not in this region
					return false;
				}
			} else {
				if (!vis[v]) {
					vis[v] = true;
					q.push(v);
				}
			}
		}
	}
	// Check all the subregions
	for (int i = 0; i < (int)subregions.size(); ++i) {
		if (!checkLinearRegionRec(g, subregions[i], e)) {
			return false;
		}
	}
	return true;
}

bool linearExtraction(const EGraph &g, const EClassId root, const Extraction &e) {
	if (!validExtraction(g, root, e)) {
		return false;
	}
	assert(g.eclasses[root].isEffectful);
	return checkLinearRegionRec(g, root, e);
}


typedef vector<pair<EClassId, ENodeId>> StateWalk;

/*
StateWalk getStateWalk(const EGraph &g, const EClassId root, const Extraction &e) {
	assert(validExtraction(g, root, e));
	assert(g.eclasses[root].isEffectful);
	StateWalk sw;
	int cur = e.size() - 1;
	while (cur != -1) {
		sw.push_back(make_pair(e[cur].c, e[cur].n));
		int nxt = -1;
		for (int i = 0; i < (int)e[cur].ch.size(); ++i) {
			if (g.eclasses[e[e[cur].ch[i]].c].isEffectful) {
				nxt = e[cur].ch[i];
				break;
			}
		}
		cur = nxt;
	}
	return sw;
}
*/

pair<bool, Extraction> regionExtractionWithStateWalk(const EGraph &g, const EClassId root, const StateWalk &sw) {
	EGraph gp = g;
	// 1. remove all enodes in effectful eclasses
	for (int i = 0; i < (int)gp.eclasses.size(); ++i) {
		if (gp.eclasses[i].isEffectful) {
			gp.eclasses[i].enodes.clear();
		}
	}
	// 2. add back all the enodes in the statewalk as individual eclasses
	EClassId last = -1;
	vector<int> ecmap(g.eclasses.size() + sw.size());
	for (int i = sw.size() - 1; i >= 0; --i) {
		EClassId cg = sw[i].first, cgp;
		ENodeId ng = sw[i].second;
		if (gp.eclasses[cg].enodes.size() == 0) {
			gp.eclasses[cg].enodes.push_back(g.eclasses[cg].enodes[ng]);
			cgp = cg;
		} else {
			cgp = gp.eclasses.size();
			EClass ec;
			ec.isEffectful = true;
			ec.enodes.push_back(g.eclasses[cg].enodes[ng]);
			gp.eclasses.push_back(ec);
		}
		bool subregionchild = false;
		for (int j = 0; j < (int)gp.eclasses[cgp].enodes[0].ch.size(); ++j) {
			EClassId chc = gp.eclasses[cgp].enodes[0].ch[j];
			if (g.eclasses[chc].isEffectful) {
				assert(!subregionchild); // at most one effectful child in a region egraph
				gp.eclasses[cgp].enodes[0].ch[j] = last;
				subregionchild = true;
			}
		}
		ecmap[cgp] = i;
		last = cgp;
	}
	// 3. is automatically handled by keeping the edges of the pure enodes
	// printf("Reconstructed egraph gprime:\n");
	// print_egraph(gp);
	pair<bool, Extraction> result = NormalGreedyExtraction(gp, root);
	if (result.first == false) {
		return result;
	} else {
		//Reconstruct the extraction in G
		Extraction &e = result.second;
		for (int i = 0; i < (int)e.size(); ++i) {
			if (gp.eclasses[e[i].c].isEffectful) {
				e[i].n = sw[ecmap[e[i].c]].second;
				e[i].c = sw[ecmap[e[i].c]].first;
			}
		}
		assert(validExtraction(g, root, e));
		assert(linearExtraction(g, root, e));
		return result;
	}
}

typedef vector<bool> ExtractableSet;

inline bool isExtractable(const EGraph &g, const ExtractableSet &es, const EClassId c, const ENodeId n) {
	for (int i = 0; i < (int)g.eclasses[c].enodes[n].ch.size(); ++i) {
		EClassId chc = g.eclasses[c].enodes[n].ch[i];
		if (!es[chc]) {
			return false;
		}
	}
	return true;
}

ExtractableSet saturate_pure(const EGraph &g, const ExtractableSet &es) {
	ExtractableSet ret(es.size(), false);
	queue<EClassId> q;
	vector<vector<pair<EClassId, ENodeId>>> edges(g.eclasses.size());
	vector<vector<int>> counters(g.eclasses.size());
	for (int i = 0; i < (int)g.eclasses.size(); ++i) {
		if (es[i]) {
			q.push(i);
			ret[i] = true;
		} else {
			if (!g.eclasses[i].isEffectful) {
				bool canextract = false;
				for (int j = 0; j < (int)g.eclasses[i].enodes.size(); ++j) {
					if (g.eclasses[i].enodes[j].ch.size() == 0) {
						canextract = true;
					}
				}
				if (canextract) {
					q.push(i);
					ret[i] = true;
				} else {
					counters[i].resize(g.eclasses[i].enodes.size());
					for (int j = 0; j < (int)g.eclasses[i].enodes.size(); ++j) {
						counters[i][j] = g.eclasses[i].enodes[j].ch.size();
						for (int k = 0; k < (int)g.eclasses[i].enodes[j].ch.size(); ++k) {
							edges[g.eclasses[i].enodes[j].ch[k]].push_back(make_pair(i, j));
						}
					}
				}
			}
		}
	}
	while (q.size() > 0) {
		int u = q.front();
		q.pop();
		for (int i = 0; i < (int)edges[u].size(); ++i) {
			EClassId vc = edges[u][i].first;
			ENodeId vn = edges[u][i].second;
			if (!ret[vc]) {
				--counters[vc][vn];
				if (counters[vc][vn] == 0) {
					q.push(vc);
					ret[vc] = true;
				}
			}
		}
	}
	return ret;
}

typedef pair<EClassId, ExtractableSet> ExVertex;
typedef int ExVertexId;

StateWalk UnguidedFindStateWalk(const EGraph &g, const EClassId initc, const ENodeId initn, const EClassId root, const vector<vector<int>> &nsubregion) {
	// print_egraph(g);
	// cout << initc << ' ' << initn << ' ' << root << endl;
	vector<vector<pair<EClassId, ENodeId>>> edges(g.eclasses.size());
	for (int i = 0; i < (int)g.eclasses.size(); ++i) {
		if (g.eclasses[i].isEffectful) {
			for (int j = 0; j < (int)g.eclasses[i].enodes.size(); ++j) {
				for (int k = 0; k < (int)g.eclasses[i].enodes[j].ch.size(); ++k) {
					if (g.eclasses[g.eclasses[i].enodes[j].ch[k]].isEffectful) {
						edges[g.eclasses[i].enodes[j].ch[k]].push_back(make_pair(i, j));
					}
				}
			}
		}
	}
	vector<ExVertex> vs;
	map<ExVertex, ExVertexId> vsmap;
	vector<pair<Cost, Cost> > dis;
	vector<pair<ENodeId, ExVertexId> > pa;

	ExtractableSet inites(g.eclasses.size(), false);
	inites[initc] = true;
	inites = saturate_pure(g, inites);
	ExVertex initv = make_pair(initc, inites);
	vsmap[initv] = vs.size();
	vs.push_back(initv);
	dis.push_back(make_pair(0, 1));
	pa.push_back(make_pair(initn, -1));

	priority_queue<pair<pair<Cost, Cost>, ExVertexId> > maxheap;
	maxheap.push(make_pair(make_pair(-dis[0].first, -dis[0].second), 0));

	ExVertexId goal = -1;
	while (maxheap.size() > 0) {
		pair<Cost, Cost> c = maxheap.top().first;
		c.first = -c.first;
		c.second = -c.second;
		ExVertexId i = maxheap.top().second;
		// cout << i << ' ' << c.first << ' ' << c.second << endl;
		maxheap.pop();
		if (dis[i] != c) {
			continue;
		}
		if (goal != -1 && dis[i] == dis[goal]) {
			break;
		}
		ExVertex u = vs[i];
		ExtractableSet &ues = u.second;
		for (int j = 0; j < (int)edges[u.first].size() && goal == -1; ++j) {
			EClassId vc = edges[u.first][j].first;
			ENodeId vn = edges[u.first][j].second;
			if (isExtractable(g, ues, vc, vn)) {
				ExtractableSet ves = ues;
				if (!ues[vc]) {
					ves[vc] = true;
					ves = saturate_pure(g, ves);
				}
				ExVertex v = make_pair(vc, ves);
				pair<Cost, Cost> nc = make_pair(c.first + nsubregion[vc][vn], c.second + 1);
				int vid;
				if (!vsmap.count(v)) {
					vid = vs.size();
					vsmap[v] = vid;
					vs.push_back(v);
					dis.push_back(nc);
					pa.push_back(make_pair(vn, i));
					maxheap.push(make_pair(make_pair(-dis[vid].first, -dis[vid].second), vid));
				} else {
					vid = vsmap[v];
					if (dis[vid] > nc) {
						dis[vid] = nc;
						pa[vid] = make_pair(vn, i);
						maxheap.push(make_pair(make_pair(-dis[vid].first, -dis[vid].second), vid));
					}
				}
				if (vc == root && (goal == -1 || dis[vid] < dis[goal])) {
					goal = vid;
				}
			}
		}
	}
	assert(goal != -1);
	ExVertexId cur = goal;
	StateWalk sw;
	while (cur != -1) {
		sw.push_back(make_pair(vs[cur].first, pa[cur].first));
		cur = pa[cur].second;
	}
	return sw;
}

typedef int Rank;

inline Rank Vrank(const ExtractableSet &es, const vector<EClassId> &V, const int js = 0) {
	for (int i = js; i < (int)V.size(); ++i) {
		if (!es[V[i]]) {
			return i;
		}
	}
	return V.size();
}

typedef pair<EClassId, Rank> Vertex;

//cheating global states for the pick variable heuristics
vector<EClassId> __gfullv;

pair<bool, StateWalk> FindStateWalk(const EGraph &g, const EClassId initc, const ENodeId initn, const EClassId root, const vector<EClassId> &V) {
	vector<vector<pair<EClassId, ENodeId>>> edges(g.eclasses.size());
	for (int i = 0; i < (int)g.eclasses.size(); ++i) {
		if (g.eclasses[i].isEffectful) {
			for (int j = 0; j < (int)g.eclasses[i].enodes.size(); ++j) {
				for (int k = 0; k < (int)g.eclasses[i].enodes[j].ch.size(); ++k) {
					if (g.eclasses[g.eclasses[i].enodes[j].ch[k]].isEffectful) {
						edges[g.eclasses[i].enodes[j].ch[k]].push_back(make_pair(i, j));
					}
				}
			}
		}
	}
	// using a map here for sparsity
	map<Vertex, pair<ExtractableSet, pair<ENodeId, Vertex>>> dis;
	queue<Vertex> q;
	ExtractableSet inites(g.eclasses.size(), false);
	inites[initc] = true;
	inites = saturate_pure(g, inites);
	Rank initrnk = Vrank(inites, V);
	Vertex initv = make_pair(initc, initrnk);
	Vertex goalv = make_pair(root, V.size());
	Vertex INVALID = make_pair(-1, -1);
	dis[initv] = make_pair(inites, make_pair(initn, INVALID));
	q.push(initv);
	while (q.size() > 0 && !dis.count(goalv)) {
		Vertex u = q.front();
		q.pop();
		ExtractableSet ues = dis[u].first;
		for (int i = 0; i < (int)edges[u.first].size(); ++i) {
			EClassId vc = edges[u.first][i].first;
			ENodeId vn = edges[u.first][i].second;
			if (isExtractable(g, ues, vc, vn)) {
				ExtractableSet ves = ues;
				Rank vrnk = u.second;
				if (!ues[vc]) {
					ves[vc] = true;
					ves = saturate_pure(g, ves);
					vrnk = Vrank(ves, V, u.second);
				}
				Vertex v = make_pair(vc, vrnk);
				if (!dis.count(v)) {
					dis[v] = make_pair(ves, make_pair(vn, u));
					q.push(v);
				}
			}
		}
	}
	if (dis.count(goalv) != 0) {
		Vertex cur = goalv;
		StateWalk sw;
		while (cur != INVALID) {
			sw.push_back(make_pair(cur.first, dis[cur].second.first));
			cur = dis[cur].second.second;
		}
		return make_pair(true, sw);
	} else {
		return make_pair(false, StateWalk());
	}
}

vector<EClassId> analyzeStateWalkOrdering(const EGraph &g, const StateWalk &sw) {
	vector<bool> containsGet(g.eclasses.size(), false), vis(g.eclasses.size(), false);
	vector<vector<pair<EClassId, ENodeId>>> edges(g.eclasses.size());
	vector<vector<int>> counters(g.eclasses.size());
	queue<EClassId> q;
	for (int i = 0; i < (int)g.eclasses.size(); ++i) {
		if (!g.eclasses[i].isEffectful) {
			counters[i].resize(g.eclasses[i].enodes.size());
			for (int j = 0; j < (int)g.eclasses[i].enodes.size(); ++j) {
				if (vis[i]) {
					break;
				}
				counters[i][j] = g.eclasses[i].enodes[j].ch.size();
				for (int k = 0; k < (int)g.eclasses[i].enodes[j].ch.size(); ++k) {
					edges[g.eclasses[i].enodes[j].ch[k]].push_back(make_pair(i, j));
					if (g.eclasses[g.eclasses[i].enodes[j].ch[k]].isEffectful) {
						containsGet[i] = true;
					}
				}
				if (counters[i][j] == 0 && !vis[i]) {
					q.push(i);
					vis[i] = true;
				}
			}
		}
	}
	while (q.size()) {
		EClassId u = q.front();
		q.pop();
		for (int i = 0; i < (int)edges[u].size(); ++i) {
			EClassId vc = edges[u][i].first;
			ENodeId vn = edges[u][i].second;
			--counters[vc][vn];
			if (counters[vc][vn] == 0 && !vis[vc]) {
				q.push(vc);
				vis[vc] = true;
			}
		}
	}
	vector<EClassId> ret;
	for (int i = (int)sw.size() - 1; i >= 0; --i) {
		if (!vis[sw[i].first]) {
			q.push(sw[i].first);
			vis[sw[i].first] = true;
			while (q.size()) {
				EClassId u = q.front();
				if (i < (int)sw.size() - 1  && containsGet[u]) {
					ret.push_back(u);	
				}
				q.pop();
				for (int i = 0; i < (int)edges[u].size(); ++i) {
					EClassId vc = edges[u][i].first;
					ENodeId vn = edges[u][i].second;
					--counters[vc][vn];
					if (counters[vc][vn] == 0 && !vis[vc]) {
						q.push(vc);
						vis[vc] = true;
					}
				}
			}
		}
	}
	return ret;
}

pair<EClassId, ENodeId> findArg(const EGraph &g) {
	for (int i = 0; i < (int)g.eclasses.size(); ++i) {
		if (g.eclasses[i].isEffectful) {
			for (int j = 0; j < (int)g.eclasses[i].enodes.size(); ++j) {
				if (g.eclasses[i].enodes[j].ch.size() == 0) {
					return make_pair(i, j);
				}
			}
		}
	}
	assert(false);
}

EClassId pick_next_variable_heuristics(const vector<EClassId> &v) {
	// This is currently the stupiest thing
	while (true) {
		int i = rand() % (int)__gfullv.size();
		if (find(v.begin(), v.end(), __gfullv[i]) == v.end()) {
			return __gfullv[i];
		}
	}
}

typedef int RegionId;

ExtractionENodeId reconstructExtraction(const EGraph &g, const vector<EClassId> &region_roots, const vector<RegionId> &region_root_id, vector<ExtractionENodeId> &extracted_roots, Extraction &e, const RegionId &cur_region) {
	if (extracted_roots[cur_region] != -1) {
		return extracted_roots[cur_region];
	}
	EClassId region_root = region_roots[cur_region];
	// cout << "Region root : " << region_root << endl;
	pair<EGraph, SubEGraphMap> res = createRegionEGraph(g, region_root);
	EGraph &gr = res.first;
	SubEGraphMap &rmap = res.second;
	pair<EClassId, ENodeId> arg = findArg(gr);
	EClassId argc = arg.first;
	ENodeId argn = arg.second;
	EClassId root = rmap.inv[region_root];
	StateWalk sw = UnguidedFindStateWalk(gr, argc, argn, root, rmap.nsubregion);
	Extraction er = regionExtractionWithStateWalk(gr, root, sw).second;
	Extraction ner(er.size());
	for (int i = 0; i < (int)er.size(); ++i) {
		ExtractionENode &en = er[i], &nen = ner[i];
		EClassId oric = rmap.eclassmp[en.c];
		nen.c = oric;
		ENodeId orin = en.n;
		nen.n = orin;
		bool subregionchild = false;
		for (int j = 0, k = 0; j < (int)g.eclasses[oric].enodes[orin].ch.size(); ++j) {
			EClassId orichc = g.eclasses[oric].enodes[orin].ch[j];
			if (g.eclasses[orichc].isEffectful) {
				if (subregionchild) {
					nen.ch.push_back(reconstructExtraction(g, region_roots, region_root_id, extracted_roots, e, region_root_id[orichc]));
				} else {
					subregionchild = true;
					nen.ch.push_back(en.ch[k++]);
				}
			} else {
				nen.ch.push_back(en.ch[k++]);
			}
		}
	}
	int delta = e.size();
	for (int i = 0; i < (int)ner.size(); ++i) {
		bool subregionchild = false;
		for (int j = 0; j < (int)g.eclasses[ner[i].c].enodes[ner[i].n].ch.size(); ++j) {
			EClassId chc = g.eclasses[ner[i].c].enodes[ner[i].n].ch[j];
			if (g.eclasses[chc].isEffectful) {
				if (subregionchild) {
					continue;
				} else {
					subregionchild = true;
					ner[i].ch[j] += delta;
				}
			} else {
				ner[i].ch[j] += delta;
			}
		}
	}
	e.insert(e.end(), ner.begin(), ner.end());
	extracted_roots[cur_region] = e.size() - 1;
	return extracted_roots[cur_region];
}

int main() {
	FILE* ppin = preprocessing();
	EGraph g = read_egraph(ppin);
	EClassId program_root;
	fscanf(ppin, "%d", &program_root);
	print_egraph(g);
	vector<RegionId> region_root_id(g.eclasses.size(), -1);
	vector<EClassId> region_roots;
	region_roots.push_back(program_root);
	region_root_id[program_root] = 0;
	for (int i = 0; i < (int)g.eclasses.size(); ++i) {
		if (g.eclasses[i].isEffectful) {
			for (int j = 0; j < (int)g.eclasses[i].enodes.size(); ++j) {
				bool subregionroot = false;
				for (int k = 0; k < (int)g.eclasses[i].enodes[j].ch.size(); ++k) {
					EClassId v = g.eclasses[i].enodes[j].ch[k];
					if (g.eclasses[v].isEffectful) {
						if (subregionroot) {
							region_root_id[v] = region_roots.size();
							region_roots.push_back(v);
						} else {
							subregionroot = true;
						}
					}
				}
			}
		}
	}
	/*
	vector<pair<EGraph, SubEGraphMap>> region_egraphs;
	for (int i = 0; i < (int)region_roots.size(); ++i) {
		int u = region_roots[i];
		//cout << "Region root : " << u << endl;
		region_egraphs.push_back(createRegionEGraph(g, u));
		//print_egraph(region_egraphs.back().first);
	}
	vector<Extraction> region_extractions;
	for (int i = 0; i < (int)region_egraphs.size(); ++i) {
		cout << "Region root : " << region_roots[i] << endl;
		EGraph &gr = region_egraphs[i].first;
		pair<EClassId, ENodeId> arg = findArg(gr);
		EClassId argc = arg.first;
		ENodeId argn = arg.second;
		EClassId root = region_egraphs[i].second.inv[region_roots[i]];
		StateWalk sw = UnguidedFindStateWalk(gr, argc, argn, root);
		region_extractions.push_back(regionExtractionWithStateWalk(gr, root, sw).second);
		print_extraction(gr, region_extractions.back());
	}
	*/
	vector<ExtractionENodeId> extracted_roots(region_roots.size(), -1);
	Extraction e;
	reconstructExtraction(g, region_roots, region_root_id, extracted_roots, e, region_root_id[program_root]);
	print_extraction(g, e);
	assert(linearExtraction(g, program_root, e));
/*
	Extraction e1 = NormalGreedyExtraction(g, root).second;
	print_extraction(g, e1);
	if (!linearExtraction(g, root, e1)) {
		printf("This extraction is not linear!\n");
		printf("Try two-pass extraction!\n");
		StateWalk sp = getStateWalk(g, root, e1);
		pair<bool, Extraction> result = ExtractionWithStateWalk(g, root, sp);
		if (result.first) {
			printf("Two-pass extraction succeeded!\n");
			print_extraction(g, result.second);
		} else {
			printf("Two-pass extraction failed!\n");
			printf("Reading the state walk of the original program.\n");
			int l;
			fscanf(ppin, "%d", &l);
			StateWalk ori_sw(l);
			for (int i = 0; i < l; ++i) {
				fscanf(ppin, "%d%d", &ori_sw[i].first, &ori_sw[i].second);
			}
			pair<bool, Extraction> result = ExtractionWithStateWalk(g, root, ori_sw);
			if (result.first) {
				printf("Successfully extracted with the original program's state walk [as an optional test]!\n");
				Extraction e_ori = result.second;
				print_extraction(g, e_ori);
				printf("Analyzing the original program's state walk.\n");
				vector<EClassId> fullv = analyzeStateWalkOrdering(g, ori_sw);
				__gfullv = fullv;
				printf("Found the following variable ordering:\n");
				for (int i = 0; i < (int)fullv.size(); ++i) {
					printf("%d%c", fullv[i], i == (int)fullv.size() - 1 ? '\n' : ' ');
				}
				vector<int> fullvrnk(g.eclasses.size(), -1);
				for (int i = 0; i < (int)fullv.size(); ++i) {
					fullvrnk[fullv[i]] = i;
				}
				vector<EClassId> v;
				StateWalk sw;
				pair<EClassId, ENodeId> arg = findArg(g);
				EClassId argc = arg.first;
				ENodeId argn = arg.second;	
				assert(arg == ori_sw.back());
				if (FindStateWalk(g, argc, argn, root, fullv).first) {
					printf("Successfully found a state walk with the original program variable ordering [as an optional test]!\n");
				} else {
					printf("Failed to find a statewalk with the original program's variable ordering!\n");
					printf("Something is very wrong!\n");
					assert(false);
				}
				bool succ = false;
				while (!succ) {
					pair<bool, StateWalk> result = FindStateWalk(g, argc, argn, root, v);
					if (result.first) {
						printf("Found statewalk:\n");
						sw = result.second;
						for (int i = 0; i < (int)sw.size(); ++i) {
							printf("%d %d\n", sw[i].first, sw[i].second);
						}
						break;
					} else {
						printf("Failed to find statewalk with the given eclass set (Size = %zu)!\n", v.size());
						v.push_back(pick_next_variable_heuristics(v));
						vector<int> vrnks;
						for (int i = 0; i < (int)v.size(); ++i) {
							vrnks.push_back(fullvrnk[v[i]]);
						}
						sort(vrnks.begin(), vrnks.end());
						v.clear();
						for (int i = 0; i < (int)vrnks.size(); ++i) {
							if (vrnks[i] != -1) {
								v.push_back(fullv[vrnks[i]]);
							}
						}
						printf("New eclass set v: ");
						for (int i = 0; i < (int)v.size(); ++i) {
							printf("%d%c", v[i], i == (int)v.size() - 1 ? '\n' : ' ');
						}
					}
				}
				pair<bool, Extraction> result = ExtractionWithStateWalk(g, root, sw);
				if (result.first) {
					print_extraction(g, result.second);
				} else {
					printf("Failed to extract along the statewalk!\n");
					assert(false);
				}

			} else {
				printf("Failed to extract with the original program's state walk!\n");
				printf("Something is very wrong!\n");
				assert(false);
			}
		}
	}
*/
	return 0;
}
