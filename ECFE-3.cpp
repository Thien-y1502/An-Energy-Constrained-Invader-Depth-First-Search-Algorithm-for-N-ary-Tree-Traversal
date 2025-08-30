#include <iostream>
#include <vector>
#include <stack>
#include <unordered_map>
#include <unordered_set>
#include <stdexcept>
#include <sstream>
#include <tuple>
#include <algorithm>
#include <functional>
#include <time.h>

using namespace std;

int numTrees;
double B;
vector<tuple<int, int, double>> edgesList;

struct Node {
	int id;
	vector<pair<Node*, double>> children;
	Node* parent = nullptr;
	bool visited = false;
	Node(int _id) : id(_id) {}
};

class Tree {
private:
	Node* root;
	double B;
	unordered_map<int, Node*> nodes;
	unordered_map<int, double> distanceFromRoot;

	Node* getOrCreate(int id) {
		if (!nodes.count(id)) {
			nodes[id] = new Node(id);
		}
		return nodes[id];
	}

	void assignDistanceFromRoot(Node* node, double currentLength, unordered_set<int>& visitedSet) {
		if (visitedSet.count(node->id)) return;
		visitedSet.insert(node->id);
		distanceFromRoot[node->id] = currentLength;
		for (auto& childPair : node->children) {
			Node* child = childPair.first;
			double w = childPair.second;
			assignDistanceFromRoot(child, currentLength + w, visitedSet);
		}
	}

	vector<int> findRoots(const vector<tuple<int, int, double>>& edgeList) {
		unordered_set<int> allNodes, childNodes;
		for (const auto& edge : edgeList) {
			int from = get<0>(edge);
			int to = get<1>(edge);
			allNodes.insert(from);
			allNodes.insert(to);
			childNodes.insert(to);
		}
		vector<int> roots;
		for (int id : allNodes) {
			if (!childNodes.count(id)) {
				roots.push_back(id);
			}
		}
		return roots;
	}

public:
	Tree(const vector<tuple<int, int, double>>& edgeList, double _B) : B(_B) {
		for (const auto& edge : edgeList) {
			int from = get<0>(edge);
			int to = get<1>(edge);
			double w = get<2>(edge);
			Node* parent = getOrCreate(from);
			Node* child = getOrCreate(to);
			parent->children.emplace_back(child, w);
			child->parent = parent;
		}

		vector<int> roots = findRoots(edgeList);
		root = getOrCreate(0);
		for (int realRoot : roots) {
			Node* ch = getOrCreate(realRoot);
			root->children.emplace_back(ch, 0.0);
			ch->parent = root;
		}

		unordered_set<int> visitedSet;
		assignDistanceFromRoot(root, 0.0, visitedSet);
	}

	void IDFS() {
		vector<pair<Node*, double>> path;
		vector<int> currentRoute;
		vector<vector<int>> routes;
		vector<double> routeCosts;

		double currentLength = 0.0;
		double routeEnergy = 0.0;
		double sumEnergy = 0.0;
		int routeCount = 1;

		vector<int> fullDFS;

		// Bắt đầu từ root
		path.push_back({ root, 0.0 });
		currentRoute.push_back(root->id);
		fullDFS.push_back(root->id);

		function<void(Node*, double&, double&)> exploreWithSurplus1 = [&](Node* currentNode, double& surplus, double& routeEnergy) {
			for (auto& childPair : currentNode->children) {
				Node* child = childPair.first;
				double weight = childPair.second;

				if (!child->visited && 2 * weight <= surplus ) {
					surplus -= 2 * weight;
					routeEnergy += 2 * weight;

					currentRoute.push_back(child->id);
					fullDFS.push_back(child->id);

					exploreWithSurplus1(child, surplus, routeEnergy);

					currentRoute.push_back(currentNode->id);
					fullDFS.push_back(currentNode->id);

					// Sau khi đã duyệt các con của child, nếu tất cả con của nó đã visited thì mới đánh dấu nó
					bool allChildrenVisited = true;
					for (auto& grandChild : child->children) {
						if (!grandChild.first->visited) {
							allChildrenVisited = false;
							break;
						}
					}
					if (allChildrenVisited) {
						child->visited = true;
					}
				}
			}
			};

		function<void(Node*)> DFS = [&](Node* u) {
			for (auto& childPair : u->children) {
				Node* v = childPair.first;
				double w = childPair.second;

				if (!v->visited) {
					// Nếu đi tiếp vượt quá B → kết thúc tuyến
					if (routeEnergy + w + (currentLength + w) > B) {
						double distToRoot = currentLength;
						routeEnergy += distToRoot;
						double surplus = B - routeEnergy;

						// Quay lại root
						for (int i = (int)path.size() - 2; i >= 0; i--) {
							if (path[i].first != root) exploreWithSurplus1(path[i].first, surplus, routeEnergy);
							currentRoute.push_back(path[i].first->id);
							fullDFS.push_back(path[i].first->id);
						}

						// Khám phá thêm bằng năng lượng dư
						exploreWithSurplus1(root, surplus, routeEnergy);

						// Lưu tuyến
						routes.push_back(currentRoute);
						routeCosts.push_back(routeEnergy);

						// Reset cho tuyến mới
						routeCount++;
						currentRoute.clear();
						currentRoute.push_back(root->id);
						routeEnergy = 0;
						double newDist = 0;

						// Quay lại đường từ root đến node u
						for (int i = 1; i < (int)path.size(); i++) {
							Node* parentNode = path[i - 1].first;
							Node* curNode = path[i].first;
							double wt = path[i].second;
							newDist += wt;
							routeEnergy += wt;
							sumEnergy += newDist;
							currentRoute.push_back(curNode->id);
						}
						currentLength = newDist;
					}

					// Duyệt tiếp
					v->visited = true;
					fullDFS.push_back(v->id);
					currentLength += w;
					routeEnergy += w;
					sumEnergy += currentLength;
					currentRoute.push_back(v->id);
					path.push_back({ v, w });

					DFS(v);

					// Backtrack
					fullDFS.push_back(u->id);
					path.pop_back();
					currentLength -= w;
					routeEnergy += w;
					currentRoute.push_back(u->id);
				}
			}
			};

		root->visited = true;
		DFS(root);

		// Tuyến cuối cùng nếu chưa đóng
		if (currentRoute.size() > 1) {
			double distToRoot = currentLength;
			routeEnergy += distToRoot;
			for (int i = (int)path.size() - 2; i >= 0; i--) {
				currentRoute.push_back(path[i].first->id);
				fullDFS.push_back(path[i].first->id);
			}

			double surplus = B - routeEnergy;
			exploreWithSurplus1(root, surplus, routeEnergy);

			routes.push_back(currentRoute);
			routeCosts.push_back(routeEnergy);
		}

		// In DFS đầy đủ
		cout << "Full DFS traversal: ";
		for (int id : fullDFS) cout << id << " ";
		cout << "\n\n";

		// In từng tuyến
		for (int i = 0; i < routes.size(); i++) {
			cout << "Route " << (i + 1) << " (cost = " << routeCosts[i] << "): ";
			for (int j = 0; j < routes[i].size(); j++) {
				cout << routes[i][j] << (j + 1 < routes[i].size() ? " " : "\n");
			}
		}
	}


	~Tree() {
		for (auto& pair : nodes) {
			delete pair.second;
		}
		nodes.clear();
	}
};

vector<tuple<int, int, double>> readEdgeList() {
	edgesList.clear();
	int totalNodes = 0;
	for (int t = 0; t < numTrees; t++) {
		int nodesInTree;
		cin >> nodesInTree;
		if (t == 0) totalNodes = nodesInTree;
		else totalNodes += nodesInTree - 1;
		for (int i = 0; i < nodesInTree - 1; i++) {
			int from, to;
			double w;
			cin >> from >> to >> w;
			edgesList.emplace_back(from, to, w);
		}
	}
	return edgesList;
}

int main() {
	cin >> numTrees >> B;
	readEdgeList();
	Tree tree(edgesList, B);
	clock_t begin = clock();
	tree.IDFS();
	clock_t end = clock();
	cout << "Time run: " << (double)(end - begin) / CLOCKS_PER_SEC << " s" << endl;
	return 0;
}

/*
4 18
5
0 1 1
0 2 2
2 3 3
2 4 4
4
5 6 2
5 7 3
7 8 1
8
9 10 1
9 11 2
9 12 5
11 13 1
11 14 1
12 15 2
12 16 2
2
17 18 1

3 60
9
0 1 1
1 2 4
2 3 4
2 4 5
1 5 3
0 6 2
6 7 3
7 8 6
9
9 10 7
10 11 7
11 12 7
12 13 5
12 14 5
14 15 1
12 16 5
16 17 2
13
18 19 1
18 20 1
18 21 7
18 22 2
19 23 1
19 24 4
20 25 5
20 26 5
21 27 3
21 28 7
22 29 1
22 30 1


Route 1 (cost = 60): -1 0 1 2 3 2 4 2 1 5 1 0 6 7 8 7 6 0 -1 9 -1 18 19 23 19 18 -1
Route 2 (cost = 60): -1 9 10 11 12 13 12 11 10 9 -1 18 19 18 20 18 22 18 -1
Route 3 (cost = 58): -1 9 10 11 12 14 15 14 12 11 10 9 -1 18 19 18 20 18 -1
Route 4 (cost = 60): -1 9 10 11 12 16 17 16 12 11 10 9 -1 18 19 20 18 18 -1
Route 5 (cost = 60): -1 18 19 24 19 18 20 25 20 26 20 18 21 27 21 22 29 22 30 22 18 18 -1
Route 6 (cost = 28): -1 18 21 28 21 18 -1

5 20
5
0 1 8
0 2 3
2 3 2
2 4 2
7
5 6 6
5 7 7
6 8 1
6 9 1
7 10 3
7 11 1
2
12 13 2
5
14 15 5
14 16 1
16 17 1
17 18 1
3
18 19 2
18 20 2

5 20
9
0 1 6
0 3 6
0 5 6
0 7 6
1 2 3
3 4 2
5 6 1
7 8 3
6 8 2
2 
9 10 1
2
11 12 2
2 
13 14 3
2 
15 16 1


0 1 6
0 3 6
0 5 6
0 7 6
1 2 3
3 4 2
5 6 1
7 8 3
9 10 1
11 12 2
13 14 3
15 16 1
*/