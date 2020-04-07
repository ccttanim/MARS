#include <bits/stdtr1c++.h>
#include "headers/splaytree.h"
using namespace std;

#define ll long long
#define pb push_back
#define MAX 200000
#define pii pair<int,int>
#define vpi vector< pii >
#define vi vector<int>
#define vll vector<ll>
#define pii pair<int,int>
#define pll pair<ll,ll>
#define spll set<pll>
#define all(v) v.begin(),v.end()
#define pr 7
#define type 0
#define NUM_OF_HASH 1
#define THRESHOLD 400000
#define TIME_THRESHOLD 20

#ifdef TOP_K_ENABLE
int TOP_K[] = {1,2,4,8,16,32,64,128,256,512,1024};

int STOP = 0;
#endif

/// hash value calculation ///
ll Hash[NUM_OF_HASH][MAX];
ll power[NUM_OF_HASH][MAX];
ll MOD[] = {1000000007, 1000000009, 998244353, 1000000037,1000000021,1000000003,1000005133};
int len;
vector<int>str;

///Splay Tree///
//SplayTree spt;
unordered_map<ll,unordered_map<ll,int> >spt;

void pre()
{
    for(int i=0; i<NUM_OF_HASH; i++)
    {
        power[i][0] = 1;
        for(int j=1; j<=len; j++)
        {
            power[i][j] = (power[i][j-1]*pr)%MOD[i];
        }
    }
    return;
}

ll getHash(int i,int j,int k)
{
    Hash[i][0] = str[0]-type;
    for(int j=1; j<=len; j++)
    {
        Hash[i][j] = (Hash[i][j-1]*pr + str[j]-type)%MOD[i];
    }
    return (Hash[k][j]-(Hash[k][i-1]*power[k][j-i+1])+MOD[k]*MOD[k])%MOD[k];
}

double showTime(clock_t st) {
  clock_t en = clock();
  double elapsed_secs = double(en - st) / CLOCKS_PER_SEC;
  return elapsed_secs;
}


/// data graph ///
vi data_graph[MAX],dataTag[MAX];
int data_label[MAX];
ifstream dataGraph;

/// query graph ///
vi query_graph[MAX],queryTag[MAX];
int QUERY_NODE,QUERY_EDGE,noOfSoln;
int query_label[MAX];
ifstream queryGraph;
vi C[MAX];
vector< pii > ordered_node;

ofstream writeToFile;

void CLR(int qN)
{
    for(int i=0; i<=qN; i++) query_graph[i].clear();
    for(int i=0; i<=qN; i++) queryTag[i].clear();
    memset(query_label,0,sizeof query_label);
    for(int i=0; i<=qN; i++) C[i].clear();
    ordered_node.clear();
    str.clear();
    #ifdef TOP_K_ENABLE
    STOP = 0;
    #endif
}

void printGraph(int nn,int data,int query)
{
    if(data)
    {
        puts("Data graph...");
        for(int i=1; i<=nn; i++)
        {
            printf("%d : ",i);
            for(auto v : data_graph[i])
            {
                printf("%d ",v);
            }
            puts("");
        }
        puts("Data graph ( tags )...");
        for(int i=1; i<=nn; i++)
        {
            if((int)dataTag[i].size()==0)
                continue;
            printf("%d : %d\n",i,dataTag[i].size());
        }
    }
    else
    {
        puts("Query graph...");
        for(int i=1; i<=nn; i++)
        {
            printf("%d : ",i);
            for(auto v : query_graph[i])
            {
                printf("%d ",v);
            }
            puts("");
        }
        puts("Query graph ( tags )...");
        for(int i=1; i<=nn; i++)
        {
            if((int)queryTag[i].size()==0)
                continue;
            printf("%d : %d\n",i,queryTag[i].size());
        }
    }
}

void printVector(vi v)
{
    for(auto it : v)
    {
        cout << it << " ";
    }
    puts("");
}


void graph_input() // this function takes input of the main graph
{
    int u,v,node,edge;
    // cin >> node >> edge;
    dataGraph >> node >> edge;

    printf("Taking input : Data Graph...\n");

    for(int i=1; i<=node; i++)
    {
        dataGraph >> data_label[i];
        //cin >> data_label[i];
    }

    ///tag classifier (assuming no negative tag)
    for(int i=1; i<=node; i++)
    {
        dataTag[data_label[i]].pb(i);
    }

    for(int i=0; i<edge; i++)
    {
        // cin >> u >> v;
        dataGraph >> u >> v;
        data_graph[u].pb(v);
        data_graph[v].pb(u);
    }
    for(int i=1 ; i<=node; i++)
    {
        sort(all(data_graph[i]));
    }

    printf("Data Graph Input : Done...\n");
    //printGraph(node,1,0);
}

void query_input() // this function takes input of the query graph
{
    int u,v,node,edge;
    //cin >> node >> edge;
    queryGraph >> node >> edge;
    QUERY_NODE = node;
    QUERY_EDGE = edge;

    printf("Taking input : Query Graph...\n");

    for(int i=1; i<=node; i++)
    {
        queryGraph >> query_label[i];
        //cin >> data_label[i];
    }

    ///tag classifier (assuming no negative tag)
    for(int i=1; i<=node; i++)
    {
        queryTag[query_label[i]].pb(i);
    }

    for(int i=0; i<edge; i++)
    {
        queryGraph >> u >> v;
        //cin >> u >> v;
        query_graph[u].pb(v);
        query_graph[v].pb(u);
    }
    for(int i=1 ; i<=node; i++)
    {
        sort(all(query_graph[i]));
    }
    printf("Query Graph Input : Done...\n");
    //printGraph(node,0,1);
}

void printVecPair(vpi vc)
{
    for(auto x : vc)
    {
        printf("(%d : %d) ",x.first,x.second);
    }
    puts("");
}


void createOrderedNode()
{
    for(int i=1; i<=QUERY_NODE; i++)
    {
        ordered_node.pb({query_graph[i].size(),i});
    }
    sort(all(ordered_node));
    reverse(all(ordered_node));
}

int nextQueryVertex(set<int>M_q)
{
    for(auto it : ordered_node)
    {
        if(M_q.find(it.second)==M_q.end()) return it.second;
    }
}


vi refineCandidates(vpi M,int u,set<int>M_g,set<int>M_q)
{
    vi CC = C[u];

    ///prune 1
    for(int i=0; i<CC.size(); i++)
    {
        if(M_g.find(CC[i])==M_g.end())
        {
            CC.erase(CC.begin()+i);
        }
    }
    int sz1 = CC.size();


    ///prune 2
    set<int>C_q,C_g;
    for(auto it : M)
    {
        for(auto nd : query_graph[it.first])
        {
            C_q.insert(nd);
        }
        for(auto nd : data_graph[it.second])
        {
            C_g.insert(nd);
        }
    }

    vector<int>interU,interV;

    for(int i=0; i<query_graph[u].size(); i++)
    {
        int V = query_graph[u][i];
        if(C_q.find(V)!=C_q.end())
            interU.pb(V);
    }

    for(int i=0; i<CC.size(); i++)
    {
        interV.clear();
        for(auto V : data_graph[CC[i]])
        {
            if(C_g.find(V)!=C_g.end())
                interV.pb(V);
        }
        if((int)interU.size()>(int)interV.size())
            CC.erase(CC.begin()+i);
    }
    int sz2 = CC.size();
    //if(sz1!=sz2) puts("Pruning 2 has been used...\n");

    ///prune 3
    vector<int>diffU,diffV;
    int setLenU = 0;
    int setLenV = 0;

    for(auto V : query_graph[u])
    {
        if(C_q.find(V)==C_q.end())
            diffU.pb(V);
    }
    for(auto V : diffU)
    {
        if(M_q.find(V)==M_q.end())
            setLenU++;
    }

    for(int i=0; i<CC.size(); i++)
    {
        diffV.clear();
        setLenV = 0;
        for(auto V : data_graph[CC[i]])
        {
            if(C_g.find(V)==C_g.end())
                diffV.pb(V);
        }
        for(auto V : diffV)
        {
            if(M_g.find(V)==M_g.end())
                setLenV++;
        }
        if(setLenU>setLenV)
        {
            CC.erase(CC.begin()+i);
            // puts("Pruning 3 has been used...\n");
        }
    }

    return CC;
}

bool existsInSol(int v,vpi M,int which=2)
{
    if(which==2)
    {
        for(auto it : M)
        {
            if(it.second == v)
                return 1;
        }
        return 0;
    }
    else
    {
        for(auto it : M)
        {
            if(it.first == v)
                return 1;
        }
        return 0;
    }
}


bool isJoinable(int u,int v,vpi M)
{
    ///make list for u from M and query_graph[u]
    vi edgeList;

    for(auto it : M)
    {
        if(binary_search(all(query_graph[u]),it.first))
            edgeList.pb(it.second);
    }

    /// check whether v has connections with the matching nodes of it's adjacent nodes
    for(auto it : edgeList)
    {
        if(!binary_search(all(data_graph[v]),it))
            return 0;
    }
    return 1;
}

void get_match(vpi M,set<int>M_g,set<int>M_q,clock_t st)
{
    if(noOfSoln>=THRESHOLD || double(clock() - st) / CLOCKS_PER_SEC >=TIME_THRESHOLD) return;
    if((int)M.size()==QUERY_NODE)
    {
        //printf("Matching found...\n");
        noOfSoln++;
        #ifdef TOP_K_ENABLE
        if(noOfSoln>=TOP_K[qN])
        {
            STOP = 1;
        }
        #endif
       // printf("Result no %d\n",noOfSoln);
        //printVecPair(M);
        return;
    }

    int u = nextQueryVertex(M_q);
    vi Cr = refineCandidates(M,u,M_g,M_q);

    for(auto v : Cr)
    {
        if(existsInSol(v,M))
            continue;

        if(isJoinable(u,v,M))
        {
            M.pb({u,v});
            M_g.insert(v);
            M_q.insert(u);
            get_match(M,M_g,M_q,st);
            M.pop_back();
            M_g.erase(v);
            M_q.erase(u);
        }
    }
}

ll genHash(int qnode,bool structed = 0)
{
    if(!structed)
    {
        str.clear();
        for(int i=1; i<=qnode; i++)
        {
            str.pb(query_label[i]);
            str.pb(i);
            for(auto it : query_graph[i])
            {
                str.pb(it);
            }
            str.pb(query_graph[i].size());
        }
        len = str.size();
        //pre();
        return getHash(0,len-1,0);
    }
    else
    {
        str.clear();
        for(int i=1;i<=qnode;i++)
        {
            str.pb(query_graph[i].size());
        }
        sort(all(str));
        str.push_back(qnode);
        len = str.size();
        //pre();
        return getHash(0,len-1,0);
    }
}

ofstream resultWrite;

void genericQueryProc(int qnode)
{

    srand(time(0));
    clock_t st = clock();
    for(int i=1; i<=qnode; i++)
    {
        if(dataTag[query_label[i]].size()==0)
            return;
        C[i] = dataTag[query_label[i]];
    }
    createOrderedNode();
    vpi M;
    set<int>M_g,M_q;

    ll struc_hashValue = genHash(qnode,1);
    ll spec_hashValue = genHash(qnode,0);

    ll dpVal = 0;
    //if(spt.searchValue(hashValue,dpVal)==0)
    if(spt.find(struc_hashValue)==spt.end())
    {
        cout << "NOT PROCESSED EARLIER\n";
        writeToFile << "NOT PROCESSED EARLIER\n";
        get_match(M,M_g,M_q,st);
        //spt.Insert({hashValue,noOfSoln});
        spt[struc_hashValue][spec_hashValue] = noOfSoln;
        //getchar();
    }
    else
    {
        if(spt[struc_hashValue].find(spec_hashValue)==spt[struc_hashValue].end())
        {
             cout << "PROCESSED EARLIER,BUT NOT EXACTLY\n";
             writeToFile << "PROCESSED EARLIER,BUT NOT EXACTLY\n";
            get_match(M,M_g,M_q,st);
            spt[struc_hashValue][spec_hashValue] = noOfSoln;
            //getchar();
        }
        else
        {
            cout << "EXACTLY PROCESSED EARLIER\n";
            writeToFile << "EXACTLY PROCESSED EARLIER\n";
            noOfSoln = spt[struc_hashValue][spec_hashValue];
            //getchar();
        }

    }
    writeToFile << "Elapsed time : " << showTime(st) << "\n";
    cout << "Elapsed Time : " << showTime(st) << "\n";
    CLR(qnode);
    return;
}

int main()
{
    pre();
    dataGraph.open("data/dGraph(small).txt");
    queryGraph.open("queries/multiple_queries_100.txt");
    writeToFile.open("result.txt");

    graph_input();
    int testCase = 1;
    queryGraph >> testCase;
    for(int qN = 1;qN<=testCase;qN++)
    {
        query_input();
        genericQueryProc(QUERY_NODE);
        cout << noOfSoln << "\n";
        writeToFile << noOfSoln << "\n";
        noOfSoln = 0;
    }
    dataGraph.close();
    queryGraph.close();
    writeToFile.close();
    return 0;
}
