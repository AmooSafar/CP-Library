/*
	verification : https://dmoj.ca/problem/ds5

	use LinkCutTree<Type, Info, Lazy> : type of node date, info of Subtree
	
	Info requirements:
		Info += Info 
		Info += Lazy
		Info() should Create empty Info
		Info(Type) should Create Info of single element
	Lazy requirements:
		bool() return true if lazy is doing sth false otherwise
		Lazy() should Create lazy that do nothing
		Lazy += Lazy
	Type requirements:
		T += Lazy
*/

namespace SubtreeLinkCutTree {

	template<typename Type, typename Info, typename Lazy> // node Value, Info, Lazy
	struct SplayTree {
		Info info[2]; // 0 aux, 1 all_sub - aux 
		Lazy lz[2]; // 0 aux, 1 all_sub - aux
		SplayTree* par;
		SplayTree* ch[5]; // aux. L, aux. R, p.p. L, p.p R, p.p tree root
		int id;
		Type val; // node number,  current value
		int rev; // lz of reverse of aux.
		SplayTree(int _id, Type v){
			par = NULL;
			for(int i = 0; i < 5; i++) ch[i] = NULL;
			id = _id;
			val = v;
			rev = 0;
			info[0] = Info(v); info[1] = Info();
			lz[0] = Lazy(); lz[1] = Lazy();
		}
		int WhichChild(){ // root is -1, pp is 4
			if(par == NULL) return -1;
			for(int i = 0; i < 5; i++)
				if(par -> ch[i] == this)
					return i;
			return -2;
		}
		bool RootAux(){ return (par == NULL) || ((par -> ch[0] != this) && (par -> ch[1] != this)); }
		bool Root(){ return (!par) || (par -> ch[4] == this); }

		void RemoveChild(int child){ // be carefull about child's par
			if(this -> ch[child])
				this -> ch[child] -> par = NULL;
			this -> ch[child] = NULL;
		}
		void AddChild(SplayTree* C, int child){
			this -> ch[child] = C;
			if(C)
				C -> par = this;
		}
		void Rotate(){
			if(this -> Root()) return ;

			auto *p = par;
			auto *anc = p -> par;

			p -> Push();
			this -> Push();

			int x = this -> WhichChild(), y = p -> WhichChild();

			if(x == 0 || x == 1){ // Aux. Tree Rotate
				for(int i = 2; i < 4; i++){
					this -> AddChild(p -> ch[i], i);
					p -> ch[i] = NULL;
				}
			}

			p -> AddChild(this -> ch[x^1], x);
			this -> AddChild(p, x^1);

			if(y != -1)
				anc -> AddChild(this, y);

			this -> par = anc;
			
			p -> Pull();
			this -> Pull();
		}
		void SplayStep(){
			if(par -> Root()) return Rotate();
			(this -> WhichChild() != par -> WhichChild() ? this : par) -> Rotate();
			Rotate();
		}
		void SplayAuxStep(){
			if(par -> RootAux()) return Rotate();       
			(this -> WhichChild() != par -> WhichChild() ? this : par) -> Rotate();
			Rotate();
		}
		void Splay(){
			while(!RootAux()) SplayAuxStep();
			while(!Root()) SplayStep();
			this -> Push();
		}

		// Data Functions
		void ApplyAux(const Lazy& L){
			val += L;
			info[0] += L; lz[0] += L;
		}
		void ApplyNotAux(const Lazy& L){
			info[1] += L; lz[1] += L;
		}
		void ApplyAll(const Lazy& L){ ApplyAux(L); ApplyNotAux(L); }

		void Rev(){ rev ^= 1; swap(ch[0], ch[1]); }
		void Push(){
			if(rev){ for(int i = 0; i < 2; i++) if(ch[i]) ch[i] -> Rev(); }
			if(lz[0])
				for(int i = 0; i < 2; i++)
					if(ch[i]) ch[i] -> ApplyAux(lz[0]);
			if(lz[1]){ 
				for(int i = 0; i < 5; i++) if(ch[i]){
					ch[i] -> ApplyNotAux(lz[1]);
					if(i > 1) ch[i] -> ApplyAux(lz[1]);
				}
			}
			rev = 0;
			lz[0] = lz[1] = Lazy();
		}
		void Pull(){ // Push Required
			info[0] = Info(val); info[1] = Info();
			for(int i = 0; i < 5; i++) if(ch[i]){
				info[1] += ch[i] -> info[1];
				info[i >= 2] += ch[i] -> info[0];
			}
		}

		friend SplayTree* Walk(SplayTree* st, int dir){
			st -> Push();
			while(st -> ch[dir]){
				st = st -> ch[dir];
				st -> Push();
			}
			st -> Splay();
			return st;
		}
		friend SplayTree* Append(SplayTree* A, SplayTree* B){ // returns A;
			if(!A) return B;
			A -> Splay();
			auto mx = Walk(A, 3); // Max in pp Tree

			mx -> AddChild(B, 3);
			mx -> Pull();

			A -> Splay();
			return A;
		}
		friend SplayTree* RemoveFromTree(SplayTree* A){
			A -> Splay();
			
			auto L = A -> ch[2], R = A -> ch[3];
			A -> RemoveChild(2); A -> RemoveChild(3);
			A -> Pull();
			auto X = Append(L, R);
			if(X) X -> par = A -> par;

			return X;
		}
	};

	template<typename Type, typename Info, typename Lazy>
	struct LinkCutTree {
		using Splay = SplayTree<Type, Info, Lazy>;
		vector<Splay*> ver;
		int n;
		LinkCutTree(int _n, vector<Type> W) : ver(_n, NULL), n(_n) {
			for(int i = 0; i < n; i++) ver[i] = new Splay(i, W[i]);
		}
		void Access(int u){
			Splay *la = NULL;
			for(auto *nw = ver[u]; nw; nw = nw -> par){
				nw -> Splay();

				// Get Rid of Right
				auto R = nw -> ch[1];
				if(R){
					nw -> RemoveChild(1);
					nw -> AddChild(Append(R, nw -> ch[4]), 4);
				}
				
				// Add new Right
				if(la){
					auto PP_root = RemoveFromTree(la);
					nw -> AddChild(la, 1);
					nw -> AddChild(PP_root, 4);
				}
				la = nw;
				nw -> Pull();
			}
			ver[u] -> Splay();
		}

		void MakeRoot(int u){
			Access(u);
			ver[u] -> Rev();
		}
		void Link(int u, int v){
			MakeRoot(u);
			Access(v);
			ver[v] -> AddChild(Append(ver[v] -> ch[4], ver[u]), 4);
			ver[v] -> Pull();
		}
		void Cut(int u){
			Access(u);
			ver[u] -> RemoveChild(0);
			ver[u] -> Pull();
		}
		int LCA(int u, int v){
			Access(u);
			Access(v);
			ver[u] -> Splay();
			return (ver[u] -> par ? ver[u] -> par : ver[u]) -> id;
		}

		void ApplyPath(int u, int v, const Lazy& L){
			MakeRoot(u);
			Access(v);
			ver[v] -> ApplyAux(L);
		}
		Info GetPath(int u, int v){
			MakeRoot(u);
			Access(v);
			return ver[v] -> info[0];
		}

		void ApplySub(int u, const Lazy& L){
			Access(u);
			ver[u] -> val += L;
			for(int i = 2; i < 5; i++) if(ver[u] -> ch[i])
				ver[u] -> ch[i] -> ApplyAll(L);
			ver[u] -> Pull();
		}
		Info GetSub(int u){
			Access(u);
			ver[u] -> Pull();
			Info res(ver[u] -> val);
			for(int i = 2; i < 5; i++) if(ver[u] -> ch[i])
				(res += ver[u] -> ch[i] -> info[0]) += ver[u] -> ch[i] -> info[1];
			return res;
		}	
	};

}

using SubtreeLinkCutTree::LinkCutTree;
