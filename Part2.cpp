#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include <vector>
#include <iostream>
#include <queue>
#include <limits>

using namespace llvm;

#define DEBUG_TYPE "hello"

//STATISTIC(HelloCounter, "Counts number of functions greeted");

/* Question 1 */
namespace {
	struct BasicBlockCount : public FunctionPass {
		static char ID;
		static int func_count;
		static std::vector<int> func_bbcounts;
		//static std::map<std::string, int> func_bbcount; // each function's basic block count
		BasicBlockCount() : FunctionPass(ID) {}

		bool runOnFunction(Function &F) override {
			func_count++;
			//++HelloCounter;
			int bb_count = 0;
			/* iterates over basic blocks in a function */
			for (Function::iterator bb = F.begin(), e = F.end(); bb != e; bb++)
				bb_count++;
			func_bbcounts.push_back(bb_count);
			std::cout << "basic block count in function: "
				  << bb_count << "\n";
			return false;
		}

		/* Apparently this gets called once runOnfunction() is done with all the functions */
		bool doFinalization(Module &M) override {
			std::cout << "Summary: " << "\n";
			std::cout << "total functions: " << func_count << "\n";
			// find max from vector
			std::cout << "max count: " << findmax() << "\n";
			// find min from vector
			std::cout << "min count: " << findmin() << "\n";
			// find avg from vector
			std::cout << "avg: " << getavg() << "\n";
			// print all three
			return false;
		}

	private:
		int findmax() {
			if (func_bbcounts.size() == 0)
				return -1; // error
			int max = func_bbcounts.front();
			std::vector<int>::iterator it;
			for (it = func_bbcounts.begin(); it != func_bbcounts.end(); it++) {
				if (max < *it)
					max = *it;
			}
			return max;
		}

		int findmin() {
			if (func_bbcounts.size() == 0)
				return -1; // error
			int min = func_bbcounts.front();
			std::vector<int>::iterator it;
			for (it = func_bbcounts.begin(); it != func_bbcounts.end(); it++) {
				if (min > *it)
					min = *it;
			}
			return min;
		}

		double getavg() {
			if (func_bbcounts.size() == 0)
				return -1; // error
			double sum = 0.0;
			std::vector<int>::iterator it;
			for (it = func_bbcounts.begin(); it != func_bbcounts.end(); it++) {
				sum += *it;
			}
			return sum / func_count;
		}
	};
}

char BasicBlockCount::ID = 0;
int BasicBlockCount::func_count;
std::vector<int> BasicBlockCount::func_bbcounts;
static RegisterPass<BasicBlockCount> X("bbcount", "Basic Block count for every function");

/* Question 2: number of CFG edges */
namespace {
	struct CFGEdges : public FunctionPass {
		static char ID;
		static int func_count;
		static std::vector<unsigned> edges;
		CFGEdges() : FunctionPass(ID) {}

		bool runOnFunction(Function &F) override {
			func_count++;
			unsigned edge_count = 0;

			//BasicBlock &entry_block = F.getEntryBlock();
			for (Function::iterator bb = F.begin(); bb != F.end(); bb++) {
				BasicBlock &blk = *bb;
				const TerminatorInst *TInst = blk.getTerminator();
				edge_count += TInst->getNumSuccessors();
			}
			edges.push_back(edge_count);
			return false;
		}

		bool doFinalization(Module &M) override {
			std::cout << "[DEBUG] Edge count:\n";
			for (std::vector<unsigned>::iterator it = edges.begin(); it != edges.end(); it++)
				std::cout << *it << " ";
			std::cout << "\n";
			std::cout << "------------------------------\n";
			std::cout << "Summary:\n";
			std::cout << "Max: " << findmax() << "\n";
			std::cout << "Min: " << findmin() << "\n";
			std::cout << "Average: " << getavg() << "\n";
			std::cout << "vector size: " << edges.size() << "\n";
			return false;
		}

	private:
		unsigned findmax() {
			if (edges.size() == 0)
				return -1; // error
			unsigned max = edges.front();
			std::vector<unsigned>::iterator it;
			for (it = edges.begin(); it != edges.end(); it++) {
				if (max < *it)
					max = *it;
			}
			return max;
		}

		unsigned findmin() {
			if (edges.size() == 0)
				return -1; // error
			unsigned min = edges.front();
			std::vector<unsigned>::iterator it;
			for (it = edges.begin(); it != edges.end(); it++) {
				if (min > *it)
					min = *it;
			}
			return min;
		}

		double getavg() {
			if (edges.size() == 0)
				return -1; // error
			double sum = 0.0;
			std::vector<unsigned>::iterator it;
			for (it = edges.begin(); it != edges.end(); it++) {
				sum += *it;
			}
			return sum / func_count;
		}
	};
}

char CFGEdges::ID = 0;
std::vector<unsigned> CFGEdges::edges;
int CFGEdges::func_count;
static RegisterPass<CFGEdges> Y("cfg", "CFG edge count inside functions");

/* Quesiton 3: counts all back edges */
/* back edges are defined as edge (b,a) where a dominates b */
namespace {
	struct SingleEntryLoop : public FunctionPass {
		static char ID;
		static int func_count;
		static std::vector<int> sel; /* single entry loops */
		SingleEntryLoop() : FunctionPass(ID) {}

		void getAnalysisUsage(AnalysisUsage &AU) const {
			AU.addRequired<DominatorTreeWrapperPass>();
			AU.setPreservesAll();
		}

		bool runOnFunction(Function &F) override {
			func_count++;
			int backedges = 0;
			DominatorTree *DT = &getAnalysis<DominatorTreeWrapperPass>().getDomTree();
			for (Function::iterator bb = F.begin(); bb != F.end(); bb++) {
				BasicBlock &blk = *bb;
				const TerminatorInst *TInst = blk.getTerminator();
				for (unsigned i = 0, nSucc = TInst->getNumSuccessors(); i < nSucc; i++) {
					BasicBlock *succ = TInst->getSuccessor(i);
					if (DT->dominates(succ, &blk)) {
						backedges++;
					}
				}
			}
			sel.push_back(backedges);
			return false;
		}

		bool doFinalization(Module &M) override {
			std::cout << "Single Entry Loop count:\n";
			for (std::vector<int>::iterator it = sel.begin(); it != sel.end(); it++)
				std::cout << *it << " ";
			std::cout << "\n";
			std::cout << "------------------------------\n";
			std::cout << "Summary:\n";
			std::cout << "Max: " << findmax() << "\n";
			std::cout << "Min: " << findmin() << "\n";
			std::cout << "Average: " << getavg() << "\n";
			std::cout << "vector length (# of functions): " << sel.size() << "\n";
			return false;
		}

	private:
		int findmax() {
			if (sel.size() == 0)
				return -1; // error
			int max = sel.front();
			std::vector<int>::iterator it;
			for (it = sel.begin(); it != sel.end(); it++) {
				if (max < *it)
					max = *it;
			}
			return max;
		}

		int findmin() {
			if (sel.size() == 0)
				return -1; // error
			int min = sel.front();
			std::vector<int>::iterator it;
			for (it = sel.begin(); it != sel.end(); it++) {
				if (min > *it)
					min = *it;
			}
			return min;
		}

		double getavg() {
			if (sel.size() == 0)
				return -1; // error
			double sum = 0.0;
			std::vector<int>::iterator it;
			for (it = sel.begin(); it != sel.end(); it++) {
				sum += *it;
			}
			return sum / func_count;
		}

	};
}

char SingleEntryLoop::ID = 0;
int SingleEntryLoop::func_count;
std::vector<int> SingleEntryLoop::sel;
static RegisterPass<SingleEntryLoop> Z("sel", "Single entry loop count inside functions");

/* Question 4 */
namespace {
	struct LoopBasicBlock : public FunctionPass {
		static char ID;
		static int func_count;
		static std::vector<int> lbb;
		LoopBasicBlock() : FunctionPass(ID) {}

		void getAnalysisUsage(AnalysisUsage &AU) const {
			AU.addRequired<LoopInfoWrapperPass>();
			AU.setPreservesAll();
		}

		bool runOnFunction(Function &F) override {
			func_count++;
			LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
			int loop_count = 0;
			int bbcount = 0;
			errs() << F.getName() + "\n";
			for (LoopInfo::iterator loop = LI.begin(); loop != LI.end(); loop++) {
				Loop *L = *loop;
				loop_count++;
				//int bbcount = 0;
				for (Loop::block_iterator bb = L->block_begin(); bb != L->block_end(); bb++) {
					bbcount++;
				}
				//lbb.push_back(bbcount);
				errs() << "loop ";
				errs() << loop_count;
				errs() << ": #BBs = ";
				errs() << bbcount << "\n";
			}
			lbb.push_back(bbcount);
			return false;
		}

		bool doFinalization(Module &M) override {
			std::cout << "------------------------------\n";
			std::cout << "Loop basic block count:\n";
			for (std::vector<int>::iterator it = lbb.begin(); it != lbb.end(); it++)
				std::cout << *it << " ";
			std::cout << "\n";
			std::cout << "------------------------------\n";
			std::cout << "Summary:\n";
			std::cout << "Max: " << findmax() << "\n";
			std::cout << "Min: " << findmin() << "\n";
			std::cout << "Average: " << getavg() << "\n";
			std::cout << "vector length (# of functions): " << lbb.size() << "\n";
			return false;
		}

	private:
		int findmax() {
			if (lbb.size() == 0)
				return -1; // error
			int max = lbb.front();
			std::vector<int>::iterator it;
			for (it = lbb.begin(); it != lbb.end(); it++) {
				if (max < *it)
					max = *it;
			}
			return max;
		}

		int findmin() {
			if (lbb.size() == 0)
				return -1; // error
			int min = lbb.front();
			std::vector<int>::iterator it;
			for (it = lbb.begin(); it != lbb.end(); it++) {
				if (min > *it)
					min = *it;
			}
			return min;
		}

		double getavg() {
			if (lbb.size() == 0)
				return -1; // error
			double sum = 0.0;
			std::vector<int>::iterator it;
			for (it = lbb.begin(); it != lbb.end(); it++) {
				sum += *it;
			}
			return sum / func_count;
		}
	};
}

char LoopBasicBlock::ID = 0;
int LoopBasicBlock::func_count;
std::vector<int> LoopBasicBlock::lbb;
static RegisterPass<LoopBasicBlock> A("lbb", "Loop basic block count inside functions");

/* Question 5 */
namespace {
	struct DomCount : public FunctionPass {
		static char ID;
		static int bb_count;
		static std::vector<int> dom_counts;
		DomCount() : FunctionPass(ID) {}

		void getAnalysisUsage(AnalysisUsage &AU) const {
			AU.addRequired<DominatorTreeWrapperPass>();
			AU.setPreservesAll();
		}

		bool runOnFunction(Function &F) override {
			int dom_count = 0;
			DominatorTree *DT = &getAnalysis<DominatorTreeWrapperPass>().getDomTree();

			for (Function::iterator bb = F.begin(); bb != F.end(); bb++) {
				bb_count++;
				BasicBlock &blk = *bb;

				for (Function::iterator bb_tail = F.begin(); bb_tail != F.end(); bb_tail++) {
					BasicBlock &blk_tail = *bb_tail;
					if (DT->properlyDominates(&blk_tail, &blk))
						dom_count++;
				}

				// for (auto node = GraphTraits<DominatorTree *>::nodes_begin(DT);
				//      node != GraphTraits<DominatorTree *>::nodes_end(DT); ++node) {
				// 	dom_count++;
				// 	if (&blk == node->getBlock())
				// 		break;
				// }
			}

			// for (auto node = GraphTraits<DominatorTree *>::nodes_begin(DT);
			//      node != GraphTraits<DominatorTree *>::nodes_end(DT); ++node) {
			// 	dom_count++;

			// 	//BasicBlock *BB = node->getBlock();

			// }
			errs() << "Dom count in function ";
			errs() << F.getName() << ": " << dom_count << "\n";
			dom_counts.push_back(dom_count);
			return false;
		}

		bool doFinalization(Module &M) override {
			std::cout << "dom count:\n";
			for (std::vector<int>::iterator it = dom_counts.begin(); it != dom_counts.end(); it++)
				std::cout << *it << " ";
			std::cout << "\n";
			std::cout << "------------------------------\n";
			std::cout << "Summary:\n";
			std::cout << "Average: " << getavg() << "\n";
			std::cout << "vector length (# of functions): " << dom_counts.size() << "\n";
			return false;
		}

		double getavg() {
			if (dom_counts.size() == 0)
				return -1; // error
			double sum = 0.0;
			std::vector<int>::iterator it;
			for (it = dom_counts.begin(); it != dom_counts.end(); it++) {
				sum += *it;
			}
			return sum / bb_count;
		}
	};
}

char DomCount::ID = 0;
int DomCount::bb_count;
std::vector<int> DomCount::dom_counts;
static RegisterPass<DomCount> B("dc",
				"average number of dominators for a basic block across all functions");

/* Part 3 */

/* 3.1.1) Count all loops */
namespace {
	struct AllLoops : public FunctionPass {
		static char ID;
		static int loop_count;
		AllLoops() : FunctionPass(ID) {}

		void getAnalysisUsage(AnalysisUsage &AU) const {
			AU.addRequired<LoopInfoWrapperPass>();
			AU.setPreservesAll();
		}

		void count_loops(Loop *L) {
			loop_count++;
			std::vector<Loop *> subloops = L->getSubLoops();
			for (Loop::iterator sub = subloops.begin(); sub != subloops.end(); sub++) {
				//loop_count++;
				count_loops(*sub);
			}
		}

		bool runOnFunction(Function &F) override {
			LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
			for (LoopInfo::iterator loop = LI.begin(); loop != LI.end(); loop++) {
				count_loops(*loop);
			}
			return false;
		}

		bool doFinalization(Module &M) override {
			std::cout << "All loop count:\n";
			std::cout << "------------------------------\n";
			std::cout << "Summary:\n";
			std::cout << "All loop count: " << loop_count << "\n";
			return false;
		}
	};
}

char AllLoops::ID = 0;
int AllLoops::loop_count;
static RegisterPass<AllLoops> E("allloops", "number of all loops");


/* 3.1.2) */
namespace {
	struct OuterLoops : public FunctionPass {
		static char ID;
		static int loop_count;
		OuterLoops() : FunctionPass(ID) {}

		void getAnalysisUsage(AnalysisUsage &AU) const {
			AU.addRequired<LoopInfoWrapperPass>();
			AU.setPreservesAll();
		}

		bool runOnFunction(Function &F) override {
			LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
			for (LoopInfo::iterator loop = LI.begin(); loop != LI.end(); loop++) {
				loop_count++;
			}
			return false;
		}

		bool doFinalization(Module &M) override {
			std::cout << "Outer loop count:\n";
			std::cout << "------------------------------\n";
			std::cout << "Summary:\n";
			std::cout << "Outer loop count: " << loop_count << "\n";
			return false;
		}
	};
}

char OuterLoops::ID = 0;
int OuterLoops::loop_count;
static RegisterPass<OuterLoops> C("outloops", "number of outermost loops");

/* 3.1.3) total number of loop exit CFG edges */
namespace {
	struct LoopExitEdges : public FunctionPass {
		static char ID;
		static int count;

		LoopExitEdges() : FunctionPass(ID) {}

		void getAnalysisUsage(AnalysisUsage &AU) const {
			AU.addRequired<LoopInfoWrapperPass>();
			AU.setPreservesAll();
		}

		// void count_loopexit(Loop *L) {
		// 	for (Loop::block_iterator bi = L->block_begin(); bi != L->block_end(); bi++)
		// 		if (L->isLoopExiting(*bi))
		// 			count++;
		// 	std::vector<Loop *> subloops = L->getSubLoops();
		// 	for (Loop::iterator sub = subloops.begin(); sub != subloops.end(); sub++) {
		// 		count_loopexit(*sub);
		// 	}
		// }

		bool runOnFunction(Function &F) override {
			LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
			// for (LoopInfo::iterator loop = LI.begin(); loop != LI.end(); loop++) {
			// 	Loop *L = *loop;
			// 	for (Loop::block_iterator bi = L->block_begin(); bi != L->block_end(); bi++) {
			// 		if (L->isLoopExiting(*bi))
			// 			count++;
			// 	}
			// }

			for (Function::iterator bb = F.begin(); bb != F.end(); bb++) {
				BasicBlock &blk = *bb;
				Loop *L = LI.getLoopFor(&blk);
				if (L != NULL && L->isLoopExiting(&blk))
					count++;
			}

			// LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
			// for (LoopInfo::iterator loop = LI.begin(); loop != LI.end(); loop++) {
			// 	count_loopexit(*loop);

			// 	// Loop *L = *loop;
			// 	// for (Loop::block_iterator bi = L->block_begin(); bi != L->block_end(); bi++)
			// 	// 	if (L->isLoopExiting(*bi))
			// 	// 		count++;
			// 	// std::vector<Loop *> subloops = L->getSubLoops();
			// 	// for (Loop::iterator sub = subloops.begin(); sub != subloops.end(); sub++) {
			// 	// 	for (Loop::block_iterator bb = (*sub)->block_begin(); bb != (*sub)->block_end(); bb++) {
			// 	// 		if ((*sub)->isLoopExiting(*bb))
			// 	// 			count++;
			// 	// 	}
			// 	// }
			// }
			return false;
		}

		bool doFinalization(Module &M) override {
			std::cout << "------------------------------\n";
			std::cout << "Summary:\n";
			std::cout << "loop exit edge count: " << count << "\n";
			return false;
		}
	};
}

char LoopExitEdges::ID = 0;
int LoopExitEdges::count;
static RegisterPass<LoopExitEdges> D("lee", "loop exit edge count");


/* 3.2: Warshall's algorithm  */
namespace {
	struct Warshall : public FunctionPass {
		static char ID;
		static int total_loops;
		static int INF;
		Warshall() : FunctionPass(ID) {}

		void getAnalysisUsage(AnalysisUsage &AU) const {
			AU.addRequired<DominatorTreeWrapperPass>();
			AU.setPreservesAll();
		}

		void print_table(std::map<BasicBlock *, std::map<BasicBlock *, int> > &dist) {
			// debug
			std::map<BasicBlock *, std::map<BasicBlock *, int> >::iterator it;
			std::map<BasicBlock *, int>::iterator it_in;
			for (it = dist.begin(); it != dist.end(); it++) {
				BasicBlock *row = it->first;
				errs() << row->getName() << " ";
				std::map<BasicBlock *, int> &inner_map = dist[row];
				for (it_in = inner_map.begin(); it_in != inner_map.end(); it_in++) {
					BasicBlock *col = it_in->first;
					errs() << inner_map[col] << "\t  ";
				}
				errs() << "\n";
			}
			errs() << "\n";
		}

		void print_next_table(std::map<BasicBlock *, std::map<BasicBlock *, BasicBlock *> > &next) {
			// debug
			std::map<BasicBlock *, std::map<BasicBlock *, BasicBlock *> >::iterator it;
			std::map<BasicBlock *, BasicBlock *>::iterator it_in;
			for (it = next.begin(); it != next.end(); it++) {
				BasicBlock *row = it->first;
				std::map<BasicBlock *, BasicBlock *> &inner_map = next[row];
				for (it_in = inner_map.begin(); it_in != inner_map.end(); it_in++) {
					BasicBlock *col = it_in->first;
					if (inner_map[col] == NULL)
						errs() << inner_map[col] << "\t   ";
					else
						errs() << inner_map[col]->getName() << "   ";
				}
				errs() << "\n";
			}
			errs() << "\n";
		}

		void print_vector(std::vector<BasicBlock *> *path) {
			errs() << "printing vector...\n";
			std::vector<BasicBlock *>::iterator it;
			for (it = path->begin(); it != path->end(); it++) {
				errs() << (*it)->getName() << " ";
			}
			errs() << "\n";
		}

		bool vector_equals(std::vector<BasicBlock *> *path1, std::vector<BasicBlock *> *path2) {
			// errs() << "comparing vector...\n";
			if (path1->size() != path2->size())
				return false;
			std::vector<BasicBlock *>::iterator p1_it;
			std::vector<BasicBlock *>::iterator p2_it;
			for (p1_it = path1->begin(); p1_it != path1->end(); p1_it++) {
				BasicBlock *blk1 = *p1_it;
				bool found = false;
				for (p2_it = path2->begin(); p2_it != path2->end(); p2_it++) {
					BasicBlock *blk2 = *p2_it;
					if (blk1 == blk2) {
						found = true;
						break;
					}
				}
				if (found == false) {
					// errs() << "two vectors are NOT equal!\n";
					return false;
				}
			}
			// errs() << "two vectors are equal!\n";
			return true;
		}

		bool in_set(std::set<std::vector<BasicBlock *> *> &paths_completed, std::vector<BasicBlock *> *path) {
			std::set<std::vector<BasicBlock *> *>::iterator set_it;
			for (set_it = paths_completed.begin(); set_it != paths_completed.end(); set_it++) {
				//debug
				// print_vector(*set_it);
				// print_vector(path);
				if (vector_equals(*set_it, path))
					return true;
			}
			return false;
		}

		bool runOnFunction(Function &F) override {
			std::map<BasicBlock *, std::map<BasicBlock *, int> > dist;
			std::map<BasicBlock *, std::map<BasicBlock *, BasicBlock *> > next;

			// init
			for (Function::iterator bb = F.begin(), bb_end = F.end(); bb != bb_end; bb++) {
				BasicBlock &blk = *bb;
				const TerminatorInst *TInst = blk.getTerminator();
				for (Function::iterator bb_in = F.begin(), bb_in_end = F.end(); bb_in != bb_in_end; bb_in++) {
					BasicBlock &blk_in = *bb_in;
					if (&blk == &blk_in)
						dist[&blk][&blk_in] = 0;
					else
						//dist[&blk][&blk_in] = -1;
						dist[&blk][&blk_in] = INF;
					next[&blk][&blk_in] = NULL;
				}
				for (unsigned i = 0, nSucc = TInst->getNumSuccessors(); i < nSucc; i++) {
					BasicBlock *succ = TInst->getSuccessor(i);
					dist[&blk][succ] = 1;
					next[&blk][succ] = succ;
				}
			}

			errs() << "right after init:\n";
			errs() << "dist table:\n";
			print_table(dist);
			errs() << "next table:\n";
			print_next_table(next);

			for (Function::iterator k = F.begin(), k_end = F.end(); k != k_end; k++) {
				BasicBlock &blk_k = *k;
				for (Function::iterator i = F.begin(), i_end = F.end(); i != i_end; i++) {
					BasicBlock &blk_i = *i;
					for (Function::iterator j = F.begin(), j_end = F.end(); j != j_end; j++) {
						BasicBlock &blk_j = *j;
						if (dist[&blk_i][&blk_j] > dist[&blk_i][&blk_k] + dist[&blk_k][&blk_j]) {
							// errs() << dist[&blk_i][&blk_j] << ", " << dist[&blk_i][&blk_k] << ", " << dist[&blk_k][&blk_j] << "\n";
							dist[&blk_i][&blk_j] = dist[&blk_i][&blk_k] + dist[&blk_k][&blk_j];
							next[&blk_i][&blk_j] = next[&blk_i][&blk_k];
						}
					}
				}
			}

			errs() << "right after Warshall's:\n";
			errs() << "dist table:\n";
			print_table(dist);
			errs() << "next table:\n";
			print_next_table(next);

			DominatorTree *DT = &getAnalysis<DominatorTreeWrapperPass>().getDomTree();

			//std::vector<BasicBlock *> path;
			std::set<std::vector<BasicBlock *> *> paths_completed;
			// bool multi_flag = true;
			// debug
			errs() << "# of basic blocks: " << F.size() << "\n";
			for (Function::iterator bb = F.begin(), bb_end = F.end(); bb != bb_end; bb++) {
				BasicBlock &blk = *bb;
				errs() << blk.getName() << " ";
			}
			errs() << "\n";

			std::set<std::pair<BasicBlock *, BasicBlock *> > predecessor_entry;
			for (Function::iterator bb = F.begin(), bb_end = F.end(); bb != bb_end; bb++) {
				BasicBlock &b1 = *bb;
				//BasicBlock *b1_cpy = &b1;
				for (Function::iterator bb_in = F.begin(), bb_in_end = F.end(); bb_in != bb_in_end; bb_in++) {
					std::vector<BasicBlock *> *path = new std::vector<BasicBlock *>();
					BasicBlock &b2 = *bb_in;
					//if (dist[&b1][&b2] == INF || dist[&b2][&b1] == INF || dist[&b1][&b2] == 0 || dist[&b1][&b2] == 0)
					// errs() << dist[&b1][&b2] << ", " << dist[&b2][&b1] << "\n";
					if (dist[&b1][&b2] == INF || dist[&b2][&b1] == INF)
						continue;
					if (dist[&b1][&b2] == 0 || dist[&b2][&b1] == 0)
						continue;
					// errs() << "cycle path pushing: ";
					// errs() << b1.getName() << " ";
					path->push_back(&b1);
					BasicBlock *b1_cpy = &b1;
					// while (b1_cpy != &b2 && next[b1_cpy][&b2] != NULL) {
					while (b1_cpy != &b2) {
						b1_cpy = next[b1_cpy][&b2];
						// errs() << b1_cpy->getName() << " ";
						path->push_back(b1_cpy);
					}
					// errs() << " and then, ";
					BasicBlock *b2_cpy = next[&b2][&b1];
					//while (b2_cpy != &b1 && next[b2_cpy][&b1] != NULL) {
					while (b2_cpy != &b1) {
						// errs() << b2_cpy->getName() << " ";
						path->push_back(b2_cpy);
						b2_cpy = next[b2_cpy][&b1];
						//path.push_back(b2_cpy);
					}
					// errs() << "\n";

					// debug
					errs() << "cycle path found: ";
					for (auto v : *path)
						errs() << v->getName() << " (" << v << ") ";
					errs() << "\n";

					// check if this path already has been looked at
					if (in_set(paths_completed, path)) {
						errs() << "this path has already been looked at\n";
						delete path;
						continue;
					} else {
						errs() << "adding path to paths_completed...\n";
						paths_completed.insert(path);

						// loop count logic here!!
						for (auto v : *path) {
							for (Function::iterator basic = F.begin(); basic != F.end(); basic++) {
								bool break_flag = false;
								BasicBlock &basicblock = *basic;
								if (in_cycle_path(*path, &basicblock))
									continue;
								const TerminatorInst *TInst = basicblock.getTerminator();
								for (unsigned i = 0, nSucc = TInst->getNumSuccessors(); i < nSucc; i++) {
									BasicBlock *succ = TInst->getSuccessor(i);
									if (succ == v) {
										if (DT->dominates(v, &basicblock))
											continue;
										std::pair<BasicBlock *, BasicBlock *> ans(&basicblock, v);
										if (in_pred_entry(predecessor_entry, ans))
											continue;
										errs() << "[ANS] " << basicblock.getName() << " -> " << v->getName() << "\n";
										predecessor_entry.insert(ans);
										total_loops++;
										break_flag = true;
										break;
									}
								}
								if (break_flag)
									break;
							}
						}
					}
					//path.clear();
					//delete path;
					//break;
					//break;
					errs() << "\n";
				}
			}
			return false;
		}

		bool in_pred_entry(std::set<std::pair<BasicBlock *, BasicBlock *> > &pred_entry, std::pair<BasicBlock *, BasicBlock *> &ans) {
			std::set<std::pair<BasicBlock *, BasicBlock *> >::iterator it;
			for (it = pred_entry.begin(); it != pred_entry.end(); it++) {
				const std::pair<BasicBlock *, BasicBlock *> &pred = *it;
				if (pred.first == ans.first && pred.second == ans.second) {
					errs() << "already found this pred!\n";
					return true;
				}
			}
			return false;
		}

		bool in_cycle_path(std::vector<BasicBlock *> &path, BasicBlock *bb) {
			std::vector<BasicBlock *>::iterator it;
			for (it = path.begin(); it != path.end(); it++) {
				if (*it == bb)
					return true;
			}
			return false;
		}

		bool doFinalization(Module &M) override {
			std::cout << "------------------------------\n";
			std::cout << "Summary:\n";
			errs() << "total loops: " << total_loops << "\n";
			// std::cout << "single entry loops detected: " << sel << "\n";
			// std::cout << "multi entry loops detected: " << mel << "\n";
			return false;
		}
	};
}

char Warshall::ID = 0;
int Warshall::total_loops;
int Warshall::INF = 99999;
static RegisterPass<Warshall> G("warshall", "warshall impl");

/* 3.3: Control dependence */
namespace {
	struct ControlDep : public FunctionPass {
		static char ID;
		static int func_count;
		//static std::map<BasicBlock *, std::vector<BasicBlock> > cdmap;
		ControlDep() : FunctionPass(ID) {}

		void getAnalysisUsage(AnalysisUsage &AU) const {
			AU.addRequired<PostDominatorTree>();
			AU.setPreservesAll();
		}

		bool runOnFunction(Function &F) override {
			func_count++;
			PostDominatorTree *PDT = &getAnalysis<PostDominatorTree>();
			for (Function::iterator bb = F.begin(); bb != F.end(); bb++) {
				BasicBlock &B1 = *bb;
				//errs() << blk.getName() << ": ";
				//std::vector<BasicBlock> list;
				errs() << "Basic Blocks that are control dependent on " << *B1.getFirstNonPHI() << "={";
				for (Function::iterator bb_tail = F.begin(); bb_tail != F.end(); bb_tail++) {
					BasicBlock &B2 = *bb_tail;
					if (!PDT->dominates(&B2, &B1)) {
						const TerminatorInst *TInst = B1.getTerminator();
						for (unsigned i = 0, nSucc = TInst->getNumSuccessors(); i < nSucc; i++) {
							BasicBlock *succ = TInst->getSuccessor(i);
							if (PDT->dominates(&B2, succ)) {
								errs() << *B2.getFirstNonPHI() << ", ";
								//errs() << B2.getName() << "\n";
								break;
							}
						}
						//list.push_back(blk_tail);
					}
					//errs() << "}\n";
				}
				errs() << "}\n";

				//cdmap[&blk] = list;
			}
			return false;
		}

		bool doFinalization(Module &M) override {
			std::cout << "------------------------------\n";
			std::cout << "Summary:\n";
			return false;
		}
	};
}

char ControlDep::ID = 0;
int ControlDep::func_count;
//std::map<BasicBlock *, std::vector<BasicBlock> > ControlDep::cdmap;
static RegisterPass<ControlDep> F("cdep", "Control dependence");

/* 3.4: Reachability */
namespace {
	struct Reach : public FunctionPass {
		static char ID;
		Reach() : FunctionPass(ID) {}

		bool runOnFunction(Function &F) override {
			// BasicBlock *A;
			// BasicBlock *B;
			// A = &F.getEntryBlock();
			// B = A->getTerminator()->getSuccessor(0);


			for (Function::iterator bb = F.begin(), bb_end = F.end(); bb != bb_end; bb++) {
				BasicBlock &b1 = *bb;
				for (Function::iterator bb_in = F.begin(), bb_in_end = F.end(); bb_in != bb_in_end; bb_in++) {
					BasicBlock &b2 = *bb_in;
					if (bfs(&b1, &b2))
						;// errs() << b1.getName() << " to " << b2.getName() << " is reachable\n";
					else
						;// errs() << b1.getName() << " to " << b2.getName() << " is NOT reachable\n";
				}
			}

			// if (bfs(A, B))
			// 	std::cout << "A to B is reachable\n";
			// else
			// 	std::cout << "A to B is NOT reachable\n";
			// return false;
			return false;
		}

		bool bfs(BasicBlock *A, BasicBlock *B) {
			std::queue<BasicBlock *> q;
			std::map<BasicBlock *, bool> visited;
			q.push(A);

			while (q.size() > 0) {
				BasicBlock *blk = q.front();
				q.pop();
				visited[blk] = true;
				const TerminatorInst *TInst = blk->getTerminator();
				for (unsigned i = 0, nSucc = TInst->getNumSuccessors(); i < nSucc; i++) {
					BasicBlock *succ = TInst->getSuccessor(i);
					if (succ == B)
						return true;
					else if (visited.count(succ) != 1)
						q.push(succ);
				}
			}
			return false;
		}

		bool doFinalization(Module &M) override {
			std::cout << "------------------------------\n";
			std::cout << "Summary:\n";
			return false;
		}
	};
}

char Reach::ID = 0;
static RegisterPass<Reach> H("reach", "reachability from basic block A to B");
