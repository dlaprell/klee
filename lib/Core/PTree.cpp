//===-- PTree.cpp ---------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "PTree.h"

#include <klee/Expr.h>
#include <klee/util/ExprPPrinter.h>

#include <vector>
#include <iterator>
#include <algorithm>
#include <klee/ExecutionState.h>

using namespace klee;

  /* *** */

PTree::PTree(const data_type &_root) : root(new Node(0,_root)) {
}

PTree::~PTree() {}

std::pair<PTreeNode*, PTreeNode*>
PTree::split(Node *n, 
             const data_type &leftData, 
             const data_type &rightData) {
  assert(n && !n->left && !n->right);
  n->left = new Node(n, leftData);
  n->right = new Node(n, rightData);
  return std::make_pair(n->left, n->right);
}

void PTree::remove(Node *n) {
  assert(!n->left && !n->right);
  do {
    Node *p = n->parent;
    if (p) {
      if (n == p->left) {
        p->left = 0;
      } else {
        assert(n == p->right);
        p->right = 0;
      }
    }
    delete n;
    n = p;
  } while (n && !n->left && !n->right);
}

void PTree::dump(llvm::raw_ostream &os) {
  ExprPPrinter *pp = ExprPPrinter::create(os);
  pp->setNewline("\\l");
  os << "digraph G {\n";
  os << "\tsize=\"10,7.5\";\n";
  os << "\tratio=fill;\n";
  os << "\trotate=90;\n";
  os << "\tcenter = \"true\";\n";
  os << "\tnode [style=\"filled\",width=.1,height=.1,fontname=\"Terminus\"]\n";
  os << "\tedge [arrowsize=.5]\n";
  std::vector<PTree::Node*> stack;
  stack.push_back(root);
  while (!stack.empty()) {
    PTree::Node *n = stack.back();
    stack.pop_back();
    if (n->condition.isNull()) {
      if (n->schedulingDecision.epochNumber == 0) {
        os << "\tn" << n << " [label=\"\"";
      } else {
        os << "\tn" << n << " [label=\"";
        os << n->schedulingDecision.scheduledThread << " @ ep=" << n->schedulingDecision.epochNumber;
        os << "\",shape=pentagon";
      }
    } else {
      os << "\tn" << n << " [label=\"";
      pp->print(n->condition);
      os << "\",shape=diamond";
    }
    if (n->data) {
      os << ",fillcolor=green";
    }
    os << "];\n";
    if (n->left) {
      os << "\tn" << n << " -> n" << n->left << ";\n";
      stack.push_back(n->left);
    }
    if (n->right) {
      os << "\tn" << n << " -> n" << n->right << ";\n";
      stack.push_back(n->right);
    }
  }
  os << "}\n";
  delete pp;
}

PTreeNode::PTreeNode(PTreeNode *_parent, 
                     ExecutionState *_data) 
  : parent(_parent),
    left(0),
    right(0),
    data(_data),
    condition(0) {
  schedulingDecision.epochNumber = 0;
  schedulingDecision.scheduledThread = 0;
}

PTreeNode::~PTreeNode() {
}

