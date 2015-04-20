#!/usr/bin/python
# -*- coding: utf-8 -*-
#

"""
Script to extract sentences from Penn Treebank
"""

import os;
import sys;
import re;
import math;
import codecs;
import string;
import xml.etree.ElementTree as ET;
from StringIO import StringIO as sio;
from treelib import *;
from path_finder import *;
    
class PBAnnotationChecker(object):
  """
  This is useful to check whether we have propbank annotation on the tree.
  """
  def __init__(self):
    self.filename = "";
    self.sentence = -1;
    self.vv = 0;
    self.vpred = 0;

  def CountPred(self, node):
    """
    This method is used to count the number of annotations we should have.
    We simply check the number of level zero span with V* tag.
    """
    if node.children:   
      res = 0;
      for child in node.children:
        res += self.CountPred(child);
      return res;
    else:
      if node.tag.startswith("V"):
        self.vv += 1;
        if len(node.arguments) != 0:
          self.vpred += 1;
        return 1;
      else:
        return 0;

  def __call__(self, node):
    """
    If the number of actual annotations is more than the number of needed
    annotations, we like it. Otherwise, it is bad.
    """
    return True;
    predcount = self.CountPred(node);
    if predcount == 0: return True;
    return len(node.predicates) != 0;

#
# There are couple things that we need to do before we let path finder to run.
#

class SelfProductionRemover(object):
  """
  Remove the self production node where an NonTerminla expand to itself.
  """
  def TagEqual(self, n0, n1):
    f0 = n0.tag.split("-");
    f1 = n1.tag.split("-");
    return f0[0] == f1[0];

  def Tag(self, n0, n1):
    f0 = n0.tag.split("-");
    f1 = n1.tag.split("-");    
    if len(f1) != 1: f0.append("|");
    return string.join(f0 + f1[1:], "-");

  def __call__(self, node):
    """remove the self production, on node where there is only one child, and it
    has the same tag as the node itself.
    """
    if node.children:
      if len(node.children) == 1:
        if self.TagEqual(node.children[0], node):
          #print node.ToString()
          node.tag = self.Tag(node, node.children[0]);
          lst = node.children[0].children;
          node.children = lst;

class StackPairFinder(object):
  """This class is used to find all the pair of things from input"""
  def __init__(self, pairs):
    self.filename = ""
    self.dict= {};
    self.debug = False;
    if len(pairs) % 2 != 0: raise ValueError("Can't pair up");
    size = len(pairs)/2;
    for i in range(size):
      self.dict[pairs[2*i]] = None;
      self.dict[pairs[2*i+1]] = pairs[2*i];
  
  def FindFromTokens(self, tkns, sink):
    """This is used to find all pairs from token sequence."""
    stack = [];
    stt = 0;
    for i in range(len(tkns)):
      if not self.dict.has_key(tkns[i]): continue;
      if self.dict[tkns[i]]:
        if len(stack) == 0:
          stt -= 1;
          sink.append((stt, i));
        else:
          front = stack.pop();
          if front[0] != self.dict[tkns[i]]:
            raise ValueError("Wrong pair at %s" % self.filename);
          sink.append((front[1], i));
      else:
        stack.append((tkns[i], i));
    end = len(tkns);
    while len(stack) != 0:
      front = stack.pop();
      sink.append((front[1], end));
      end += 1;

  def Find(self, children, sink):
    """We only deal with at lowest level, terminal level, the
    pairs that we find is emitted to sink which should be a
    list of some sort. Note a pair can start at a negative
    position, which basically means there is an unmatched closing
    bracket, or a pair can end with a positon that is longer than
    the number tokens, in which case, there is an unmatched starting
    bracket. Note also this is useful for the unnomalized ctb, where
    brackets are marked with starting/ending marker."""

    tkns = [];
    for child in children:
      key = child.word;
      if not child.word: key = child.tag;
      tkns.append(key);
    self.FindFromTokens(tkns, sink);

class DuplicateMarkerRemover(object):
  """Some sentences contains the duplicate markers, it should
  be ok to remove the duplicates."""
  def __init__(self, markers, badnodes):
    self.badnodes = badnodes;
    self.markers = set();
    for marker in markers:
      self.markers.add(marker);
    self.markers.add(u"＊");
  def IsDuplicate(self, node, i):
    if not node.children: return False;
    if not node.children[i-1].word: return False;
    if not node.children[i].word: return False;
    if not node.children[i-1].tag == "PU": return False;
    if not node.children[i].tag == "PU": return False;
    if node.children[i-1].word != node.children[i].word: return False;
    return node.children[i].word in self.markers;

  def __call__(self, node):
    if not node.children: return;
    # This remove all the node that has only PU as its single child.
    for n in node.children:
      if not n.children: continue;
      if len(n.children) != 1: continue;
      if n.children[0].tag == "PU":
        n.ReplaceBy(n.children[0]);

    # This move all the PRN node that has only one child.
    for n in node.children:
      if not n.children: continue;
      if len(n.children) != 1: continue;
      if n.tag == "PRN":
        n.ReplaceBy(n.children[0]);

    # This remove all the FLR node that has only on PU;
    for n in node.children:
      if n.tag != "FLR": continue;
      if not n.children: continue;
      if len(n.children) != 1: continue;
      if n.children[0].tag != "PU": continue;
      n.ReplaceBy(n.children[0]);

    # This is used to remove the badnodes;
    to_remove = [];
    for i in range(len(node.children)):
      n = node.children[i];
      if (n.ToString() == u"(FLR (PU （) (PU （) (PU ）))" or n.ToString() == u"(FLR (PU ）))" ) and node.children[i+1].ToString() == u"(PU ）)":
        to_remove.append(node.children[i+1]);
        to_remove.append(n);
      elif n.ToString() in self.badnodes:
        to_remove.append(n);
    for n in to_remove:
      if len(n.arguments) != 0: raise ValueError("Deleting a node with Arguments");
      node.children.remove(n);

    duplicates = [];
    for i in range(len(node.children)-1):
      if self.IsDuplicate(node, i+1):
        duplicates.append(node.children[i+1]);
    for x in duplicates:
      node.children.remove(x);

class PairMarkerSplitter(object):
  """Sometime, the pair marker is left combined with other charactor
  to form a token, and we want to split it so that marker is by itself
  a token"""
  def __init__(self, markers):
    self.markers = markers;

  def ProperContainsMarker(self, node):
    """determine whether word of node properly contains one of marker,
    by that we mean word contains one of marker, and at least one other
    charactor"""
    if not node.word: return;
    for mark in self.markers:
      if node.word.find(mark) != -1 and node.word != mark: return mark;
    return None;
      
  def __call__(self, node):
    """If we see a node with a child that has marker combined with other
    charactors, we split them at this level."""
    if not node.children: return;
    ochildren = node.children;
    for n in ochildren:
      mark = self.ProperContainsMarker(n);
      if mark: raise ValueError("not implemented");
      

class PairMatcher(object):
  """
  There are many sentences with wrong bracketing (in another word, there are mismatched)
  when it comes to pairs, most of these errors can be automatically correctted. The
  correction of these errors should make the grammar more compact.
  """
  def __init__(self, pair_finder):
    self.pair_finder = pair_finder;
    self.debug = False;

  def FindUnmatchedPairInTree(self, node, no_starting, no_closeing):
    if not node.children: return;
    lsink = [];
    self.pair_finder.Find(node.children, lsink);
    num_of_children = len(node.children);
    for span in lsink:
      if span[0] < 0: no_starting.append(span);
      if span[1] > num_of_children: no_closeing.append(span);
    for child in node.children:
      self.FindUnmatchedPairInTree(child, no_starting, no_closeing);


  def IsSpanCovered(self, node, span):
    """This method determine whether the span is covered by this node"""
    return node.start <= span[0] and node.start + node.length > span[1];

  def IsSpanCoveredBySomeChild(self, node, span):
    if not node.children: return False;
    tot = 0;
    for child in node.children:
      if self.IsSpanCovered(child, span): tot = 1;
    return tot != 0;

  def FindLeafNode(self, node, index):
    """Find leaf node at index position"""
    if node.start > index or node.end() <= index:
      if self.debug:
        print node.ToPrettyString();
        print index;
      raise ValueError("Node don't contain index");
    if node.start == index and node.level == 0: return node;
    if not node.children:
      raise ValueError("Didn't find the index");
    for child in node.children:
      if child.start <= index and child.end() > index:
        return self.FindLeafNode(child, index);
    if self.debug:
      print node.ToPrettyString();
      print index;
      print "node.start=%d" % node.start;
      print "node.end=%d" % node.end();
    raise ValueError("Shouldn't reach the end");

  def IsAfter(self, node, start):
    """return true is the node starts after given start position"""
    return node.start > start;

  def PushDownToNode(self, node, stack, node_start):
    if not node.children: raise ValueError("Node has no children");
    if node == node_start.parent:
      for xnode in reversed(stack): node.children.append(xnode);
    else:
      lastidx = len(node.children)-1;
      # We push down all the node along the way.
      while node.children[lastidx].start > node_start.start:
        stack.append(node.children.pop());
        lastidx = len(node.children)-1;
      self.PushDownToNode(node.children[lastidx], stack, node_start);

  def MoveUpToNode(self, node, stack, node_start):
    """
    In case we have the following (VP (PU <) (NN x) (NP (NN y) (PU >))),
    we simply extract all the material starting from closing marker, and
    move these up to meet the starting marker.
    """
    if not node.children: raise ValueError("Node has no children");
    if node == node_start.parent:
      for xnode in reversed(stack): node.children.append(xnode);
    else:
      if not node.parent: raise ValueError("something is wrong");
      self.MoveUpToNode(node.parent, stack, node_start);

  def AlignSinglePair(self, root, span):
    """This is used to make sure that the specified span is governed
    by a single node, where both start and close mark is direct children
    of that node.
    The first thing: find out the node that barely cover the span, basically
    the node covers the span, but no child covers it.
    The second thing: find the node that host the starting mark as direct
    child, and moving the rest of thing down to that node.
    """
    if not self.IsSpanCovered(root, span):
      raise ValueError("not covered by node");
    if self.IsSpanCoveredBySomeChild(root, span):
      for child in root.children:
        if self.IsSpanCovered(child, span):
          self.AlignSinglePair(child, span);
    else:
      if self.debug:
        print root.ToPrettyString();
        print span;
      node_start = self.FindLeafNode(root, span[0]);
      node_close = self.FindLeafNode(root, span[1]);
      if self.debug:
        print "node_start.parent.depth=%d" % node_start.parent.depth;
        print "node_close.parent.depth=%d" % node_close.parent.depth;
      if node_start.parent.depth == node_close.parent.depth:
        if node_start.parent.start == node_close.parent.start:
          return;
        else:
          raise ValueError("same depth not same start");
      if node_start.parent.depth < node_close.parent.depth:
        if self.debug:
          print node_close.parent.arguments;
          print node_start.parent.arguments;
          print node_start.parent.ToPrettyString();
        if node_start.parent != root:
          raise ValueError("Something is wrong");
        reversed_siblings = reversed(node_close.parent.children);
        stack = []
        for node in reversed_siblings:
          stack.append(node);
          if node == node_close: break;
        for node in stack: node_close.parent.children.remove(node);
        self.MoveUpToNode(node_close.parent.parent, stack, node_start);
        if self.debug:
          print node_start.parent.ToPrettyString();
      else:
        if node_close.parent != root:
          raise ValueError("Don't know how to deal with this");
        if self.debug:
          print node_start.parent.ToString();
          print node_close.parent.ToString();
        reversed_siblings = reversed(node_close.parent.children);
        # We find the close marker first, 
        for node in reversed_siblings:
          if node != node_close:
            continue;
          else:
            break;
        # Now we add node_close to stack first;
        stack = [node_close];
        node_to_append = None;
        for node in reversed_siblings:
          if self.IsAfter(node, span[0]):
            stack.append(node);
          else:
            node_to_append = node;
            break;
        if self.debug: print stack;
        # Now remove the node from the original place so that
        # we don't end up with duplicates.
        for node in stack: node_close.parent.children.remove(node);
        # Now, we need to move these left over node to the right
        # place, the only problem is to make sure that we 
        self.PushDownToNode(node_to_append, stack, node_start);


  def __call__(self, root, tkns):
    """First thing we do is to figure out how mismatched is the text
    at token level. For now, we only deal with sentence that has at
    most one mismatched pairs.
    Return true if we successfully nomalize the pairs. Otherwise, we
    return false, in which case, the subsequent process can choose to
    ignore these sentence"""
    sink = [];
    self.pair_finder.FindFromTokens(tkns, sink);
    no_starting = [];
    no_closeing = [];
    for span in sink:
      if span[0] < 0: no_starting.append(span);
      if span[1] > len(tkns): no_closeing.append(span);
    if len(no_starting) > 1 or len(no_closeing) > 1:
      print u" ".join(tkns);
      raise ValueError("Too many unclosed pairs"); 
    tree_no_starting = []
    tree_no_closeing = [];
    self.FindUnmatchedPairInTree(root, tree_no_starting, tree_no_closeing);
    start_flag = len(tree_no_starting) == len(no_starting);
    close_flag = len(tree_no_closeing) == len(no_closeing);
    if not (start_flag and close_flag):
      # This is part when we should try to change the bracketing so
      # that trees are balanced.
      if self.debug: print root.ToPrettyString();
      for span in sink:
        if span[0] < 0: continue;
        if span[1] >= len(tkns): continue;
        self.AlignSinglePair(root, span);
        if self.debug: print root.ToPrettyString()


class PairNormalizer(object):
  """
  This is the base class for both inside/outside pair normalizer.
  """
  def GetLabel(self, node):
    return node.tag.split("-")[0];

  def GetLabelSeq(self, children, stt, end):
    res = [];
    for n in children[stt+1:end]:
      res.append(self.GetLabel(n));
    return string.join(res, "^");

class InsidePairNormalizer(PairNormalizer):
  """
  This takes a branch, find the left and right mark of a pair, we try to find an
  single node to explain the sequence between these marks.
  """
  def __init__(self, path_finder, pair_finder):
    self.path_finder = path_finder;
    self.pair_finder = pair_finder;
    self.debug = 1;
    self.filename = "";
    self.sentence = -1;

  def FindPair(self, children):
    list = [];
    self.pair_finder.Find(children, list);
    list.sort();
    list.reverse();
    #if len(list) != 0: print list;
    for pair in list:
      if (pair[1] <= pair[0]+2): continue;
      return pair;
    return None;  

  def __call__(self, node):
    if node.children:
      if len(node.children) <= 2: return;
      if self.debug: print node.ToString();
      pair = self.FindPair(node.children);
      while pair:
        stt = pair[0];
        if stt < 0: stt = -1;
        end = pair[1];
        if end >= len(node.children): end = len(node.children);
        if self.debug:
          print "stt=%d\tend=%d" % (stt, end)
          print "children.size()=%d" % len(node.children);
        if stt + 1 == end: return;
        if self.debug:
          print node.ToString();
          print "deeal with %d-%d" % (stt, end);
        lblseq = self.GetLabelSeq(node.children, stt, end);
        lbl = self.path_finder.ExplainSequence(lblseq);
        if not lbl:
          print node.ToPrettyString()
          raise ValueError("Can't find labelseq: %s:%s:%d" % (lblseq, self.filename, self.sentence));
        if end == stt + 2: return;
        if self.debug:
          print "lbl=%s" % lbl; 
        nnode = Node(node, lbl)
        nnode.children = node.children[stt+1:end];
        node.children[stt+1:end] = [nnode];
        pair = self.FindPair(node.children);

      if self.debug:
        print node.ToString();

class OutsidePairNormalizer(PairNormalizer):
  """
  This takes a branch, find the left and right mark of a pair, we try to find an
  single node to explain the sequence including these marks. We 
  """
  def __init__(self, path_finder, pair_finder):
    self.path_finder = path_finder;
    self.pair_finder = pair_finder;
    self.debug = 1;
    self.filename = "";
    self.sentence = -1;

  def FindPair(self, children):
    """
    Return only the complete pairs, the ones with begin and end mark.
    """
    list = [];
    self.pair_finder.Find(children, list);
    list.sort();
    list.reverse();
    #if len(list) != 0: print list;
    for pair in list:
      if (pair[0] < 0 or pair[1] >= len(children)): continue;
      return pair;
    return None;    

  def Rearrange(self, node):
    """
    This re arrange the "< Lable >" sequence into something different.
    """
    nnode = Node(node, "%si" % node.tag);
    nnode.children = node.children[1:];
    node.children[1:] = [nnode];

  def __call__(self, node):
    if node.children:
      if len(node.children) <= 2: return;
      if self.debug: print node.ToString();
      pair = self.FindPair(node.children);
      while pair:
        stt = pair[0];
        end = pair[1];
        if end != stt + 2:
          print node.ToPrettyString()
          msg = "Should had collapsed already";
          raise ValueError("%s in: %s:%d" % (msg, self.filename, self.sentence));
        if stt == 0 and end == len(node.children)-1:
          self.Rearrange(node);
          return;
        lblseq = self.GetLabelSeq(node.children, stt-1, end+1);
        lbl = self.path_finder.ExplainSequence(lblseq);
        if not lbl:
          print node.ToPrettyString()
          msg = "Can't find labelseq: %s" % lblseq;
          raise ValueError("%s in: %s:%d" % (msg, self.filename, self.sentence));
        nnode = Node(node, lbl)
        nnode.children = node.children[stt:end+1];
        self.Rearrange(nnode);
        node.children[stt:end+1] = [nnode];
        pair = self.FindPair(node.children);
    

class PathBinarizer(object):
  """
  Binarize the path by using the existing shorter rules (binary/trinary).
  """
  def __init__(self, path_finder):
    self.path_finder = path_finder;
    self.GetLabel = NodeLabeler();
    self.filter=TripleFilter(NodeLabeler());

  def IsGoodTriple(self, children):
    """
    Determine whether this is a good triple.
    """
    if len(children) != 3: return False;
    node0 = children[0];
    node1 = children[1];
    node2 = children[2];
    return self.filter(node0, node1, node2);

  def Transform(self, structure, node, index, parent=None):
    """
    Taken the children in the list of node form, and structure (in list of not node form)
    it should be in, return the new chilren in the list of node form that conform to the
    structure given.
    Node is the parent node that we need to create the node,
    The structure is the list representation of the node, and children is list of Node
    that we want to impose the structure on, and index is the starting point of node we
    want to consume from the list.
    We return the new constructed node, and the number of child we consumed from children
    list. This allow us to update the index for the subsequent method call.
    """
    children = node.children;
    if len(structure) == 1:
      print children[index].ToString();
      return (children[index], 1);
    nnode = Node(parent, structure[0]);
    tot = 0;
    for struct in structure[1:]:
      tnode, count = self.Transform(struct, node, tot + index, nnode);
      tot += count;
      nnode.AddChild(tnode);
    print nnode.ToPrettyString();
    return (nnode, tot);

  def __call__(self, node):
    """
    Given the children in the list form and its supposed label, return decomposition of
    such rules (into composition of smaller rules).
    """
    if not node.children: return;
    if len(node.children) <= 2: return;
    if self.IsGoodTriple(node.children): return;
    if len(node.children) >= 8: raise ValueError("Too long to decompose");
    children = map(lambda x : [self.GetLabel(x)], node.children);
    #print "Guessing %s" % children;
    print node.ToPrettyString();
    res = self.path_finder.FindPath(children, self.GetLabel(node));
    if len(res) != 0:
      print res[0];
      tnodes, count = self.Transform(res[0][1], node, 0);
      node.children = tnodes.children;
    else:
      raise ValueError("Find no production chains to decompose for %s" % children);
    print node.ToPrettyString();

def StripXMLTag(fin):
  f = codecs.open(fin, "r", "utf-8");
  res = "";
  lcl = "";
  for l in f:
    if (l.startswith("<")): continue;
    if (l.startswith("(")):
      if (lcl.strip() != ""):
        res += lcl.strip();
        res += "\n";
      lcl = l.strip();
    else:
      lcl += " ";
      lcl += l.strip();
  if (lcl.strip() != ""):
    res += lcl.strip();
  return res;

if __name__ == '__main__':
  path = "ctb_raw"
  lst = os.listdir(path)
  parser = TreeParser()
  self_production_remove = SelfProductionRemover();
  pred_finder = PredicateFinder("cpb3.0.txt");

  markers = [u"‘", u"’", u"“", u"”", u"（", u"）", u"「", u"」", u"『", u"』", u"《", u"》", u"〈", u"〉", u"［", u"］", u"【", u"】"];
  pair_finder = StackPairFinder(markers);
  parse_rule = RulesToMapParser();
  badnodes = set();
  badnodes.add(u"(FLR (PU （) (PU （) (PU ）))");
  badnodes.add(u"(FLR (PU （) (PU （))");
  badnodes.add(u"(FLR (PU ）) (PU ）))");
  badnodes.add(u"(FLR (PU ＊) (PU ＊) (PU （) (PU （))");
  duplicate_remove = DuplicateMarkerRemover(markers, badnodes);
  marker_separate= PairMarkerSplitter(markers);
  pbannotation_check = PBAnnotationChecker();

  debug = False;
  pair_match = PairMatcher(pair_finder);
  count_pair_normalize = 0;
  count_inside_pair = 0;
  count_tot = 0;
  count_duplicates = 0;
  count_no_pb_annotations = 0;
  count_tree_duplicates = 0;
  trees_by_file = [];
  tkn2tree = {};
  rule_count = RuleCounter();
  for l in lst:
    #if l != "chtb_3095.bn": continue;
    trees_by_file.append((l, []));
    ltrees = trees_by_file[-1][1]; 
    pair_finder.filename = l;
    pbannotation_check.filename = l;
    res = StripXMLTag(path+"/"+l)
    lns = res.split("\n")
    for i in range(len(lns)):
      count_tot += 1;
      pbannotation_check.sentence = i;
      x = lns[i];
      skip = False;
      try:
        tree = parser.ParseTree(x)
      except ValueError as e:
        # Simply do nothing for now.
        print lns[i];
        print e;
        skip = True;
        
      #print tree;
      tkns = []
      tree.SetStartLevel(tkns);
      if debug:
        print l;
        print tree.ToPrettyString();
        print tree.ToString();
      # So that we donot print start/level.
      #tree.SpreadInvoke(lambda x: x.ToggleStartLevelOutput());
      #tree.SpreadInvoke(lambda x: x.ToggleArgumentOutput());
      pred_finder.AttachPredicatesToNode(l, i, tree);
      tree.InvokeSpread(duplicate_remove);
      
      tkns = []
      tree.SetStartLevel(tkns);
      try:
        tree.InvokeSpread(marker_separate);
        pair_match(tree, tkns);
        tree.SpreadInvoke(self_production_remove);
      except ValueError as e:
        count_pair_normalize += 1;
        print e;
        skip = True;

      # We only need to have on copy for each sentence.
      stkn = u" ".join(tkns);
      stre = tree.ToString();
      if not tkn2tree.has_key(stkn):
        tkn2tree[stkn] = set([stre]);
      else:
        if not stre in tkn2tree[stkn]:
          if debug:
            print "duplicate: %s" % stre;
            print "different: %s" % tkn2tree[stkn][0];
          count_tree_duplicates += 1;
        else:
          tkn2tree[stkn].add(stre);
          count_duplicates += 1;
          skip = True;

      if skip:
        ltrees.append(None);
      else:
        rule_count.Process(tree);
        ltrees.append(tree);
  print "has %d rules" % len(rule_count.rcount)

  path_finder = PathFinder();
  path_finder.InsertRules(rule_count.rcount);
  #path_finder.InsertRulesFromFile("ctb.rules.bridge");
  inside_pair_normalize = InsidePairNormalizer(path_finder, pair_finder);
  inside_pair_normalize.debug = int(sys.argv[1]);
  rule_count = RuleCounter();
  for file in trees_by_file:
    l = file[0];
    inside_pair_normalize.filename = l;
    for i in range(len(file[1])):
      inside_pair_normalize.sentence = i;
      tree = file[1][i];
      if not tree: continue;
      skip = False;
      try:
        tree.SpreadInvoke(inside_pair_normalize);
      except ValueError as e:
        print tree.ToString();
        print e;
        skip = True;
        count_inside_pair += 1;
      if skip:
        file[1][i] = None;
      else:
        file[1][i] = tree;
        rule_count.Process(tree);

  print "has %d rules" % len(rule_count.rcount)

  # Now we try the outside pair normalize.
  path_finder = PathFinder();
  path_finder.InsertRules(rule_count.rcount);
  #path_finder.InsertRulesFromFile("ctb.rules");
  outside_pair_normalize = OutsidePairNormalizer(path_finder, pair_finder);
  outside_pair_normalize.debug = int(sys.argv[1]);
  path_binarizer = PathBinarizer(path_finder);
  count_good = 0;
  count_outside_pair = 0;
  for file in trees_by_file:
    l = file[0];
    outside_pair_normalize.filename = l;
    out = codecs.open("ctb_new/" + l, mode="w", encoding="utf-8")
    for i in range(len(file[1])):
      outside_pair_normalize.sentence = i;
      tree = file[1][i];
      if not tree: continue;
      good_flag = True;
      try:
        tree.SpreadInvoke(outside_pair_normalize);
        tree.SpreadInvoke(path_binarizer);
      except ValueError as e:
        print tree.ToString();
        print e;
        good_flag = False;
        count_outside_pair += 1;
      #print tree.ToPrettyString();
      if not good_flag: continue;
      count_good += 1;
      out.write("%d\t%s" % (i, tree.ToString()))
      out.write("\n")
    out.close();

  print "count_pair_normalize # bad %d" % count_pair_normalize;
  print "count_inside_pair # bad %d" % count_inside_pair;
  print "count_outside_pair # bad %d" % count_outside_pair;
  print "count_tot = %d" % count_tot;
  print "count_duplicates=%d" % count_duplicates;
  print "count_no_pb_annotations=%s" % count_no_pb_annotations;
  print "count_good = %d" % count_good;
