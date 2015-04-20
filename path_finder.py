#!/usr/bin/python
# Copyright 2013 HIP Inc. All Rights Reserved

import copy
import math
import os
import pickle
import random
import re
import string
import Queue
import sys

class RuleCounter(object):
  """This process is used to collect the count of production rules, 
  such information can be used by path finding"""
  def __init__(self):
    self.rcount = {};

  def GetLabel(self, node):
    if node.tag.startswith("-"): return node.tag;
    tkns = node.tag.replace("=", "-").split("-");
    return tkns[0];

  def GetRule(self, node):
    symbols = [];
    symbols.append(self.GetLabel(node));
    for child in node.children:
      symbols.append(self.GetLabel(child));
    return string.join(symbols, "^");

  def Process(self, node):
    if (not node.children): return
    rule = self.GetRule(node);
    if (not self.rcount.has_key(rule)):
      self.rcount[rule] = 0;
    self.rcount[rule] += 1;
    for child in node.children:
      self.Process(child);

class ListLabeler(object):
  """
  Functor that return the normalized label for node in the list form.
  """
  def __call__(self, node):
    return node[0].replace("=", "-").split("-")[0];

class NodeLabeler(object):
  """
  Functor that return the normalized label for node the Node form.
  """
  def __call__(self, node):
    return node.tag.replace("=", "-").split("-")[0];

class TripleFilter(object):
  """
  While we want the binary rule in the end, there are some construction
  are better describe naturally with triples, it is thus useful to decide
  what triples that we want to preserve before binarization.
  The common candidates are x CC/PU y, or begin xP end.
  """
  def __init__(self, label=ListLabeler()):
    self.GetLabel = label;

  def __call__(self, node0, node1, node2):
    lbl1 = self.GetLabel(node1);
    return lbl1 == "PU" or lbl1 == "CC";


class PathFinder(object):
  """
  Given set of unary/binary production rules, try to find how can one
  produce the observed sequence.
  Throughout we use left as children seq, and right as parent. Mainly
  because that is the way we will be access the production rule.
  """
  def __init__(self):
    """
    rules is of map<string, map<string, int>>, where the first key is right
    side of production rule, the second key is left side of production rule.
    """
    self.rules = {};
    self.lognorm = {}
    self.threshold = 10;
    self.minvalue = -sys.float_info.max;
    self.filter = TripleFilter();
    self.GetLabel=ListLabeler();
    
  def ExplainSequence(self, key):
    """
    We first test whether the input label sequence exists or not.
    If yes, we return the right side of the rules.
    Otherwise, we try to figure out the best label that explains it.
    """
    if self.rules.has_key(key):
      maxcount = -1;
      maxlabel = None;
      for lkey in self.rules[key].keys():
        count = self.rules[key][lkey];
        if maxcount < count:
          maxcount = count;
          maxlabel = lkey;
      return maxlabel;
    #return None;
    # we now check we can explain this use shorter rules.
    tkns = key.split("^");
    if len(tkns) >= 8: return None;
    children = map(lambda x: [x], tkns);
    print "Guess %s" % str(children);
    res = self.FindPath(children);
    if len(res) != 0:
      print "label %s" % res[0][1][0];
      return res[0][1][0];
    else:
      return None;

  def Finalize(self):
    """
    To compute the probability of the transition, we need to compute the normalization
    factor, we store this in a separate map as log.
    """
    for key in self.rules.keys():
      count = 0;
      for lkey in self.rules[key].keys():
        count += self.rules[key][lkey];
      self.lognorm[key] = math.log(count);

  def UpdateUnaryCount(self, left_tkns, count):
    """
    We assume each label is used as is a straight through unary rule.
    """
    # For now, we only use the binary rules, but we can use k-nary rules
    # if we want to.
    #if len(left_tkns) != 2: return;
    for lbl in left_tkns:
      if not self.rules.has_key(lbl): self.rules[lbl] = {};
      if not self.rules[lbl].has_key(lbl): self.rules[lbl][lbl] = 0;
      self.rules[lbl][lbl] += count;

  def InsertRulesFromFile(self, fn):
    """
    This method load rules from file in format of "rule\tcount";
    """
    for l in open(fn):
      fields = l.strip().split("\t");
      count = int(fields[1]);
      if len(fields) != 2: raise ValueError("Can't parse the file");
      tkns = fields[0].split("^");
      tkns = map(lambda x: x.replace("=", "-").split("-")[0], tkns);
      right = tkns[0];
      left = "^".join(tkns[1:]);
      if not self.rules.has_key(left): self.rules[left] = {};
      if not self.rules[left].has_key(right): self.rules[left][right] = 0;
      self.rules[left][right] += count;
      self.UpdateUnaryCount(tkns[1:], count);
    self.Finalize();

  def InsertRules(self, rules):
    """
    We take a map from rule to it's count, and organized that info into
    left-side to right-side then count.
    """
    for key in rules.keys():
      tkns = key.split("^");
      tkns = map(lambda x: x.replace("=", "-").split("-")[0], tkns);
      right = tkns[0];
      left = "^".join(tkns[1:]);
      if not self.rules.has_key(left): self.rules[left] = {}
      if not self.rules[left].has_key(right): self.rules[left][right] = 0;
      self.rules[left][right] += rules[key];
      self.UpdateUnaryCount(tkns[1:], rules[key]);
    self.Finalize();

  def GetValue(self, left, right):
    """
    We need to make sure that both left and right are in the
    map<string, map<string, int>> before we
    call this function. return the normalized probabilities in log.
    """
    return math.log(self.rules[left][right]) - self.lognorm[left];

  def UExpand(self, node):
    """
    Given a node, return all possible parent label per unary rule and
    straight-through rule, along with their merit. The straight-through
    rule get merit of unimax.
    """
    lbl = self.GetLabel(node);
    res = [];
    maxvalue = self.minvalue;
    if self.rules.has_key(lbl):
      lmap = self.rules[lbl];
      for key in lmap.keys():
        merit = self.GetValue(lbl, key);
        if maxvalue < merit: maxvalue = merit;
        if key != lbl:
          res.append((merit, [key, node]));
        else:
          res.append((merit, node));
    res.sort();
    res.reverse();
    fres = [];
    for item in res:
       if item[0] > maxvalue - self.threshold: fres.append(item);
    return fres;

  def BExpand(self, node0, node1):
    """
    Given two nodes, enumerates all the possible label pairs along with
    their merit based on the straight-through and unary rule.
    """
    ulst0 = self.UExpand(node0);
    ulst1 = self.UExpand(node1);
    res = {};
    maxvalue = self.minvalue;
    for t0 in ulst0:
      for t1 in ulst1:
        leftside = "%s^%s" % (self.GetLabel(t0[1]), self.GetLabel(t1[1]));
        if not self.rules.has_key(leftside): continue;
        for lkey in self.rules[leftside].keys():
          merit = t0[0] + t1[0] + self.GetValue(leftside, lkey);
          if maxvalue < merit: maxvalue = merit;
          if not res.has_key(lkey): res[lkey] = [];
          res[lkey].append((merit, [lkey, t0[1], t1[1]]));
    fres = [];
    for lkey in res.keys():
      res[lkey].sort();
      res[lkey].reverse();
      item = res[lkey][0];
      if item[0] > maxvalue - self.threshold: fres.append(item);
    fres.sort();
    fres.reverse();
    return fres;

  def TriExpand(self, node0, node1, node2):
    """
    Given three nodes, enumerates all the possible label pairs along with
    their merit based on the straight-through and unary rule.
    """
    ulst0 = self.UExpand(node0);
    ulst1 = self.UExpand(node1);
    ulst2 = self.UExpand(node2);
    res = {};
    maxvalue = self.minvalue;
    for t0 in ulst0:
      lbl0 = self.GetLabel(t0[1]);
      for t1 in ulst1:
        lbl1 = self.GetLabel(t1[1]);
        for t2 in ulst2:
          leftside = "%s^%s^%s" % (lbl0, lbl1, self.GetLabel(t2[1]));
          if not self.rules.has_key(leftside): continue;
          for lkey in self.rules[leftside].keys():
            merit = t0[0] + t1[0] + t2[0] + self.GetValue(leftside, lkey);
            if maxvalue < merit: maxvalue = merit;
            if not res.has_key(lkey): res[lkey] = [];
            res[lkey].append((merit, [lkey, t0[1], t1[1], t2[1]]));
    fres = [];
    for lkey in res.keys():
      res[lkey].sort();
      res[lkey].reverse();
      item = res[lkey][0];
      if item[0] > maxvalue - self.threshold: fres.append(item);
    fres.sort();
    fres.reverse();
    return fres;

  def GetTopLabelSequence(self, children, labeler):
    return "^".join(map(lambda x: self.GetLabel(x), children));

  def Append(self, llst, cost, children, processed):
    s = str(children);
    if s in processed: return;
    processed.add(s);
    llst.put((cost, children));

  def HandleSingle(self, res, merit, nchildren, root_label):
    child_label = self.GetLabel(nchildren[0]);
    if root_label and root_label != child_label: return;
    # The final list contains the actual node instead of node list.
    res.append((merit, nchildren[0]));

  def PrintAgenda(self, llst, tag):
    res = Queue.Queue();
    count = 0;
    while not llst.empty():
      item = llst.get();
      count += 1;
      print "%s: %f %s" % (tag, item[0], item[1]);
      res.put(item);
    print "count = %d" % count;
    while not res.empty(): llst.put(res.get());

  def FindPath(self, children, root_label = None):
    """
    Find a exisitng path of short rules to explain a long rule.
    """ 
    maxlength = len(children);
    if len(children) <= 2:
      print children;
      raise ValueError("expecting longer branch");
    llst = Queue.Queue();
    processed = set();
    self.Append(llst, 0, children, processed);
    res = []
    idx = 0;
    while not llst.empty():
      idx += 1;
      if idx % 1000 == 0: print idx;
      # now we need to expand the list based on existing rules.
      (cost, children) = llst.get()
      # We now try to enumerate all possible grouping of two connected
      # nodes.
      for li in range(len(children)-1):
        combs = self.BExpand(children[li], children[li+1]);
        # This allow for the most promising tuple to pop first.
        for t in combs:
          merit = t[0] + cost;
          nchildren = children[:li];
          nchildren.append(t[1]);
          nchildren +=  children[li+2:];
          if len(nchildren) == 1:
            self.HandleSingle(res, merit, nchildren, root_label);
          else:
            self.Append(llst, merit, nchildren, processed);
      if len(children) <= 2: continue;
      for li in range(len(children)-2):
        # For now, we only deal with the triples that has a center PU/CC
        if not self.filter(children[li], children[li+1], children[li+2]): continue;
        combs = self.TriExpand(children[li], children[li+1], children[li+2]);
        # This allow for the most promising tuple to pop first.
        for t in combs:
          merit = t[0] + cost;
          nchildren = children[:li];
          nchildren.append(t[1]);
          nchildren +=  children[li+3:];
          if len(nchildren) == 1:
            self.HandleSingle(res, merit, nchildren, root_label);
          else:
            self.Append(llst, merit, nchildren, processed);        
    # now we just sort the whole things and reverse.
    res.sort()
    res.reverse()
    return res


def TestPathFinding(path_finder, rule):
  tkns = map(lambda x: [x], rule.split("^"));
  print tkns;
  res = path_finder.UExpand(tkns[1]);
  print res;
  print;
  res = path_finder.UExpand(tkns[2]);
  print res;
  print;

  print "++++Print BiExpand++++++ %s" % tkns[1:3];
  res = path_finder.BExpand(tkns[1], tkns[2]);
  for x in res[:100]: print x;

  print "++++Print TriExpand++++++ %s" % tkns[1:4];
  res = path_finder.TriExpand(tkns[1], tkns[2], tkns[3]);
  for x in res[:100]: print x;

  print "++++Print FoundPath++++++ %s" % rule;
  res = path_finder.FindPath(tkns[1:]);
  for x in res[0:20]: print x;


def TestPathFindingWithLabel(path_finder, rule, threshold=10):
  print "++++Print FoundPath with Label++++++"
  tkns = map(lambda x: [x], rule.split("^"));
  path_finder.threshold=threshold;
  res = path_finder.FindPath(tkns[1:], tkns[0][0]);
  for x in res[0:20]: print x;
  print tkns;
  if res[0][1][0] != tkns[0][0]: raise ValueError("Expecting %s" % tkns[0][0]);

if __name__ == "__main__":
  """
  This script takes two files, the first one contains all the rules dumped
  from tree bank, and the second file contains all the bridging rules.
  """
  path_finder = PathFinder();
  path_finder.InsertRulesFromFile(sys.argv[1]);
  #TestPathFinding(path_finder, "IP^NP^VP^SP");
  TestPathFinding(path_finder, "IP^NN^NR^PU^NP");
  
  TestPathFinding(path_finder, "IP^NP^LCP^NP^VP^PU");
  TestPathFindingWithLabel(path_finder, "IP^NP^LCP^NP^VP^PU");
  TestPathFindingWithLabel(path_finder, "FRAG^NN^NR^NT^NT^NN^PRN")
