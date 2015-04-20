#!/usr/bin/python
# -*- coding: utf-8 -*-
#


"""Script to extract sentences from Penn Treebank

"""

import os;
import sys;
import re;
import codecs;
import string;
import xml.etree.ElementTree as ET;
from StringIO import StringIO as sio;

# These words are escaped in bracket representation.
ESCAPING_MAP = {
    '(': '-LRB-',
    ')': '-RRB-',
    '{': '-LCB-',
    '}': '-RCB-',
    '/': '\\/',
    '*': '\\*',
}


# When a new leaf node is introduced, its POS tag is determined based on this
# mapping e.g. If its word is '-', its tag would be ':'. If the word is not
# in this list, its POS tag is inherited from the left node.
NEW_WORD_POS_MAP = {
    '-': ':',
    '.': '.',
    '&': 'CC',
    '/': 'CC',
}


class RulesToMapParser(object):
  def insert(self, dict, key1, key2, count):
    """Helper funciton to insert key into two level maps."""
    if not dict.has_key(key1): dict[key1] = {};
    dict[key1][key2] = count;

  def __call__(self, fn, srules):
    """Take a file contains all the rules from some treebank, and split them
    into two parts, one contains all the short rules: unary and binary, and one
    contains all the longer rules. We assume the input is in rule\tcount format,
    and rule is term seperated by ^. Output is map<string, map<string, count>>
    where the key for the first map is right side of a rule, and the key for
    the second map is left side of a rule, and count is how many time such a rule
    is observed."""
    for l in open(fn):
      tkns = l.strip().split("\t");
      if len(tkns) != 2: raise Error("Parsing Error");
      count = int(tkns[1]);
      trms = tkns[0].split("^");
      lside = trms[0];
      rside = string.join(trms[1:], "^");
      self.insert(srules, rside, lside, count);


class Argument(object):
  """Represent the argument, basically all the info in proplabel"""
  def __init__(self, frame, argtype, idx = 0):
    self.frame = frame;
    self.argtype = argtype;
    self.comtype = "";
    self.index = idx;
    self.start_level = (-1, 0);

  def __repr__(self):
    return "%d.%s %s" % (self.frame.terminal, self.frame.frameid, self.argtype);
    
class Predicate(object):
  """Represent one predicate along with all its argment"""
  def __init__(self):
    self.predicate = "";
    self.frameid = "";
    self.arguments = {};
    self.terminal = -1;

  def IsTerminalAgreed(self):
    return self.terminal == self.arguments["rel"][0].start_level[0];

  def GetArgumentInStr(self, key):
    if not self.arguments.has_key(key): raise ValueError("Can't find %s" % key);
    lst = self.arguments[key];
    argument = self.arguments[key][0];
    comtype = argument.comtype;
    spans = map(lambda x: "%d:%d" % (x.start_level[0], x.start_level[1]), lst);
    return u"%s-%s" % (comtype.join(spans), argument.argtype);

  def ToString(self):
    res = [];
    for key in self.arguments.keys():
      res.append(self.GetArgumentInStr(key));
    proplabels = " ".join(res);
    return u"%s.%s %s" % (self.predicate, self.frameid, proplabels);

class PredicateFinder(object):
  """Hold the file content for predicates from cpb, and return all the desc for
  given file and sentence."""
  def __init__(self, url):
    f = codecs.open(url, "r", "utf-8");
    self.predicates = {};
    for l in f:
      tkns = l.split(" ");
      key = " ".join(tkns[0:2]);
      if not self.predicates.has_key(key): self.predicates[key] = [];
      self.predicates[key].append(l.strip());

  def GetPredicates(self, filename, sentence_index):
    key = "%s %d" % (filename, sentence_index);
    slist = [];
    if self.predicates.has_key(key):
      slist = self.predicates[key];
    return slist;

  def AttachPredicatesToNode(self, filename, sentence_index, root):
    """This is used to attach the predicates to root, we do
    two things, the predicates is attached to only the root node,
    but the proplabels are attach to the right start/level."""
    slist = self.GetPredicates(filename, sentence_index);
    predicates = self.ParsePredicates(slist);
    root.predicates = predicates;
    for pred in predicates: root.SetPredicate(pred);

  def SplitSpan(self, s):
    res0 = s.split("*");
    res1 = [];
    for t in res0:
      res1 += t.split(",");
    return res1;
    

  def ParsePredicates(self, predicates_in_str):
    """Take a line that contains the frame, create the frame, and make
    node aware of frame so that we can adjust the """
    res = [];
    for s in predicates_in_str:
      tkns = s.split(" ");
      frame = Predicate();
      res.append(frame);
      frame.terminal = int(tkns[2]);
      pf = tkns[4].split(".");
      frame.predicate = pf[0];
      frame.frameid = pf[1];
      for tkn in tkns[6:]:
        idx = tkn.find("-");
        lbl = tkn[idx+1:];
        frame.arguments[lbl] = [];
        prop = tkn[0:idx];
        spans = [prop];
        comptype = "";
        if prop.find("*") != -1:
          comptype += "*";
        if prop.find(",") != -1:
          comptype += ",";
        if comptype != "":
          spans = self.SplitSpan(prop);
        for i in range(len(spans)):
          s = spans[i];
          argument = Argument(frame, lbl);
          try:
            span = map(lambda x: int(x), s.split(":"));
          except ValueError as e:
            print tkns;
            raise e;
          if len(span) != 2: raise ValueError("%s has wrong format" % s);
          argument.start_level = (span[0], span[1]);
          argument.comtype = comptype;
          argument.index = i;
          frame.arguments[lbl].append(argument);
    return res;

class Node(object):
  """Represents one node in a constituent tree."""

  def __init__(self, parent, tag, word=None):
    """data structure needed to store the tree structure and
    annotations from propbank. 
    For now, predicates are only available from the root node.
    But arguments is available at every node, and it also
    contains rel itself."""
    self.parent = parent
    self.tag = tag
    self.word = word
    self.children = None
    self.output_start_level = False;
    self.start = -1;
    self.level = -1;
    self.depth = 0;
    self.length = 0;
    self.arguments = [];
    self.predicates = [];
    self.output_arguments = False;
    if (self.word and self.children):
      raise Error();

  def __repr__(self):
    return ('<Node tag=%s word=%s children=%s>' %
            (repr(self.tag), repr(self.word), repr(self.children)))

  def SpreadInvoke(self, func):
    """Spead the func call to all children first, then invoke the func
    on itself."""
    if self.children:
      for x in self.children: x.SpreadInvoke(func);
    func(self);

  def ToggleStartLevelOutput(self):
    self.output_start_level = not self.output_start_level;

  def ToggleArgumentOutput(self):
    self.output_arguments = not self.output_arguments;

  def end(self):
    return self.start + self.length;

  def SetStartLevel(self, list):
    """Set the start and level for this node, it is useful for
    play with cpb annotations."""
    if self.word:
      self.start = len(list);
      self.level = 0;
      self.length = 1;
      list.append(self.word);
    else:
      res = [];
      for c in self.children:
        c.depth = self.depth + 1;
        res.append(c.SetStartLevel(list));
      self.start = res[0][0]
      self.level = res[0][1] + 1;
      tot = 0;
      for r in res:
        tot += r[2];
      self.length = tot;
    return (self.start, self.level, self.length);

  def SetPredicate(self, pred):
    """Annotate the predicate to the node so that we can preserve all the 
    predicate annotation when we are manipulate the trees"""
    if self.start == -1 or self.level == -1:
      raise ValueError("Start/Level is not annotated.");
    for key in pred.arguments.keys():
      for arg in pred.arguments[key]:
        if arg.start_level[0] == self.start and arg.start_level[1] == self.level:
          self.arguments.append(arg);
    # Now we need to call this all its children if there is any.
    if self.children:
      for child in self.children:child.SetPredicate(pred);

  def UpdatePredicate(self):
    """After one manipulate the tree, it is good idea to dump the annotation
    out with updated information. We only need to update all the arguments, 
    with its start/level, if we see a rel argument, we update the frame it
    points to so that terminal of frame get updated."""
    for arg in self.arguments:
      arg.start_level = (self.start, self.level);
      if arg.argtype == "rel":
        arg.frame.terminal = self.start;

  def InvokeSpread(self, func):
    func(self);
    if self.children:
      for x in self.children: x.InvokeSpread(func);

  def ReplaceBy(self, node):
    """This replace the payload of current node by the node specified.
    Which includes tag and word/children, along with other annotation."""
    self.arguments += node.arguments;
    self.tag = node.tag;
    if node.word:
      self.word = node.word;
      self.children = None;
    else:
      self.word = None;
      self.children = node.children;

  def ToString(self):
    """Converts the tree rooted in this node to bracket representation.

    Returns:
      For example, (NP (NN sushi))"""
    if self.word:
      items = [self.word]
    else:
      if self.children:
        items = [c.ToString() for c in self.children]
      else:
        items = []
    return '(' + ' '.join([self.tag] + items) + ')'

  def ToPrettyString(self, padding = 0):
    """Convert the tree rooted in this node in pretty printed string.
    Returns: for example (NP \t(NN sushi))"""
    sl = "";
    if self.output_start_level:
      sl = "%s%s:%d:%d|" % (sl, self.level, self.start, self.start + self.length);
    if self.output_arguments:
      largs = [];
      for arg in self.arguments:
        largs.append("%d:%s" % (arg.frame.terminal, arg.argtype));
      sl = "%s%s|" % (sl, ",".join(largs));
    if self.word:
      return "%s(%s%s\t%s)" % ("\t"*padding, sl, self.tag, self.word);
    else:
      if self.children:
        items = [c.ToPrettyString(padding+1) for c in self.children];
      else:
        items = [];
      res = '\n'.join(items);
      if len(res) != 0: res = res[padding:];
    return "%s(%s%s%s)" % ("\t"*padding, sl, self.tag, res) 

  def AddChild(self, child):
    """Adds a child node to the end."""
    if not self.children:
      self.children = []
    self.children.append(child)

  def RemoveSelf(self):
    """Removes the node from the tree."""
    self.parent.children.remove(self)
    if not self.parent.children:
      self.parent.RemoveSelf()

  def GetLeaves(self):
    """Gets all descendant leaf nodes."""
    if self.word:
      return [self]
    else:
      leaves = []
      for c in self.children:
        leaves += c.GetLeaves()
      return leaves

  def ToList(self):
    res = [];
    res.append(self.tag);
    if not self.children:
      res.append(self.word);
    else:
      for child in self.children:
        res.append(child.ToList());
    return res;

class TreeParser(object):
  """Converts tokenization of constituent tree."""

  def __init__(self):
    self.__total = 0
    self.__converted = 0
    self.__maps = {};
    self.__maps['``'] = '"'
    self.__maps['\'\''] = '"'
    self.__maps['`'] = '\''
    self.__maps['，'] = ','
    self.__maps['（'] = '-LRB-'
    self.__maps['）'] = '-RRB-'
    self.__maps['：'] = ':'
    self.__maps['、'] = ','
    self.__maps['；'] = ';'
    self.__maps['‘'] = '\''
    self.__maps['’'] = '\''
    self.__maps['“'] = '"'
    self.__maps['”'] = '"'
    self.__maps['？'] = '?'
    self.__maps['０'] = '0'
    self.__maps['１'] = '1'
    self.__maps['２'] = '2'
    self.__maps['３'] = '3'
    self.__maps['４'] = '4'
    self.__maps['５'] = '5'
    self.__maps['６'] = '6'
    self.__maps['７'] = '7'
    self.__maps['８'] = '8'
    self.__maps['９'] = '9'
    self.__maps['。'] = '.'
    self.__maps['．'] = '.'
    self.__maps['《'] = '"'
    self.__maps['》'] = '"'
    self.__maps['「'] = '"'
    self.__maps['」'] = '"'
    self.__maps['『'] = '"'
    self.__maps['』'] = '"'
    self.__maps['％'] = '%'
    self.__maps['！'] = '!'
    self.__maps['－'] = '-'
    self.__maps['〈'] = '<'
    self.__maps['〉'] = '>'
    self.__maps['——'] = '--'

  def UnicodePrint(self, lst):
    str = "";
    for tkn in lst:
      str = "%s|%s" % (str, tkn);
    return str;

  def ParseTree(self, tree_str):
    """Parses the bracket representation and returns root Node object.

    Args:
      tree_str: tree in parenthetical string format.

    Returns:
      Root node of parse tree, or None if tree is misformed (like having more
      than one root).
    """
    list_trees = self.ParseSexp(tree_str)
    assert isinstance(list_trees, list)
    if isinstance(list_trees[0], list):
      # If the input is in format ( (...)) where the root node has no label ROOT
      # or TOP or something, then add in a ROOT label.
      list_trees.insert(0, 'ROOT')
    return self.ListTreeToNodeTree(list_trees)

  def ParseSexp(self, tree_str):
    """Converts bracket representation to nested Python list.

    e.g. '( (NP (NN sushi) (NN bar)))'
      -> [['NP', ['NN', 'sushi'], ['NN', 'bar']]]
    """
    tokens = re.findall(r'\(|\)|[^\(\)\s]+', tree_str)
    root, _ = self.ParseSexpRecurse(tokens, 0)
    assert len(root) == 1
    return root[0]

  def ParseSexpRecurse(self, tokens, i):
    """Recursive part of ParseSexp().

    Parses tokens after tokens[i], and returns the parsed node and the index
    where the node ends.
    """
    nodes = []
    while i < len(tokens):
      token = tokens[i]
      i += 1
      if token == '(':
        (child, i) = self.ParseSexpRecurse(tokens, i)
        nodes.append(child)
      elif token == ')':
        return (nodes, i)
      else:
        nodes.append(token)
    return (nodes, len(tokens))

  def ListTreeToNodeTree(self, list_tree, parent=None):
    """Converts nested Python list generated by ParseSexp() to a tree of Node
    objects, and returns its root."""
    if isinstance(list_tree[0], list):
      raise ValueError("list at wrong place with :" + str(list_tree[0]));

    node = Node(parent, list_tree[0])
    is_str = isinstance(list_tree[1], str) or isinstance(list_tree[1], unicode);
    if len(list_tree) == 2 and is_str:
      node.word = list_tree[1]
    else:
      for child in list_tree[1:]:
        node.AddChild(self.ListTreeToNodeTree(child, node))
    return node
