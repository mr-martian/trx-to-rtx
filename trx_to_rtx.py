#!/usr/bin/env python3
from lxml import etree
import re, copy, sys

# LIMITATIONS
# Can't always infer tag order
# Loses variable initial values
# Anything with <concat> or <append> is likely to get messed up
# Completely ignores .t3x
# Some if statements might get slightly changed (dropped conditions may change outcome)
# Nothing with case
# <mlu> probably wrong

Cats = {}
Attrs = {}
Vars = []
Lists = {}
Macros = {}
Output = set()
OutputTags = set()
LetClips = []

def indent(*parts):
    b1 = parts[0]
    b2 = parts[-1]
    rest = [x for x in parts[1:-1] if x]
    if sum(len(x) for x in rest) > 40 or any('\n' in x for x in rest):
        if b1: b1 += '\n  '
        if b2: b2 = '\n' + b2
        return b1 + '\n  '.join('\n'.join(rest).splitlines()) + b2
    else:
        return b1 + ' '.join(rest) + b2

class LU:
    tagclean = re.compile(r'\.\*(?=$|\.\*)')
    def __init__(self, lemma, tags):
        self.lemma = lemma
        self.tags = LU.tagclean.subn('', tags)[0].split('.')
    def __eq__(self, other):
        return isinstance(other, LU) and other.lemma == self.lemma and other.tags == self.tags
    def to_str(self):
        s = '.'.join(self.tags)
        if self.lemma:
            s = self.lemma + '@' + s
        return s

def read_cats(cat_section, suffix='t1x'):
    global Cats
    for cat in cat_section:
        n = cat.attrib['n']
        v = []
        for op in cat:
            lm = ''
            if 'lemma' in op.attrib:
                lm = op.attrib['lemma']
            l = LU(lm, op.attrib['tags'])
            if l not in v:
                v.append(l)
        if n in Cats:
            print('Warning: name conflict with pattern "%s"' % n)
        Cats[n] = v

def read_attrs(attr_section, suffix='t1x'):
    global Attrs
    for at in attr_section:
        n = at.attrib['n']
        v = []
        for op in at:
            if 'tags' not in op.attrib:
                print(op)
                continue
            s = op.attrib['tags']
            v.append('"'+s+'"' if '.' in s else s)
        if n in Attrs:
            print('Warning: name conflict with attr/list "%s"' % n)
        Attrs[n] = v

def read_lists(list_section, suffix='t1x'):
    global Attrs
    for at in list_section:
        n = at.attrib['n']
        v = []
        for op in at:
            s = op.attrib['v']
            v.append('"'+s+'"' if '.' in s else s)
        if n in Attrs:
            print('Warning: name conflict with attr/list "%s"' % n)
        Attrs[n] = v

def read_vars(var_section, suffix='t1x'):
    global Vars
    for v in var_section:
        Vars.append(v.attrib['n'])

class Clip:
    def __init__(self, pos, part, side='tl'):
        self.pos = pos
        self.part = part
        self.side = side
    def get_clips(self):
        if self.pos == 'list' or self.pos == 'lit' or self.pos == 'b':
            return []
        return [[self.pos, self.part]]
    def filter_out(self):
        return self
    def to_str(self):
        global LetClips
        for i in range(len(LetClips)):
            if LetClips[i][0] == [self.pos, self.part]:
                x = LetClips[i]
                LetClips[i] = [None, None]
                ret = x[1].to_str()
                LetClips[i] = x
                return ret
        if self.pos == 'list' or self.pos == 'lit':
            if '.' in self.part or ' ' in self.part:
                return '"' + self.part + '"'
            return self.part
        elif self.pos == 'var':
            return '$$' + self.part + '.lem'
        elif self.pos == 'b':
            return '_' + str(self.part)
        elif self.part == 'whole':
            return str(self.pos)
        else:
            return '%s.%s/%s' % (self.pos, self.part, self.side)

class Cond:
    def __init__(self, op, children):
        self.op = op
        self.children = children
    def get_clips(self):
        ret = []
        for c in self.children:
            ls = c.get_clips()
            ret += [l for l in ls if l not in ret]
        return ret
    def to_str(self):
        if self.op == 'not':
            return indent('(', 'not', self.children[0].to_str(), ')')
        elif self.op in ['and', 'or']:
            ls = [self.children[0].to_str()]
            for i in self.children[1:]:
                ls.append(self.op)
                ls.append(i.to_str())
            return indent('(', *ls, ')')
        else:
            return indent('(', self.children[0].to_str(), self.op, self.children[1].to_str(), ')')

class Choose:
    def __init__(self, test, do, otherwise):
        self.test = test
        self.do = do
        self.otherwise = otherwise
    def get_clips(self):
        ret = []
        for c in self.test + self.do + [self.otherwise]:
            ls = c.get_clips()
            ret += [l for l in ls if l not in ret]
        return ret
    def filter(self, clip):
        return Choose(self.test, [x.filter(clip) for x in self.do], self.otherwise.filter(clip))
    def filter_reject(self):
        ops = []
        for i, d in enumerate(self.do):
            r = d.filter_reject()
            if r == True:
                ops.append(self.test[i])
            elif isinstance(r, Cond):
                ops.append(Cond('and', [self.test[i], r]))
        r = self.otherwise.filter_reject()
        if r:
            o = Cond('not', [Cond('or', self.test)])
            if isinstance(r, Cond):
                o = Cond('and', [o, r])
            ops.append(o)
        if len(ops) > 0:
            return Cond('or', ops)
        else:
            return False
    def filter_out(self):
        return Choose(self.test, [x.filter_out() for x in self.do], self.otherwise.filter_out())
    def filter_let(self):
        return Choose(self.test, [x.filter_let() for x in self.do], self.otherwise.filter_let())
    def to_str(self):
        ls = []
        for i, d in enumerate(self.do):
            s = d.to_str()
            if s:
                ls.append(indent('', indent('if ', self.test[i].to_str(), ''), s, ''))
        s = self.otherwise.to_str()
        if s:
            ls.append('else ' + s)
        return indent('(', *ls, ')')

class ActionBlock:
    def __init__(self, parts):
        self.parts = parts
    def get_clips(self):
        ret = []
        for c in self.parts:
            ls = c.get_clips()
            ret += [l for l in ls if l not in ret]
        return ret
    def filter(self, clip):
        l = [x.filter(clip) for x in self.parts if not isinstance(x, Clip)]
        if len(l) == 1:
            return l[0]
        else:
            return ActionBlock(l)
    def filter_reject(self):
        ops = []
        for p in self.parts:
            r = p.filter_reject()
            if r == True:
                return True
            elif isinstance(r, Cond):
                ops.append(r)
        if len(ops) > 0:
            return Cond('or', ops)
        else:
            return False
    def filter_out(self):
        ls = []
        for p in self.parts:
            f = p.filter_out()
            if not isinstance(f, ActionBlock) or len(f.parts) > 0:
                ls.append(f)
        if len(ls) == 1:
            return ls[0]
        return ActionBlock(ls)
    def filter_let(self):
        ls = []
        for p in self.parts:
            if isinstance(p, Clip):
                continue
            f = p.filter_let()
            if not isinstance(f, ActionBlock) or len(f.parts) > 0:
                ls.append(f)
        if len(ls) == 1:
            return ls[0]
        return ActionBlock(ls)
    def to_str(self):
        return indent('', *[x.to_str() for x in self.parts], '').strip()

class Action:
    def __init__(self, name, parts):
        self.name = name
        self.parts = parts
        if None in self.parts:
            raise Exception('None!')
    def get_clips(self):
        if self.name == 'let':
            return self.parts[0].get_clips()
        else:
            return []
    def filter(self, clip):
        if self.name == 'let' and self.parts[0].get_clips()[0] == clip and self.parts[0].side == 'tl':
            return self
        elif self.name == 'out':
            return ActionBlock([x for x in self.parts if not isinstance(x, Clip)]).filter(clip)
        else:
            return ActionBlock([])
    def filter_reject(self):
        if self.name == 'reject-current-rule':
            return True
        else:
            return False
    def filter_out(self):
        if self.name == 'out':
            l = []
            for p in self.parts:
                if isinstance(p, Clip):
                    l.append(p)
                else:
                    l.append(p.filter_out())
            return Action(self.name, l)
        elif self.name == 'lu':
            return self
        else:
            return ActionBlock([])
    def filter_let(self):
        if self.name == 'let':
            return self
        elif self.name == 'out':
            return ActionBlock([x for x in self.parts if not isinstance(x, Clip)]).filter_let()
        else:
            return ActionBlock([])
    def to_str(self):
        if self.name == 'let':
            return self.parts[1].to_str()
        elif self.name == 'out':
            return indent('[', *[x.to_str() for x in self.parts], ']')
        elif self.name == 'lu':
            frame = '*(something)'
            ls = []
            for l in self.parts:
                if isinstance(l, Clip) and l.pos.isalnum():
                    if l.part == 'whole':
                        frame = l.pos
                    else:
                        ls.append(l.part + '=' + l.to_str() + ',')
                else:
                    ls.append('something=' + l.to_str() + ',')
            if ls:
                return indent(frame + '[', *ls, ']')
            else:
                return frame
        else:
            return ''

def parse_action(xml, adjust=None):
    if xml.tag == 'action' or xml.tag == 'def-macro':
        return ActionBlock([parse_action(x, adjust) for x in xml])
    elif xml.tag in 'and|or|not|equal|begins-with|begins-with-list|ends-with|ends-with-list|contains-substring|in'.split('|'):
        return Cond(xml.tag, [parse_action(x, adjust) for x in xml])
    elif xml.tag == 'list':
        return Clip('list', xml.attrib['n'])
    elif xml.tag == 'choose':
        ls = [parse_action(x, adjust) for x in xml]
        if ls[-1][0] == 'otherwise':
            a = [x[0] for x in ls[:-1]]
            b = [x[1] for x in ls[:-1]]
            return Choose(a, b, ls[-1][1])
        else:
            a = [x[0] for x in ls]
            b = [x[1] for x in ls]
            return Choose(a, b, ActionBlock([]))
    elif xml.tag == 'when':
        return [parse_action(xml[0][0]), ActionBlock([parse_action(x, adjust) for x in xml[1:]])]
    elif xml.tag == 'otherwise':
        return ['otherwise', ActionBlock([parse_action(x, adjust) for x in xml])]
    elif xml.tag in ['lit', 'lit-tag']:
        return Clip('lit', xml.attrib['v'])
    elif xml.tag == 'var':
        return Clip('var', xml.attrib['n'])
    elif xml.tag == 'clip':
        p = xml.attrib['pos']
        if adjust and p in adjust:
            p = adjust[p]
        s = 'tl'
        if 'side' in xml.attrib:
            s = xml.attrib['side']
        return Clip(p, xml.attrib['part'], s)
    elif xml.tag in ['let', 'out', 'reject-current-rule']:
        return Action(xml.tag, [parse_action(x, adjust) for x in xml])
    elif xml.tag == 'b':
        pos = ''
        if 'pos' in xml.attrib:
            pos = xml.attrib['pos']
            if adjust and pos in adjust:
                pos = adjust[pos]
        return Clip('b', pos)
    elif xml.tag == 'modify-case':
        return ActionBlock([]) #TODO
    elif xml.tag == 'get-case-from':
        return parse_action(xml[0], adjust) #TODO
    elif xml.tag == 'case-of':
        return Clip('lit', 'aa') #TODO
    elif xml.tag == 'chunk':
        if xml[0].tag == 'tags':
            #TODO: namefrom, case
            return ActionBlock([
                Action('let', [Clip('0', 'lem'), Clip('lit', xml.attrib['name'] if 'name' in xml.attrib else 'blah')]),
                Action('let', [Clip('0', 'pos_tag'), parse_action(xml[0][0][0], adjust)]),
                Action('out', [parse_action(x, adjust) for x in xml[1:]])
            ])
            #TODO: the rest of the tags
        else:
            return Action('out', [parse_action(x, adjust) for x in xml])
    elif xml.tag == 'concat':
        return Clip('lit', 'originally a concat instruction on line %s' % xml.sourceline)
    elif xml.tag == 'append':
        return Action('let', [Clip('var', xml.attrib['n']), Clip('lit', 'originally an append statement on line %s' % xml.sourceline)])
    elif xml.tag == 'lu':
        ls = [x for x in xml]
        i = 0
        while i < len(ls):
            if ls[i].tag == 'concat':
                ls = ls[:i] + [x for x in ls[i]] + ls[i+1:]
            else:
                i += 1
        return Action('lu', [parse_action(x, adjust) for x in ls])
    elif xml.tag == 'mlu':
        ls = []
        for x in xml:
            ls.append(parse_action(x, adjust))
            ls.append(Clip('lit', '+')) #TODO
        return ActionBlock(ls[:-1])
    elif xml.tag == 'call-macro':
        ad = {}
        if adjust:
            for k in adjust:
                ad[k] = adjust[k]
        parm = [p for p in xml if p.tag == 'with-param']
        for i, p in enumerate(parm):
            ad[str(i+1)] = p.attrib['pos']
        return parse_action(Macros[xml.attrib['n']], ad)
    else:
        print('not sure what to do with')
        print(etree.tostring(xml))

class State:
    # idea: use this to examine control flow in <choose>
    # see if they can be replaced with tag-replace rules
    def __init__(self, parts, stage='t1x'):
        # parts is e.g. [['a_cas', 'a_num'], ['a_tense']]
        # i.e. list of all clips that are used for each item
        self.input = {}
        self.lemmas = {}
        for i, p in enumerate(parts):
            self.input[i+1] = {'sl': {}, 'tl': {}, 'ref': {}}
            self.lemmas[i+1] = []
            for a in p:
                self.input[i+1]['tl'] = [[x,x] for x in Attrs[stage][a]]
                if stage == 't1x':
                    self.input[i+1]['sl'] = [[x,x] for x in Attrs[stage][a]]
                    self.input[i+1]['ref'] = [[x,x] for x in Attrs[stage][a]]
    def split(self, cond):
        if cond.op == 'not':
            yes, no = self.split(cond.children[0])
            return no, yes
        elif cond.op == 'and':
            yes = [self]
            no = []
            for c in cond.children:
                new_yes = []
                for y in yes:
                    a,b = y.split(c)
                    new_yes += a
                    no += b
                yes = new_yes
            return yes, no
        elif cond.op == 'or':
            yes = []
            no = [self]
            for c in cond.children:
                new_no = []
                for y in yes:
                    a,b = y.split(c)
                    new_no += b
                    yes += a
                no = new_no
            return yes, no
        else:
            yes = []
            no = []
            lems = ['lem', 'lemh', 'lemq', 'lemcase']
            has_lem = False
            for c in cond.children:
                if c.part in lems and c.pos != 'var':
                    if not has_lem:
                        yes = [copy.deepcopy(self)]
                        no = [copy.deepcopy(self)]
                    has_lem = True
                    yes[0].lemmas[c.pos].append(cond)
                    no[0].lemmas[c.pos].append(Cond('not', [cond]))
            if has_lem:
                return yes, no
            if cond.op == 'equal':
                pass
            elif cond.op == 'begins-with':
                pass
            elif cond.op == 'begins-with-list':
                pass
            elif cond.op == 'ends-with':
                pass
            elif cond.op == 'ends-with-list':
                pass
            elif cond.op == 'contains-substring':
                pass
            elif cond.op == 'in':
                pass

class Rule:
    def __init__(self, pat, act, line):
        self.pat = pat
        self.act = act
        self.line = line
    def to_str(self):
        print('to_str(%s)' % self.line)
        maybe_type = self.act.filter(['0', 'pos_tag'])
        if isinstance(maybe_type, Clip) and maybe_type.pos == 'lit':
            pos = maybe_type.part
        else:
            pos = 'unknown'
        global Output, OutputTags
        Output.add(pos)
        Output.update(self.pat)
        pat = []
        for p in self.pat:
            if len(Cats[p]) == 1:
                pat.append(Cats[p][0].to_str())
                Output.add(Cats[p][0].tags[0])
            else:
                pat.append(p)
                Output.add(p)
                OutputTags.add(p)
        l = self.act.filter_let()
        cl = l.get_clips()
        global LetClips
        LetClips = [(c, l.filter(c)) for c in cl]
        varls = [l for l in LetClips if l[0][0] == 'var']
        chls = [l for l in LetClips if l[0][0] == '0']
        rj = self.act.filter_reject()
        out = self.act.filter_out()
        if rj:
            rej = ' ?' + rj.to_str()
        else:
            rej = ''
        glob = ['$$' + v[0][1] + '= *(unknown)[lem=' + v[1].to_str() + ']' for v in varls] + ['$' + v[0][1] + '=' + v[1].to_str() for v in chls]
        return '! line %s\n%s -> %s%s [%s] {%s};\n\n' % (self.line, pos, ' '.join(pat), rej, ', '.join(glob), out.to_str())

def process_file(xml, stage):
    global Macros
    for x in xml:
        if x.tag == 'section-def-cats':
            read_cats(x, stage)
        elif x.tag == 'section-def-attrs':
            read_attrs(x, stage)
        elif x.tag == 'section-def-lists':
            read_lists(x, stage)
        elif x.tag == 'section-def-vars':
            read_vars(x, stage)
        elif x.tag == 'section-def-macros':
            Macros = {}
            for mc in x:
                Macros[mc.attrib['n']] = mc
        elif x.tag == 'section-rules':
            ret = []
            for r in x:
                if r.tag != 'rule':
                    continue
                ret.append(Rule([p.attrib['n'] for p in r[0]], parse_action(r[1]), r.sourceline))
            return ret

if len(sys.argv) < 3 or len(sys.argv) > 4:
    print('usage: trx_to_rtx.py t1x [t2x] rtx')
else:
    t1x = etree.parse(sys.argv[1], parser=etree.ETCompatXMLParser()).getroot()
    print('process t1x')
    rls1 = process_file(t1x, 't1x')
    print('done with t1x')
    t2x = None
    rls2 = []
    if len(sys.argv) == 4:
        print('process t2x')
        t2x = etree.parse(sys.argv[2], parser=etree.ETCompatXMLParser()).getroot()
        rls2 = process_file(t2x, 't2x')
        print('done with t2x')
    rtx = sys.argv[-1]
    r0s = []
    print('t1x')
    r1s = [r.to_str() for r in rls1]
    print('t2x')
    r2s = [r.to_str() for r in rls2]
    print('generating pattern rules')
    for k in OutputTags:
        for c in Cats[k]:
            r0s.append('%s -> %s {1};\n' % (k, c.to_str()))
    f = open(rtx, 'w')
    f.write('''! This file was automatically generated with
! $ %s
! Everything should be double-checked, particularly the following:
! - Can't always infer tag order
! - Loses variable initial values
! - Anything with <concat> or <append> is likely to get messed up
! - Completely ignores .t3x
! - Some if statements might get slightly changed (dropped conditions may change outcome)
! - Nothing has been done with case
! - <mlu> probably wrong

!!! ATTRIBUTES

%s

!!! TAG ORDER

%s

''' % (' '.join(sys.argv), '\n'.join('%s = %s ;' % (k, ' '.join(Attrs[k])) for k in Attrs), '\n'.join('%s: _;' % k for k in Output)))
    if r0s:
        f.write(''.join(r0s) + '\n\n')
    f.write('!!! Rules from %s\n\n' % sys.argv[1])
    f.write(''.join(r1s))
    if r2s:
        f.write('!!! Rules from %s\n\n' % sys.argv[2])
        f.write(''.join(r2s))
