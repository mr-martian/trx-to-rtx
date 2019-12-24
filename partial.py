#!/usr/bin/env python3
from lxml import etree
import sys, re

MODE = 't1x'

patterns = []
pats = {}
attrs = {}
multi_attrs = []
attr_inverse = {}

def escape(s):
    if '.' in s or ' ' in s or s == '' or s.isnumeric():
        return '"' + s + '"'
    else:
        return s

def replace_with_str(xml, _s):
    indent = '  '*(len(list(xml.iterancestors())))
    par = xml.getparent()
    if xml.getnext() == None:
        s = _s + '\n' + indent[:-2]
    else:
        s = _s + '\n' + indent
    if xml.getprevious() == None:
        if not par.text:
            par.text = '\n' + indent
        par.text += s
    else:
        prev = xml.getprevious()
        if not prev.tail:
            prev.tail = '\n' + indent
        prev.tail += s
    par.remove(xml)

def simplify_cat(cat):
    ret = []
    for op in sorted(cat, key=lambda x: len(x[0])):
        for r in ret:
            if op[0] and r[0] and op[0] != r[0]: continue
            if op[1].startswith(r[1]): break
            if r[1].startswith(op[1]):
                r[1] = op[1]
                break
        else:
            ret.append(op)
    return ret

def process_node(xml):
    global patterns, pats, attrs, multi_attrs, attr_inverse
    indent = '  '*(len(list(xml.iterancestors())) + 1)
    if xml.tag == 'def-cat':
        ls = []
        for x in xml:
            l = x.get('lemma', '')
            t = x.get('tags', '').replace('.*.*', '.*').strip('*').strip('.')
            ls.append([l, t])
        ls = simplify_cat(ls)
        if len(ls) == 1 and ls[0][1]:
            s = ls[0][1]
            if ls[0][0]:
                s = escape(ls[0][0]) + '@' + s
            pats[xml.get('n')] = s
            xml.getparent().remove(xml)
    elif xml.tag == 'section-def-attrs':
        ls = []
        for at in xml:
            name = at.attrib['n']
            vals = [v.attrib['tags'] for v in at]
            attrs[name] = vals
            ls.append('%s = %s ;' % (name, ' '.join(escape(v) for v in vals)))
        xml.clear()
        xml.text = '\n' + '\n'.join(ls) + '\n  '
        for k in attrs:
            for v in attrs[k]:
                if v in multi_attrs: continue
                for k2 in attrs:
                    if k == k2: continue
                    if v in attrs[k2]:
                        multi_attrs.append(v)
                        break
                else:
                    attr_inverse[v] = k
    elif xml.tag == 'pattern-item':
        if xml.get('n') in pats:
            replace_with_str(xml, pats[xml.get('n')])
    elif xml.tag == 'clip':
        s = xml.attrib['pos'] + '.' + xml.attrib['part']
        if 'side' in xml.attrib:
            s += '/' + xml.attrib['side']
        if 'link-to' in xml.attrib:
            s = '%' + s
        replace_with_str(xml, s)
    elif xml.tag in ['lit', 'lit-tag']:
        replace_with_str(xml, escape(xml.attrib['v']))
    elif xml.tag == 'tag':
        waslit = (xml[0].tag == 'lit-tag')
        process_node(xml[0])
        if len(xml) == 0:
            if waslit:
                rep = xml.text.strip()
                if rep[0] == '"' and rep[-1] == '"':
                    rep = rep[1:-1]
                replace_with_str(xml, rep)
            else:
                replace_with_str(xml, '[' + xml.text.strip() + ']')
    elif xml.tag == 'call-macro':
        replace_with_str(xml, '%s(%s)' % (xml.attrib['n'], ', '.join(x.attrib['pos'] for x in xml)))
    elif xml.tag == 'var':
        replace_with_str(xml, '$$' + xml.attrib['n'])
    elif xml.tag == 'lu' and MODE == 't1x' and xml[0].tag == 'var':
        replace_with_str(xml, '$$' + xml[0].attrib['n'])
    elif ((xml.tag == 'lu' and MODE == 't1x') or ((xml.tag == 'chunk') and MODE == 't2x')):
        parent_tags = []
        if MODE == 't1x':
            tgs = xml.getparent()[0].text.split('.')
            for t in tgs:
                if t[0] == '[': continue
                elif t[-1] == ']':
                    parent_tags.append(t.split('/')[0])
                elif t in attr_inverse:
                    parent_tags.append(attr_inverse[t])
                else:
                    parent_tags.append(None)
        ok = True
        parts = []
        vals = []
        linking = any('link-to' in x.attrib for x in xml)
        src = "*"
        if xml[0].tag == 'clip':
            src = xml[0].attrib['pos']
        elif xml[0].tag == 'get-case-from' and xml[0][0].tag == 'clip':
            src = xml[0][0].attrib['pos']
        for _pr in xml:
            pr = _pr
            if pr.tag == 'get-case-from':
                pr = pr[0]
                vals.append('lemcase=%s.lemcase' % _pr.get('pos'))
            if pr.tag == 'clip':
                if pr.attrib['part'] not in ['lem', 'lemh', 'lemq', 'chcontent']:
                    parts.append(pr.attrib['part'])
                if pr.get('pos') != src or pr.get('side', 'tl') != 'tl':
                    s = '{part}={pos}.{part}'.format(**pr.attrib)
                    if pr.get('side'):
                        s += '/' + pr.get('side')
                    vals.append(s)
            elif pr.tag == 'lit' and len(parts) == 0:
                vals.append('lemh=' + escape(pr.attrib['v']))
            elif pr.tag == 'lit-tag':
                if pr.attrib['v'] in attr_inverse:
                    parts.append(attr_inverse[pr.attrib['v']])
                    vals.append(attr_inverse[pr.attrib['v']] + '=' + escape(pr.attrib['v']))
                elif pr.get('v').isnumeric():
                    linking = True
                    i = int(pr.get('v')) - 1
                    if i < len(parent_tags) and parent_tags[i] != None:
                        parts.append(parent_tags[i])
                    else:
                        ok = False
                        break
                else:
                    ok = False
                    break
            else:
                ok = False
                break
        if not ok:
            if all(x.tag in ['lit', 'lit-tag', 'var'] for x in xml):
                s = ''
                for i, t in enumerate(xml):
                    if t.tag == 'lit':
                        s += t.get('v')
                        continue
                    if i > 0 and xml[i-1].tag == 'lit':
                        s += '@'
                    else:
                        s += '.'
                    if t.tag == 'var':
                        s += '[' + t.get('n') + ']'
                    else:
                        s += t.get('v')
                replace_with_str(xml, s)
            else:
                ls = [x for x in xml]
                for x in ls:
                    process_node(x)
        elif len(xml) == 1 and xml[0].tag == 'clip' and xml[0].attrib['part'] == 'whole':
            s = xml[0].attrib['pos']
            if 'side' in xml[0].attrib and xml[0].attrib['side'] != 'tl':
                s += '/' + xml[0].attrib['side']
            replace_with_str(xml, s)
        elif MODE == 't2x' and parts == ['tags'] and all(x.startswith('lem') for x in vals):
            s = src
            if vals:
                s += '[' + ', '.join(vals) + ']'
            replace_with_str(xml, s)
        else:
            n = -1
            for i, p in enumerate(patterns):
                if p == parts:
                    n = i
                    break
            else:
                n = len(patterns)
                patterns.append(parts)
            s = '%s(OP%s)' % (src, n)
            if linking:
                s = '%' + s
            if vals:
                s += '[' + ', '.join(vals) + ']'
            replace_with_str(xml, s)
    elif xml.tag == 'b':
        if 'pos' in xml.attrib:
            replace_with_str(xml, '_' + xml.attrib['pos'])
        else:
            replace_with_str(xml, '_')
    else:
        ls = [x for x in xml]
        for x in ls: process_node(x)
        if len(xml) == 0:
            lines = [x.strip() for x in (xml.text or '').strip().splitlines()]
            if xml.tag in ['and', 'or', 'equal']:
                op = xml.tag
                if op == 'equal':
                    op = '='
                if 'caseless' in xml.attrib and xml.attrib['caseless'] == 'yes':
                    op += 'cl'
                op = ' ' + op + ' '
                replace_with_str(xml, '(' + op.join(lines) + ')')
            elif xml.tag == 'not':
                replace_with_str(xml, '(not ' + xml.text.strip() + ')')
            elif xml.tag == 'tags':
                xml.text = '.'.join(lines)
            elif xml.tag == 'let':
                replace_with_str(xml, ' = '.join(lines))
            elif xml.tag == 'pattern':
                xml.text = ' '.join(lines)
            elif xml.tag == 'out':
                replace_with_str(xml, '[ ' + ' '.join(lines) + ' ]')
            elif xml.tag == 'test':
                replace_with_str(xml, xml.text.strip())
            elif xml.tag == 'when' and len(lines) == 2:
                replace_with_str(xml, 'if ' + ' '.join(lines))
            elif xml.tag == 'otherwise' and len(lines) == 1:
                replace_with_str(xml, 'else ' + lines[0])
        elif len(xml) == 1 and xml.tag == 'chunk' and MODE == 't1x':
            s = xml.attrib.get('name') or '*'
            s += '@' + xml[0].text
            ls = []
            if 'case' in xml.attrib:
                ls.append('lemcase=$$' + xml.attrib['case'])
            if 'namefrom' in xml.attrib:
                ls.append('lem=$$' + xml.attrib['namefrom'])
            if ls:
                s += ' [' + ', '.join(ls) + ']'
            s += ' { ' + ' '.join(x.strip() for x in xml[0].tail.strip().splitlines()) + ' }'
            replace_with_str(xml, s)

def clean_indent(xml):
    layer = len(list(xml.iterancestors()))
    if not xml.text or xml.text.isspace():
        if len(xml) == 0:
            xml.text = None
        else:
            xml.text = '\n  ' + '  '*layer
    if not xml.tail or xml.tail.isspace():
        if xml.getnext() == None:
            layer -= 1
        xml.tail = '\n' + '  '*layer
    for x in xml:
        clean_indent(x)

if __name__ == '__main__':
    if len(sys.argv) != 3:
        print('Usage: %s t*x_file rtx_file')
        sys.exit(1)
    xml = etree.parse(sys.argv[1], parser=etree.ETCompatXMLParser(remove_blank_text=True)).getroot()
    MODE = sys.argv[1].split('.')[-1]
    process_node(xml)
    clean_indent(xml)
    f = open(sys.argv[2], 'w')
    f.write('! Generated by %s\n! Output patterns (can probably be renamed with search and replace)\n' % ' '.join(sys.argv))
    for i, p in enumerate(patterns):
        f.write('OP%s: %s;\n' % (i, '.'.join(p)))
    f.write('\n')
    f.write(etree.tostring(xml, pretty_print=True, encoding='unicode'))
    f.close()
