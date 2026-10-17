"""Supplementary proof-source scan that distinguishes Lean comments from code.

The kernel's transitive axiom audit remains authoritative. Keeping comments
out of this scan avoids treating ordinary prose as a proof placeholder.
"""
import re


def without_comments(source):
    output = []
    index = 0
    depth = 0
    line_comment = False
    quoted = False
    escaped = False
    while index < len(source):
        pair = source[index:index + 2]
        char = source[index]
        if depth:
            if pair == '/-':
                depth += 1
                output.append('  ')
                index += 2
                continue
            if pair == '-/':
                depth -= 1
                output.append('  ')
                index += 2
                continue
            output.append('\n' if char == '\n' else ' ')
        elif line_comment:
            output.append('\n' if char == '\n' else ' ')
            if char == '\n':
                line_comment = False
        elif quoted:
            output.append(char)
            if escaped:
                escaped = False
            elif char == '\\':
                escaped = True
            elif char == '"':
                quoted = False
        elif pair in ('/-', '--'):
            depth = int(pair == '/-')
            line_comment = pair == '--'
            output.append('  ')
            index += 2
            continue
        else:
            output.append(char)
            if char == '"':
                quoted = True
        index += 1
    assert depth == 0, 'Unterminated Lean block comment'
    return ''.join(output)


def assert_proof_source(source, path):
    code = without_comments(source)
    assert not re.search(r'\b(sorry|admit|native_decide)\b', code), path
    assert not re.search(r'^\s*(?:public |private )?axiom\s', code, re.M), path
