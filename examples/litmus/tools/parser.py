#!/bin/python3
import re
import sys
import json

def get_sections(content):
    # Remove SML style comments 
    content = re.sub(r"\(\*(.|\n)*?\*\)", "", content)
    lines = []
    # Remove stuff
    for line in content.split('\n'):
        line = re.sub(r"^[A-Za-z]+=.*", "", line)
        line = re.sub(r"\s+", " ", line)
        line = re.sub(r"^\".*\"$", "", line)
        line = line.strip()
        if line:
            lines.append(line)
    content = " ".join(lines)
    content = re.sub(r"\s*=\s*", "=", content)
    content = re.sub(r"\s*;\s*", ";", content)
    content = re.sub(r"\s*\|\s*", "|", content)
    content = re.sub(r"\s+}", "}", content)
    content = re.sub(r"{\s+", "{", content)

    # Find different sections
    pattern = \
        "(?P<arch>\w+) " + \
        "(?P<name>\S+) " + \
        "{(?P<init>.*)} " + \
        "(?P<prog>(.*;)+)" + \
        "(locations ?\[(?P<locations>.*)\] ?)?" + \
        "(filter ?(?P<filter>[ \\/0-9a-zA-z:=()]*) ?)?" + \
        "(?P<final>(~exists|forall|exists).*)"
    m = re.search(pattern,content)
    if not m:
        return None
    return {'arch': m.group('arch'),
            'name': m.group('name'),
            'init': m.group('init'),
            'prog': m.group('prog'),
            'filter': m.group('filter'),
            'locations': m.group('locations'),
            'final': m.group('final')}

def fix_stmt(stmt):
    # Fixes acquire release
    stmt = re.sub("aq.rl","aqrl", stmt)
    stmt = stmt.strip()
    if stmt.startswith("lw.aq"):
        # Fix lw.aq
        m = re.search("^lw\.aq (?P<rd>\w+),0?\((?P<rs1>\w+)\)$", stmt)
        stmt = f"amoor.w.aq {m.group('rd')},zero,({m.group('rs1')})"
    elif stmt.startswith("sw.rl"):
        # Fix sw.rl
        m = re.search("^sw\.rl (?P<rs2>\w+),0?\((?P<rs1>\w+)\)$", stmt)
        stmt = f"amoswap.w.rl zero,{m.group('rs2')},({m.group('rs1')})"
    elif stmt.startswith("ld.aq"):
        # Fix ld.aq
        m = re.search("^ld\.aq (?P<rd>\w+),0?\((?P<rs1>\w+)\)$", stmt)
        stmt = f"amoor.d.aq {m.group('rd')},zero,({m.group('rs1')})"
    elif stmt.startswith("sd.rl"):
        # Fix sd.rl
        m = re.search("^sd\.rl (?P<rs2>\w+),0?\((?P<rs1>\w+)\)$", stmt)
        stmt = f"amoswap.d.rl zero,{m.group('rs2')},({m.group('rs1')})"
    return stmt

def process_prog(prog):
    # Split program into statements 
    statements = map (lambda s: s.split("|"), prog.split(';')[1:-1])
    # Transpose the statements so each program is one list
    statements = map (list, zip(*statements))
    # Fix statements
    statements = map (lambda p: map(fix_stmt,p),statements)
    # Join each program
    programs = map (lambda l: "\n".join(filter(None,l)), statements)
    # Return list of programs
    return list(programs)

def fix_form(p):
    p = re.sub("exists ?", "?", p)
    p = re.sub("forall ?", "!", p)
    p = re.sub("not ?", "~", p)
    p = re.sub(r"\s*\\/\s*", "|", p)
    return re.sub(r"\s*/\\\s*", "&", p)

def process_final(final, filter=None):
    final = fix_form(final)
    if final.startswith("~?"):
        final = f"!~({final[2:]})"
    if filter:
        filter = fix_form(filter)
        if final.startswith("?"):
            final = f"?({filter})&({final[1:]})"
        else:
            final = f"!~({filter})|({final[1:]})"
    return re.sub("\s+","",final)

def process_regs(init,n):
    # Split the init
    inits = init.split(";")

    # Keep only register assignements <tid>:<reg>=<val>
    regs = list(filter(lambda s: re.match("^\d+:\w+=\w+$", s), inits))

    # Group the register assignments by thread
    grouped_by_thread = []
    for i in range(n):
        prefix = str(i) + ":"
        # Keep only registers of thread i
        regsn = filter(lambda s: re.match(f"{prefix}\w+=\w+",s), regs)
        # Remove prefix
        regsn = list(map(lambda s: s[len(prefix):], regsn))

        grouped_by_thread.append(";".join(regsn))
    return grouped_by_thread

def process_mem(init):
    # Split the init
    inits = init.split(";")

    # Keep variable assignements <var>=<val> or <type> *<var>=&<var>
    mem = list(filter(lambda s: re.match("^\w+=\w+$", s), inits))
    decl = list(filter(lambda s: re.match("^\w+ \w$", s), inits))
    mem_ptr = list(filter(lambda s: re.match("^\w+ \*\w+=&\w+", s), inits))
    for m_ptr in mem_ptr:
        m = re.search("(?P<type>\w+) \*(?P<pvar>\w+)=&(?P<vvar>\w+)", m_ptr)
        decl.append(f"{m.group('type')} {m.group('vvar')}")
        decl.append(f"64 {m.group('pvar')}")
        mem.append(f"{m.group('pvar')}={m.group('vvar')}")
    decl = ";".join(decl)
    decl = re.sub("uint64_t", "64", decl)
    decl = re.sub("int", "32", decl)
    return [d for d in decl.split(";") if d] , mem


if __name__ == "__main__":

    # Read the litmus file
    content = sys.stdin.read()

    # Get the sections of the litmus test
    d = get_sections(content)
    if not d:
        print("No match", file=sys.stderr)
        sys.exit(1)
    # Process the program part
    d['prog'] = process_prog(d['prog'])
    # Number of threads
    d['n'] = len(d['prog'])
    # Initial value of registers per thread
    d['regs'] = process_regs(d['init'], d['n'])
    # Initial value of memory
    (d['decl'], d['mem']) = process_mem(d['init'])
    # Final condition / Postcondition
    d['final'] = process_final(d['final'], d['filter'])
    # Delete redundant fields
    del d['filter']
    del d['locations']
    del d['init']

    # Print results as JSON
    print(json.dumps(d))
