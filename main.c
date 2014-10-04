#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

typedef struct {
    uint8_t type, var;
    char name[14];
} VAR_DEF;

typedef struct {
    uint8_t type, reg;
    uint16_t last_use;
} VAR;

typedef struct {
    char name[16];
    uint8_t args, ret_type, arg_type[4];
    uint16_t code_length;
    uint8_t *code;
    VAR var[56];
} FUNC;

static uint8_t* x86_64(uint8_t *exec, FUNC *f, uint64_t *consts);

enum {
    CHAR, INT, LONG, SHORT, VOID,
};

static const char *type_name[] = {
    "char", "int", "long", "short", "void",
};

enum {
    STATIC
};

static const char *type_mod[] = {
    "static",
};

static const uint8_t type_size[] = {
    1, 4, 8, 2, 1,
};

enum {
    BREAK, CONTINUE, DO, ELSE, GOTO, IF, RETURN, WHILE,
};

static const char *keyword[] = {
    "break", "continue", "do", "else", "goto", "if", "return", "while",
};

enum {
    /* take 2 variables */
    OP_ADD, OP_OR, OP_SET, OP_RET, OP_AND, OP_SUB, OP_XOR,
    OP_JMP_IF, OP_MUL, OP_MOD, OP_DIV, OP_RSHIFT, OP_LSHIFT,
    OP_ANDL, OP_ORL, OP_EQ, OP_NEQ, OP_GT, OP_GTE, OP_LT, OP_LTE,

    /* take 1 variable */
    OP_NOT, OP_NEG,

    /* other */
    OP_CALL, OP_CALLC, OP_LABEL,
};

static const char *op_str[] = { /* same order as in enum */
    "+", "|", "", "", "&", "-", "^", "", "*", "%", "/", ">>", "<<",
    "&&", "||",  "==", "!=", ">", ">=", "<", "<=", "!",
};

static char* strcmpp(char *a, const char *b)
{
    while(*a && *b && *a++ == *b++);
    return a;
}

static char* strcmpb(char *a, const char *b)
{
    do {
        if(!*a || *a++ != *b++) {
            return NULL;
        }
    } while(*b);
    return a;
}

static int matchopeq(char **src)
{
    int i;
    char *r;

    i = 0;
    do {
        r = strcmpp(*src, op_str[i]);
        if(*r == '=') {
            *src = r;
            return i;
        }
    } while(++i <= OP_LSHIFT);

    return -1;
}

static int matchop(char **src)
{
    int i;
    char *r;

    i = 0;
    do {
        r = strcmpb(*src, op_str[i]);
        if(r) {
            *src = r;
            return i;
        }
    } while(++i < sizeof(op_str) / sizeof(*op_str));

    return -1;
}

#define match(word, list) _match(word, list, sizeof(list)/sizeof(*list) - 1)
static int _match(const char *word, const char **list, int i)
{
    /* i is index of last valid string in the list */
    do {
        if(!strcmp(word, list[i])) {
            return i;
        }
    } while(i--);
    return -1;
}

static FUNC* matchfunc(FUNC *start, FUNC *end, char *name)
{
    do {
        if(!strcmp(start->name, name)) {
            return start;
        }
    } while(++start != end);

    return NULL;
}

static VAR_DEF* matchvardef(VAR_DEF *start, VAR_DEF *end, char *name)
{
    if(start == end) { //remove this at some point
        return NULL;
    }

    do {
        if(!strcmp(start->name, name)) {
            return start;
        }
    } while(++start != end);

    return NULL;
}

static bool alpha(char ch)
{
    return (ch >= 'a' && ch <= 'z');
}

static bool digit(char ch)
{
    return (ch >= '0' && ch <= '9');
}

static bool alnum(char ch)
{
    return (alpha(ch) || digit(ch));
}

enum { /* "expect" values */
    GENERIC,
    OPEQ,
    OP,
    VALUE,
    VALUE2,
    VALUE_END,
    TYPE,
    NAME_DEC,
    NAME,
    NEW_BLOCK,
};

enum { /* "control" values */
    VAR_DEC,
    FUNC_DEC,
    FUNC_DEC_ARGS,
    FUNC_DEC_DONE,
    CODE,
    CODE_IF,
    CODE_DO,
    CODE_WHILE,
    CODE_RETURN,
};

//debugging macros
#define ERROR (-__LINE__)
#define TODO printf("TODO %u\n", __LINE__);

/* compiles src (C code) into into dest (machine code)
    dest must be large enough (TODO: pass size of dest and make it SAFE)
    src must have non-zero length and will be modified
    cb_function() called for each (non-static) defined function, with its name and address
        cb_function() should return 0 if the function will not be needed and 1 otherwise
        note: cb_function gives a pointer to a function, but it can only be called after
            compile() has returned
    ccb_link() called for each function used but not defined in the code, passing the name
        and expecting the function's address in return
    return value
        ( >= 0) length of machine code written into dest
        ( < 0) error code
notes:
    takes around 50-52k of stack space

    loops twice through the code: once through the plain text, generating an intermediary
        byte code, then through this byte code to convert it into machine code. This is required
        because knowledge of labels, variable lifetimes, function definitions,
        etc, requires parsing the code at least once
*/
int compile(void *dest, char *src, bool (*cb_function)(char*, void*), void* (*cb_link)(char*))
{
    char *word, ch;
    int control, expect, type, value, op, depth, block_depth, tmpvars, con;
    bool num;
    uint8_t varset, vararg, pointer_flag, opinfo_main, *codep;
    FUNC *f, *g, *h;
    VAR *v;
    VAR_DEF *vd, *vdef;
    void *exec;

    /* use stack for storage */
    VAR_DEF var_def[32];
    FUNC function[64]; //16k
    uint64_t constant[256]; //2k
    uint8_t depth_var[128], opinfo[128], blocktype[32];
    uint8_t code[32768]; //32k

    /* initialization */
    ch = *src;
    control = FUNC_DEC;
    expect = TYPE;
    g = function;
    vd = var_def;
    tmpvars = 0;
    codep = code;
    depth = -1;
    block_depth = 0;
    con = 0;
#define tmp(x) ((x) | 128)

    do {
        num = digit(ch);
        if(alpha(ch) || num) {
            word = src;
            do {
                ch = *(++src);
            } while(alnum(ch));
            *src = 0;

            switch(expect) {
            case GENERIC:
                if(num) {
                    return ERROR;
                }

                if(control != CODE) {
                    return ERROR;
                }

                type = match(word, type_name);
                if(type >= 0) {
                    control = VAR_DEC;
                    expect = NAME_DEC;
                    break;
                }

                value = match(word, keyword);
                if(value >= 0) {
                    if(value == IF) {
                        control = CODE_IF;
                        expect = VALUE;
                    } else if(value == DO) {
                        control = CODE_DO;
                        expect = NEW_BLOCK;
                    } else if(value == WHILE) {
                        control = CODE_WHILE;
                        expect = VALUE;
                    } else if(value == RETURN) {
                        control = CODE_RETURN;
                        expect = VALUE;
                    } else {
                        TODO;
                        return ERROR;
                    }
                    break;
                }

                h = matchfunc(function, g, word);
                if(h) {
                    TODO;
                    break;
                }

                vdef = matchvardef(var_def, vd, word);
                if(vdef) {
                    expect = OPEQ;
                    break;
                }

                return ERROR;
            case TYPE:
                if(num) {
                    return ERROR;
                }

                type = match(word, type_name);
                if(type < 0) {
                    value = match(word, type_mod);
                    if(value < 0) {
                        return ERROR;
                    }

                    TODO;
                } else {
                    expect = NAME_DEC;
                }
                break;
            case NAME_DEC:
                if(num) {
                    return ERROR;
                }

                if(control == VAR_DEC) {
                    vdef = matchvardef(var_def, vd, word);
                    if(vdef) {
                        return ERROR;
                    }

                    vd->type = type | pointer_flag;
                    vd->var = 0xFF;
                    strcpy(vd->name, word);//MAX LENGTH
                    vd++;

                    expect = GENERIC;
                } else if(control == FUNC_DEC) {
                    f = (function != g) ? matchfunc(function, g, word) : NULL;
                    if(!f) {
                        f = g++;
                    }

                    f->args = 0;

                    strcpy(f->name, word); //MAX LENGTH
                    f->ret_type = type | pointer_flag;
                    expect = GENERIC;
                } else if(control == FUNC_DEC_ARGS) {
                    vdef = matchvardef(var_def, vd, word);
                    if(vdef) {
                        return ERROR;
                    }

                    vd->type = type | pointer_flag;
                    vd->var = (v - f->var);
                    strcpy(vd->name, word);//MAX LENGTH
                    vd++;

                    v->type = vd->type;
                    v->reg = 0xFF;
                    v->last_use = 0xFFFF;
                    v++;

                    f->args++;
                    expect = GENERIC;
                } else {
                    return ERROR;
                }

                pointer_flag = 0;
                break;
            case VALUE:
                if(num) {
                    if(depth < 0) {
                        TODO;
                    } else if(depth_var[depth] != 0xFF) {
                        *codep++ = opinfo[depth] | 64;
                        *codep++ = tmp(tmpvars);
                        *codep++ = con;

                        constant[con++] = strtol(word, NULL, 0);

                        depth_var[depth] = 0xFF;
                        expect = VALUE_END;

                        printf("tmp %u op %u (%u);\n", tmpvars, (int)constant[con - 1], opinfo[depth]);
                    } else {
                        TODO;
                    }
                    break;
                }

                vdef = matchvardef(var_def, vd, word);
                if(vdef) {
                    if(depth < 0) {
                        vararg = vdef->var;
                        expect = VALUE_END;
                    } else if(depth_var[depth] != 0xFF) {
                        printf("tmp %u op %s (%u);\n", tmpvars, word, opinfo[depth]);

                        *codep++ = opinfo[depth];
                        *codep++ = tmp(tmpvars);
                        *codep++ = vdef->var;

                        f->var[vdef->var].last_use = (codep - f->code);
                        depth_var[depth] = 0xFF;
                        expect = VALUE_END;
                    } else {
                        printf("tmp %u = %s (%u %u);\n", tmpvars, word, vdef->var, opinfo[depth]);

                        *codep++ = OP_SET | opinfo[depth];
                        *codep++ = tmp(tmpvars);
                        *codep++ = vdef->var;

                        f->var[vdef->var].last_use = (codep - f->code);
                        opinfo[depth] = 0;
                        depth_var[depth] = tmpvars;
                        expect = OP;
                    }
                    break;
                }

                return ERROR;
            default:
                return ERROR;
            }
        }

        if(ch == ' ' || ch == '\n') {
            continue;
        }

        switch(expect) {
        case GENERIC:
            if(control == CODE) {
                if(ch == '}') {
                    if(block_depth) {
                        block_depth--;

                        if(blocktype[block_depth] == 0) {
                            *codep++ = OP_LABEL;
                            *codep++ = 0;
                        }
                    } else {
                        control = FUNC_DEC;
                        expect = TYPE;
                        f->code_length = codep - f->code;
                    }
                } else if(ch == '/') {
                    ch = *++(src);
                    if(ch == '*') {
                        do {
                            do {
                                ch = *++(src);
                                if(!ch) {
                                    return ERROR;
                                }
                            } while(ch != '*');
                        } while(*(src + 1) != '/');
                        src++;
                    } else if(ch == '/') {
                        do {
                            ch = *++(src);
                            if(!ch) {
                                return ERROR;
                            }
                        } while(ch != '\n');
                    } else {
                        return ERROR;
                    }
                } else if(ch == '*') {
                    TODO;
                }
            } else if(control == VAR_DEC) {
                if(ch == ';') {
                    control = CODE;
                } else if(ch == ',') {
                    expect = NAME_DEC;
                } else {
                    return ERROR;
                }
            } else if(control == FUNC_DEC) {
                if(ch == '(') {
                    control = FUNC_DEC_ARGS;
                    expect = TYPE;
                    v = f->var;
                    vd = var_def;
                } else {
                    return ERROR;
                }
            } else if(control == FUNC_DEC_ARGS) {
                if(ch == ',') {
                    expect = TYPE;
                } else if(ch == ')') {
                    control = FUNC_DEC_DONE;
                } else {
                    return ERROR;
                }
            } else if(control == FUNC_DEC_DONE) {
                if(ch == ';') {
                    control = FUNC_DEC;
                    expect = TYPE;
                    f->code_length = 0;
                } else if(ch == '{') {
                    f->code = codep;
                    control = CODE;
                    expect = GENERIC;
                } else {
                    return ERROR;
                }
            } else {
                return ERROR;
            }
            break;
        case NAME_DEC:
            if(ch == '*') {
                pointer_flag = 128;
            } else {
                return ERROR;
            }
            break;
        case VALUE:
            if(ch == '(') {
                if(depth >= 0) {
                    if(depth_var[depth] != 0xFF) {
                        depth_var[depth] = 0xFF;
                        tmpvars++;
                    } else {
                        depth_var[depth] = tmpvars;
                    }
                }

                depth++;
                depth_var[depth] = 0xFF;
                opinfo[depth] = 0;
            } else if(ch == '*') {
                if(depth >= 0) {
                    opinfo[depth] |= 128;
                } else {
                    opinfo_main |= 128;
                }
            } else {
                return ERROR;
            }
            break;
        case VALUE_END:
            if(ch == ')') {
                if(depth < 0) {
                    return ERROR;
                }

                depth--;
                if(depth >= 0) {
                    if(depth_var[depth] != 0xFF) {
                        expect = OP;
                    } else {
                        printf("tmp %u op tmp %u (%u)\n", tmpvars - 1, tmpvars, opinfo[depth]);
                        *codep++ = opinfo[depth];
                        *codep++ = tmp(tmpvars - 1);
                        *codep++ = tmp(tmpvars);

                        tmpvars--;
                    }
                } else if(control == CODE_IF) {
                    expect = NEW_BLOCK;
                }
            } else if(ch == ';') {
                if(depth >= 0) {
                    return ERROR;
                }

                if(control == CODE_WHILE) {
                    printf("jmp up if tmp 0\n");

                    *codep++ = OP_JMP_IF;
                    *codep++ = tmp(0);
                    *codep++ = 0;

                    control = CODE;
                } else if(control == CODE_RETURN) {
                    printf("ret tmp 0\n");
                    *codep++ = OP_RET;
                    *codep++ = tmp(0);

                    control = CODE;
                } else {
                    *codep++ = opinfo_main;
                    *codep++ = varset;

                    if(vararg != 0xFF) {
                        printf("var %u op var %u (%u)\n", varset, vararg, opinfo_main);
                        *codep++ = vararg;
                        f->var[vararg].last_use = codep - f->code;
                    } else {
                        printf("var %u op tmp 0 (%u)\n", varset, opinfo_main);
                        *codep++ = tmp(0);
                    }
                }

                expect = GENERIC;
            } else {
                return ERROR;
            }
            break;
        case OPEQ:
            op = matchopeq(&src);
            if(op < 0) {
                return ERROR;
            }

            if(op == OP_SET) {
                vdef->var = (v - f->var);
                v->type = vdef->type;
                v->reg = 0xFF;
                v->last_use = 0xFFFF;
                v++;
            }

            opinfo_main = op;

            varset = vdef->var;
            vararg = 0xFF;
            expect = VALUE;
            break;
        case OP:
            if(ch == ')') {
                if(depth != 0) {
                    return ERROR;
                }
                depth--;
                expect = VALUE_END;
                if(control == CODE_IF) {
                    expect = NEW_BLOCK;
                }
                break;
            }

            op = matchop(&src);
            if(op < 0) {
                return ERROR;
            }

            opinfo[depth] = op;

            expect = VALUE;
            break;
        case NEW_BLOCK:
            if(ch != '{') {
                return ERROR;
            }

            if(control == CODE_DO) {
                *codep++ = OP_LABEL;
                *codep++ = 1;
                blocktype[block_depth] = 1;
            } else { //if(control == CODE_IF)
                *codep++ = OP_JMP_IF;
                *codep++ = tmp(0);
                *codep++ = 1;

                blocktype[block_depth] = 0;

                printf("jmp if not tmp 0\n");
            }

            block_depth++;

            control = CODE;
            expect = GENERIC;
            break;
        default:
            return ERROR;
        }
    } while((ch = *(++src)));

    f = function;
    if(f == g) {
        return ERROR;
    }

    exec = dest;
    do {
        printf("%s %s (); (%u)\n", type_name[f->ret_type], f->name, f->args);

        cb_function(f->name, exec);
        exec = x86_64(exec, f, constant);
        if(!exec) {
            return ERROR;
        }
    } while(++f != g);


    return exec - dest;
}

static const uint8_t regs[] = {
    7, 6, 2, 1, 8, 9, 10, 11, 0xFF
};

static uint8_t* prefix2(uint8_t *p, uint8_t r1, uint8_t r2)
{
    if((r1 & 8) || (r2 & 8)) {
        *p++ = 0x40 | ((r2 & 8) >> 1) | ((r1 & 8) >> 3);
    }
    return p;
}

static uint8_t combine(uint8_t r1, uint8_t r2)
{
    return ((r2 & 7) << 3) | (r1 & 7);
}

static uint8_t combine2(uint8_t r1, uint8_t r2)
{
    return 0xC0 | combine(r1, r2);
}

static uint8_t* op_direct(uint8_t *p, uint8_t opcode, uint8_t r1, uint8_t r2)
{
    p = prefix2(p, r1, r2);
    *p++ = opcode;
    *p++ = combine2(r1, r2);
    return p;
}

static uint8_t* op_indirect(uint8_t *p, uint8_t opcode, uint8_t r1, uint8_t r2, int8_t offset)
{
    p = prefix2(p, r1, r2);
    *p++ = opcode;
    *p = combine(r1, r2);
    if(offset) {
        *p++ |= 0x40;
        *p = offset;
    }
    p++;
    return p;
}

static uint8_t usevar(uint8_t varid, FUNC *f, int *tmpvar, uint16_t *reg, uint16_t i, bool read)
{
    VAR *v;
    int j;
    const uint8_t *r;
    uint8_t ret, tmp;
    uint16_t *p;

    if(varid & 128) {
        varid &= 0x7F;
        ret = 0xFF;
        for(p = reg, j = *tmpvar; j && j >= varid; p++) {
            if(*p != 0xFFFF && (*p & 0xFF00)) {
                tmp = *p;
                if(tmp > varid) {
                    *p = 0xFFFF; j--;
                } else if(tmp == varid) {
                    ret = (p - reg); j--;
                }
            }

            if(p - reg >= 16) {
                printf("snh 2\n");
            }
        }

        if(!varid) {
            *tmpvar = 0;
            return 0;
        }

        *tmpvar = j + 1;

        if(ret == 0xFF) {
            if(read) {
                printf("snh 1\n");
            }

            for(r = regs; reg[*r] >= i && reg[*r] != 0xFFFF; r++);
            ret = *r;
            reg[*r] = 0xFF00 | varid;
        }
        return ret;
    }

    v = &f->var[varid];
    if(read) {
        return v->reg;
    }

    if(i > v->last_use) {
        printf("shn %u %u\n", i, v->last_use);
    }

    if(v->reg == 0xFF) {
        for(r = regs; reg[*r] >= i && reg[*r] != 0xFFFF; r++);
        v->reg = *r;
        reg[*r] = v->last_use;
    }

    return v->reg;
}

static uint8_t* x86_64(uint8_t *p, FUNC *f, uint64_t *consts)
{
    uint8_t *c, *endc, *pp;
    uint8_t cmd, op, r1, r2;
    int i, b, tmpvar;
    uint64_t constant;
    VAR *v;

    uint16_t reg[16];
    uint8_t *block[16];

    memset(reg, 0xFF, sizeof(reg));

    /* push saved registers so that they can be used in the function */
    /*
    *exec++ = 0x53;
    *exec++ = 0x55;
    *exec++ = 0x41; *exec++ = 0x54;
    *exec++ = 0x41; *exec++ = 0x55;
    *exec++ = 0x41; *exec++ = 0x56;
    *exec++ = 0x41; *exec++ = 0x57;
    */

    for(i = 0; i != f->args; i++) {
        v = &f->var[i];
        if(v->last_use != 0xFFFF) {
            v->reg = regs[i];
            reg[v->reg] = v->last_use;
            //use reg regs[i]
        }
    }

    tmpvar = 0;

    c = f->code;
    endc = f->code + f->code_length;
    b = 0;
    while(c < endc) {
        cmd = *c++;
        op = cmd & 0x3F;
        //printf("op\n");
        if(op == OP_JMP_IF) {
            //v = usevar(*c, f, tmpvar, reg, (c + 1) - f->code);
            c++;
            *p++ = 0x83;
            *p++ = 0xF8;
            *p++ = 0x00;

            if(*c++) {
                *p++ = 0x74;
                block[b++] = p++;
            } else {
                *p++ = 0x75;
                *p = (block[--b] - (p + 1)); p++;
            }
        } else if(op == OP_LABEL) {
            if(*c++) {
                block[b++] = p;
            } else {
                pp = block[--b];
                *pp = (p - (pp + 1));
            }
        } else if(op == OP_RET) {
            *p++ = 0xC3;
            c++;
        } else if(op < OP_NOT) {
            r1 = usevar(*c, f, &tmpvar, reg, (c + 1) - f->code, op != OP_SET);
            c++;
            if(!(cmd & 0x40)) {
                r2 = usevar(*c, f, &tmpvar, reg, (c + 1) - f->code, 0);
            } else {
                constant = consts[*c];
            }
            c++;

            if(op == OP_SET) {
                if(!(cmd & 0xC0)) {
                    p = op_direct(p, 0x89, r1, r2);
                } else if(cmd & 128) {
                    p = op_indirect(p, 0x8B, r2, r1, 0);
                } else {
                    TODO;
                }
            } else if(op <= OP_XOR) {
                if(!(cmd & 0xC0)) {
                    p = op_direct(p, (op << 3) | 1, r1, r2);
                } else if(cmd & 128) {
                    TODO;
                } else {
                    *p++ = 0x83;
                    *p++ = combine2(r1, op);
                    *p++ = constant;
                }
            } else if(op == OP_MUL) {
                if(!(cmd & 0xC0)) {
                    p = prefix2(p, r2, r1);
                    *p++ = 0x0F;
                    *p++ = 0xAF;
                    *p++ = combine2(r2, r1);
                } else if(cmd & 128) {
                    TODO;
                } else {
                    TODO;
                }
            } else if(op == OP_ANDL || op == OP_ORL) {
                TODO;
            } else if(op >= OP_EQ) {
                if(!(cmd & 0xC0)) {
                    TODO;
                } else if(cmd & 128) {
                    TODO;
                } else {
                    *p++ = 0x83;
                    *p++ = combine2(r1, 7);
                    *p++ = constant;

                    if(op != OP_LT) {
                        TODO;
                    }

                    if(r1 >= 4) {
                        if(r1 >= 8) {
                            *p++ = 0x41;
                        } else {
                            *p++ = 0x40;
                        }
                    }

                    *p++ = 0x0F;
                    *p++ = 0x9C; //compare op
                    *p++ = combine2(0, r1);

                    //extend
                    *p++ = 0x0F;
                    *p++ = 0xB6;
                    *p++ = combine2(0, r1);
                }
            } else {
                printf("%u\n", op);
                return NULL;
            }
        } else {
            printf("i dont know %u\n", op);
            return NULL;
        }
    }
    if(c != endc) {
        printf("%p %p\n", c, endc);
        return NULL;
    }

    /* pop */
    /*
    *exec++ = 0x5B;
    *exec++ = 0x5D;
    *exec++ = 0x41; *exec++ = 0x5C;
    *exec++ = 0x41; *exec++ = 0x5D;
    *exec++ = 0x41; *exec++ = 0x5E;
    *exec++ = 0x41; *exec++ = 0x5F;
    */

    return p;
}
