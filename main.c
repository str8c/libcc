#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

/* self reminders
    -pointer and temporary
    -types behaviour
 */

/* useful working macros */
#define ERROR return (-__LINE__)
#define TODO printf("TODO %u\n", __LINE__); ERROR
#define elserror else {ERROR;}

typedef struct {
    uint8_t type, pointer, var;
    char name[13];
} VARDEF;

typedef struct {
    uint8_t type, reg;
    uint16_t last_use;
} VAR;

typedef struct {
    char name[10];
    uint8_t ret_type, args;
    uint16_t var_base, code_length;
    uint8_t *code;
    VAR *var;
} FUNC;

typedef struct {
    int nconst;
    uint8_t *codep, *codestart;
    VAR *v1, *v2;
    VARDEF *vd;
    FUNC *f;
    uint64_t constant[256]; //256 * 8 = 2k
    VARDEF vardef[256]; //256 * 16 = 4k
    FUNC func[256]; //256 * 32 = 8k
    VAR var[4096]; //4096 * 4 = 16k
    uint8_t code[32768]; // 32k
} GLOBAL;

enum {
    /* take 2 variables */
    OP_ADD, OP_OR, OP_SET, OP_RET, OP_AND, OP_SUB, OP_XOR,
    OP_MUL, OP_MOD, OP_DIV, OP_RSHIFT, OP_LSHIFT,
    OP_ANDL, OP_ORL, OP_EQ, OP_NEQ, OP_GT, OP_GTE, OP_LT, OP_LTE,

    /* take 1 variable */
    OP_NOT, OP_NEG,

    /* other */
    OP_CALL, OP_CALLC,

    /* control */
    OP_JMP_IF, OP_JMP_WHILE,
    OP_LABEL_IF, OP_LABEL_LOOP_START, OP_LABEL_LOOP_END, OP_BREAK, OP_CONTINUE,
};

enum {
    CHAR, INT, LONG, SHORT, VOID,
};

static const char *type_name[] = {
    "char", "int", "long", "short", "void",
};

enum {
    STATIC, STRUCT, ENUM, TYPEDEF,
};

static const char *etc[] = {
    "static", "struct", "enum", "typedef",
};

enum {
    BREAK, CONTINUE, DO, ELSE, IF, RETURN,
};

static const char *control_name[] = {
    "break", "continue", "do", "else", "if", "return",
};

static const char *op_str[] = { /* same order as in enum */
    "+", "|", "", "", "&", "-", "^", "*", "%", "/", ">>", "<<",
    "&&", "||",  "==", "!=", ">", ">=", "<", "<=", "!",
};

/* begin x86-64 section */
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

static uint8_t usereg(uint8_t varid, VAR *var, int *tmpvar, uint16_t *reg, uint16_t i, bool read)
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

    v = &var[varid];
    if(read) {
        return v->reg;
    }

    if(i > v->last_use) {
        printf("shn %u %u %u\n", i, v->last_use, varid);
    }

    if(v->reg == 0xFF) {
        for(r = regs; reg[*r] >= i && reg[*r] != 0xFFFF; r++);
        v->reg = *r;
        reg[*r] = v->last_use;
    }

    return v->reg;
}

static int x86_64(GLOBAL *global, FUNC *f, void **out)
{
    uint8_t *p, *c, *endc, *pp;
    uint8_t op, cmd, r1, r2;
    int i, b, tmpvar;
    uint64_t constant;
    VAR *v, *var;

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

    var = global->var + f->var_base;

    for(i = 0; i != f->args; i++) {
        v = &var[i];
        if(v->last_use != 0xFFFF) {
            v->reg = regs[i];
            reg[v->reg] = v->last_use;
            //use reg regs[i]
        }
    }

    tmpvar = 0;

    p = *out;
    c = f->code;
    endc = f->code + f->code_length;
    b = 0;
    while(c < endc) {
        cmd = *c++;
        op = cmd & 0x3F;
        printf("%u\n", cmd);
        if(op == OP_JMP_IF || op == OP_JMP_WHILE) {
            c++; //assumed always eax
            *p++ = 0x83;
            *p++ = 0xF8;
            *p++ = 0x00;

            if(op == OP_JMP_IF) {
                *p++ = 0x74;
                block[b++] = p++;
            } else {
                *p++ = 0x75;
                *p = (block[--b] - (p + 1)); p++;
            }
        } else if(op == OP_LABEL_IF) {
            pp = block[--b];
            *pp = (p - (pp + 1));
        } else if(op == OP_LABEL_LOOP_START) {
            block[b++] = p;
        } else if(op == OP_LABEL_LOOP_END) {
            //continues jump to here
        } else if(op == OP_RET) {
            *p++ = 0xC3;
            c++; //assumed always eax
        } else if(op < OP_NOT) {
            r1 = usereg(*c, var, &tmpvar, reg, (c - 1) - f->code, op != OP_SET);
            c++;
            if(!(cmd & 0x40)) {
                r2 = usereg(*c, var, &tmpvar, reg, (c - 2) - f->code, 0);
            } else {
                constant = global->constant[*c];
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
            } elserror
        } elserror
    }
    if(c != endc) {
        ERROR;
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

    *out = p;
    return 0;
}
/* end x86-64 section */

/* add a constant, return its identifier */
static int toconst(GLOBAL *global, const char *word)
{
    //check limit of n
    //dont duplicate constants

    int n;

    n = global->nconst++;
    global->constant[n] = strtol(word, NULL, 0);

    return n;
}

/* find a variable definition from a name */
static VARDEF* tovardef(GLOBAL *global, const char *name)
{
    VARDEF *p, *end;

    p = global->vardef;
    end = global->vd;
    while(p != end) { //CHANGE TO DOWHILE
        if(!strcmp(p->name, name)) {
            return p;
        }
        p++;
    }

    return NULL;
}

static VARDEF* addvardef(GLOBAL *global, const char *name, uint8_t type, uint8_t pointer)
{
    VARDEF *vd;

    vd = global->vardef;
    while(vd != global->vd) { //CHANGE TO DOWHILE
        if(!strcmp(vd->name, name)) {
            return NULL;
        }
        vd++;
    }

    global->vd++; //CHECK MAX VALUE
    vd->type = type;
    vd->pointer = pointer;
    strcpy(vd->name, name); //CHECK MAX LENGTH

    return vd;
}

static FUNC* addfunc(GLOBAL *global, const char *name, uint8_t ret_type)
{
    FUNC *f;

    f = global->f++; //CHECK MAX VALUE

    f->ret_type = ret_type;
    f->var_base = global->v2 - global->var;
    f->code = global->codep;
    global->v1 = global->v2;

    strcpy(f->name, name); //CHECK MAX LENGTH

    return f;
}

static void usevar(GLOBAL *global, VARDEF *vd)
{
    VAR *v;

    v = global->v2++;
    v->type = vd->type | (vd->pointer << 5); //temporary pointer type store
    v->reg = 0xFF;

    vd->var = (v - global->v1);
}

static void commit(GLOBAL *global, uint8_t op, uint8_t a, uint8_t b)
{
    printf("code: %u %u %u\n", op, a, b);

    *global->codep++ = op;
    *global->codep++ = a;
    *global->codep++ = b;
}

static void commit2(GLOBAL *global, uint8_t op, uint8_t a)
{
    printf("code: %u %u\n", op, a);

    *global->codep++ = op;
    *global->codep++ = a;
}

static void commit3(GLOBAL *global, uint8_t op)
{
    printf("code: %u\n", op);

    *global->codep++ = op;
}

#define match(word, list) _match(word, list, sizeof(list)/sizeof(*list) - 1)
#define toetc(word) match(word, etc)
#define totype(word) match(word, type_name)
#define tocontrol(word) match(word, control_name)
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

static int opeq(char **src)
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

static int opop(char **src)
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
    } while(++i < (int)(sizeof(op_str) / sizeof(*op_str)));

    return -1;
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

static bool ignore(char ch)
{
    return (ch == ' ' || ch == '\n');
}

/* if comment, advance src to end of comment or null terminator and return 1
 * supports both C and C++ style comments
 */
static bool comment(char ch, char **srcp)
{
    char *src;

    if(ch != '/') {
        return 0;
    }

    src = *srcp;
    ch = *++(src);
    if(ch == '*') {
        do {
            ch = *++(src);
            if(!ch) {
                *srcp = src - 1;
                return 1;
            }
        } while(ch != '*' || *(src + 1) != '/');
        src++;
    } else if(ch == '/') {
        do {
            ch = *++(src);
            if(!ch) {
                *srcp = src - 1;
                return 1;
            }
        } while(ch != '\n');
    } else {
        return 0;
    }

    *srcp = src;
    return 1;
}

/* get next word in src, advancing src, setting ch and num */
///TODO: split into 2 functions, one which supports constants and one which does not
static char* word(char *chp, char **srcp, bool *nump)
{
    char ch, *src, *w;
    bool num;

    ch = *chp;
    src = *srcp;
    num = digit(ch);
    if(alpha(ch) || num) {
        w = src;
        do {
            ch = *(++src);
        } while(alnum(ch));
        *src = 0;

        *chp = ch;
        *srcp = src;
        *nump = num;
        return w;
    }

    return NULL;
}

/* parse value (code) in function func, advance src to end */
static int value(GLOBAL *global, char **srcp)
{
    char ch, *src, *w;
    uint8_t depth, tmp, op, opflags;
    int control, value;
    bool constant;

    VARDEF *vd;

    uint8_t dop[16], dpointer[16] = {0};
    uint8_t dvalue[16];

    depth = 0; tmp = 0;
    control = 0;
    src = *srcp;
    do {
        ch = *(++src);
        w = word(&ch, &src, &constant);
        if(w) {
            if(control == 0) {
                if(constant) {
                    value = toconst(global, w);
                } else if((vd = tovardef(global, w))) {
                    value = vd->var;
                    global->v1[vd->var].last_use = global->codep - global->codestart;
                } elserror

                if(!depth) {
                    *src-- = ch; *srcp = src;
                    return value | (dpointer[depth] << 9) | (constant ? 0x100 : 0);
                }

                opflags = (dpointer[depth] ? 128 : 0 | (constant) ? 64 : 0);
                dpointer[depth] = 0;

                if(!dvalue[depth]) {
                    dvalue[depth] = 1;
                    commit(global, OP_SET | opflags, tmp | 128, value);
                    control = 1;
                } else {
                    commit(global, dop[depth] | opflags, tmp | 128, value);
                    control = 2;
                }
            } elserror
        }

        if(!ch) {
            ERROR;
        }

        if(ignore(ch) || comment(ch, &src)) {
            continue;
        }

        if(control == 0) {
            if(ch == '(') {
                if(depth != 0) {
                    if(dvalue[depth]) {
                        tmp++;
                    }
                }

                depth++;
                dvalue[depth] = 0;
            } else if(ch == '*') {
                dpointer[depth] = 1;//dpointer[depth]++;
            } elserror
        } else if(ch == ')') { //control == 1 or 2
            depth--;
            if(depth == 0) {
                *srcp = src;
                return 128; //
            }

            if(!dvalue[depth]) {
                dvalue[depth] = 2;
                control = 1;
            } else if(dvalue[depth] == 1) {
            } else { //==2
                control = 2;
                commit(global, dop[depth], (tmp - 1) | 128, tmp | 128);
                tmp--;
            }
        } else if(control == 1) {
            op = opop(&src);
            if(op < 0) {
                ERROR;
            }

            dop[depth] = op;
            control = 0;
        } elserror
    } while(1);
}

/* parse code for function func, advance src to end */
static int code(GLOBAL *global, char **srcp)
{
    char ch, *src, *w;
    uint8_t pointer, lpointer, block, op;
    int control, type, lvalue, k;
    bool constant;

    VARDEF *vd;

    uint8_t blocktype[8];

    pointer = 0; lpointer = 0; block = 0;
    control = 0;
    src = *srcp;
    do {
        ch = *(++src);
        w = word(&ch, &src, &constant);
        if(w) {
            if(control == 0) {
                if((type = totype(w)) >= 0) {
                    control = 1;
                } /*else if((k = totypemod(w)) >= 0) {
                    TODO;
                } */else if((k = tocontrol(w)) >= 0) {
                    if(k == IF) {
                        *src-- = ch;
                        k = value(global, &src);
                        if(k < 0) {
                            return k;
                        }

                        commit2(global, OP_JMP_IF, k); //k always TMP0
                        blocktype[block++] = 0; control = 5;
                        continue;
                    } else if(k == ELSE) {
                        TODO;
                    } else if(k == DO) {
                        commit3(global, OP_LABEL_LOOP_START);
                        blocktype[block++] = 1; control = 5;
                    } else if(k == CONTINUE) {
                        commit3(global, OP_CONTINUE);
                    } else if(k == BREAK) {
                        commit3(global, OP_BREAK);
                    } else { //if(k == RETURN)
                        *src-- = ch;
                        k = value(global, &src);
                        if(k < 0) {
                            return k;
                        }

                        commit2(global, OP_RET, k); //k always TMP0
                        control = 4;
                        continue;
                    }
                } else if((vd = tovardef(global, w))) {
                    lvalue = vd->var; control = 3;
                } /*else if(f = tofunc(global, w)) {
                    TODO;
                } */ elserror
            } else if(control == 1) {
                if(!addvardef(global, w, type, pointer)) {
                    ERROR;
                }
                pointer = 0; control = 2;
            } else if(control == 6) {
                if(strcmp(w, "while")) {
                    ERROR;
                }

                *src-- = ch;
                k = value(global, &src);
                if(k < 0) {
                    return k;
                }

                commit2(global, OP_JMP_WHILE, k); //k always TMP0
                control = 4;
                continue;
            } else {
                printf("%u\n", control);
                ERROR;
            }
        }

        if(!ch) {
            ERROR;
        }

        if(ignore(ch) || comment(ch, &src)) {
            continue;
        }

        if(control == 0) {
            if(ch == '*') {
                src++;
                k = value(global, &src);
                if(k < 0) {
                    return k;
                }
                lvalue = k;
                lpointer = 1;
                control = 3;
            } else if(ch == '}') {
                if(!block) {
                    break;
                }
                block--;

                if(blocktype[block] == 1) {
                    commit3(global, OP_LABEL_LOOP_END);
                    control = 6;
                } else {
                    commit3(global, OP_LABEL_IF);
                }
            } elserror
        } else if(control == 1) {
            if(ch == '*') {
                pointer++;
            } elserror
        } else if(control == 2) {
            if(ch == ',') {
                control = 1;
            } else if(ch == ';') {
                control = 0;
            } elserror
        } else if(control == 3) {
            op = opeq(&src);
            if(op < 0) {
                ERROR;
            }

            k = value(global, &src);
            if(k < 0) {
                return k;
            }

            if(op == OP_SET && !lpointer) {
                usevar(global, vd);
                lvalue = vd->var;
            }

            commit(global, op | ((k >> 2) & 0xC0), lvalue | (lpointer << 8), k);
            lpointer = 0;
            control = 4;
        } else if(control == 4) {
            if(ch != ';') {
                ERROR;
            }
            control = 0;
        } else if(control == 5) {
            if(ch != '{') {
                ERROR;
            }
            control = 0;
        } elserror
    } while(1);

    *srcp = src;
    return 0;
}

int compile(void *dest, char *src, bool (*cb_func)(void*, char*, void*), void* (*cb_link)(void*, char*),
            void *cb_data)
{
    char ch, *w, *name;
    uint8_t pointer, ret_type;
    bool constant;
    int type, k, control;
    void *exec;

    VARDEF *vd, *vardef;
    FUNC *f;

    GLOBAL global_data, *global = &global_data;

    global->nconst = 0;
    global->codep = global->code;
    global->v2 = global->var;
    global->vd = global->vardef;
    global->f = global->func;

    pointer = 0;
    control = 0;
    ch = *src;
    do {
        w = word(&ch, &src, &constant);
        if(w) {
            if(control == 0) {
                if((type = totype(w)) >= 0) {
                    ret_type = type;
                    control = 1;
                } else if((k = toetc(w)) >= 0) {
                    TODO;
                } elserror
            } else if(control == 1) {
                name = w;
                control = 2;
            } else if(control == 3) {
                type = totype(w);
                if(type < 0) {
                    ERROR;
                }

                control = 4;
            } else if(control == 4) {
                vd = addvardef(global, w, type, pointer);
                if(!vd) {
                    ERROR;
                }

                usevar(global, vd);
                f->args++;

                pointer = 0;
                control = 5;
            } elserror
        }

        if(ignore(ch) || comment(ch, &src)) {
            continue;
        }

        if(control == 1 || control == 4) {
            if(ch == '*') {
                pointer++;
            } elserror
        } else if(control == 2) {
            if(ch == '(') {
                f = addfunc(global, name, ret_type);
                vardef = global->vd;
                global->codestart = f->code;
                control = 3;
            } else if(ch == ',') {
                TODO;
            } else if(ch == ';') {
                TODO;
            } elserror
        } else if(control == 5) {
            if(ch == ',') {
                control = 3;
            } else if(ch == ')') {
                control = 6;
            } elserror
        } else if(control == 6) {
            if(ch == '{') {
                k = code(global, &src);
                if(k < 0) {
                    return k;
                }
                f->code_length = global->codep - f->code;
                global->vd = vardef;
            } else if(ch == ';') {
                TODO;
            } elserror
        } elserror
    } while((ch = *(++src)));

    exec = dest;
    f = global->func;
    while(f != global->f) { //CHANGE TO DOWHILE
        printf("%s %s %u %u %p %u\n", f->name, type_name[f->ret_type], f->args, f->var_base,
               f->code, f->code_length);

        cb_func(cb_data, f->name, exec);
        k = x86_64(global, f, &exec);
        if(k < 0) {
            return k;
        }

        f++;
    }

    return (exec - dest);
}
