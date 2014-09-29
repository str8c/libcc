#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>

typedef struct {
    uint8_t type, reg;
    uint16_t last_use;
} VAR;

typedef struct {
    uint8_t op, args[7];
    uint64_t constant;
} INSTRUCTION;

typedef struct {
    char name[16];
    uint8_t args, vars, ret_type, unused;
    uint16_t code_length, constants;
    INSTRUCTION *code;
    VAR var[8];
} FUNC;

enum type {
    BOOL, CHAR, INT, LONG, SHORT,
    UCHAR, UINT, ULONG, USHORT, VOID,
};

static const char *type_name[] = {
    "bool", "char", "int", "long", "short",
    "uchar", "uint", "ulong", "ushort", "void",
};

static const uint8_t type_size[] = {
    1, 1, 4, 8, 2, 1, 4, 8, 2, 1,
};

enum keywords {
    BREAK, CONTINUE, DO, RETURN, WHILE,
};

static const char *keyword[] = {
    "break", "continue", "do", "return", "while",
};

enum {
    SET,
    SET_ADD,
    SET_SUB,
    SET_MUL,
    SET_MOD,
    SET_DIV,
    SET_RSHIFT,
    SET_LSHIFT,
    SET_XOR,
    SET_OR,
    SET_AND,
    INC,
    DEC,

    //(separate, use same enum)
    RET,
    RET_VOID,
    CALL,
};

static const char *op_set[] = {
    "=",
    "+=",
    "-=",
    "*=",
    "%=",
    "/=",
    ">>=",
    "<<=",
    "^=",
    "|=",
    "&=",
    "++",
    "--",
};

enum {
    _ZERO,
    ADD,
    SUB,
    MUL,
    MOD,
    DIV,
    RSHIFT,
    LSHIFT,
    XOR,
    OR,
    AND,
    OR_LOGICAL,
    AND_LOGICAL,
    GT,
    GTE,
    LT,
    LTE,
    EQ,
    NEQ,
    REF,
    ACCESS,
};

static const char *op_double[] = {
    "",
    "+",
    "-",
    "*",
    "%",
    "/",
    ">>",
    "<<",
    "^",
    "|",
    "&",
    "||",
    "&&",
    ">",
    ">="
    "<",
    "<=",
    "==",
    "!=",
    "->", //
    ".", //
};

/*enum {
    NOT,
    NOT_LOGICAL,
};

static const char *op_single[] = {
    "~",
    "!",
};*/

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

static int match_v(const char *name, char names[8][8], int i)
{
    if(!i) {
        return -1;
    }

    do {
        i--;
        if(!strcmp(name, names[i])) {
            return i;
        }
    } while(i);
    return -1;
}

static FUNC* func_find(FUNC *start, FUNC *end, const char *name)
{
    /* start != end */
    do {
        if(!strcmp(name, start->name)) {
            return start;
        }
    } while(++start != end);
    return NULL;
}

static int addvar(FUNC *f, char names[8][8], int nvar, const char *name, int len, uint8_t type)
{
    if(match_v(name, names, nvar) >= 0) {
        return 0;
    }

    if(len >= 8) {
        return 8;
    }

    f->var[nvar].type = type;
    f->var[nvar].reg = 0xFF;
    f->var[nvar].last_use = 0xFFFF;
    strcpy(names[nvar], name);
    nvar++;

    return nvar;
}

static char* getword(char *a)
{
    char c;
    do {
        c = *(++a);
    } while((c >= 'a' && c <= 'z') || (c >= '0' && c <= '9'));
    return a;
}

static _Bool isop(char c)
{
    return (c == '=' || c == '+' || c == '-' || c == '*' || c == '/' || c == '%' || c == '.' ||
            c == '&' || c == '|' || c == '^' || c == '<' || c == '>' || c == '!' || c == '~');
}

static char* getop(char *a)
{
    char c;
    do {
        c = *(++a);
    } while(isop(c));
    return a;
}

/* takes null terminated string with nonzero length */
FUNC* parse_main(char *b)
{
    char *a, c;
    int bracket, dec, type, len, k, op, j, ii, v;
    FUNC *functions, *f;
    INSTRUCTION *i;
    char var_names[8][8];

    bracket = 0;
    dec = 0;
    c = *b;

    if(!(functions = calloc(32, sizeof(FUNC)))) {
        return NULL;
    }

    f = functions - 1;

    do {
        if(c == '{') {
            if(dec != 4) {
                goto ERROR;
            }
            dec = 0;
            j = 0;

            goto skip;
            do {
                if(!c) {
                    goto ERROR;
                }

                /* "dec" values
                 {0->1} : var dec
                 {0->2->3->(-2)->3} : operation
                 {0->4} : function call
                 {0->3} : return
                */

                if(c == '{') {
                    bracket++;
                } else if(c == '}') {
                    if(!bracket) {
                        break;
                    }
                    bracket--;
                } else if(c == ';') {
                    if(dec > 0) {
                        goto ERROR;
                    }

                    if(dec != -1) {
                        if(i->op == SET) {
                            if(j > 4) {
                                goto ERROR;
                            }

                            if(i->args[1] < 128) {
                                f->var[i->args[1]].last_use = ii;
                            }

                            if(i->args[0] == i->args[1]) {
                                i->op = 0xFF;
                            }

                            if(j == 4) {
                                if(i->args[3] < 128) {
                                    f->var[i->args[3]].last_use = ii + 1;
                                }

                                if(i->args[2] > AND) {
                                    goto ERROR;
                                }

                                i[1].op = i->args[2];
                                i[1].args[0] = i->args[0];
                                i[1].args[1] = i->args[3];
                                i[1].constant = i->constant;
                                i++; ii++;
                            }
                        } else if(i->op <= SET_AND) {
                            if(j > 2) {
                                goto ERROR;
                            }

                            if(i->args[1] < 128) {
                                f->var[i->args[1]].last_use = ii;
                            }
                        } else if(i->op == CALL) {
                        } else if(i->op == RET) {
                            if(i->args[1] < 128) {
                                f->var[i->args[0]].last_use = ii;
                            }
                        }

                        i++; ii++;
                        j = 0;
                    }

                    dec = 0;
                } else if(c >= 'a' && c <= 'z') {
                    a = b; b = getword(b); c = *b; *b = 0;
                    len = strlen(a);
                    //printf("word: %s\n", a);

                    if(!dec) {
                        if((type = match(a, type_name)) >= 0) {
                            dec = 1;
                        } else if((k = match_v(a, var_names, v)) >= 0) {
                            i->args[j++] = k;
                            dec = 2;
                        } else if(0) {
                            //TODO(function)
                        } else if((k = match(a, keyword)) >= 0) {
                            if(k == RETURN) {
                                if(f->ret_type != VOID) {
                                    i->op = RET;
                                    dec = 3;
                                } else {
                                    i->op = RET_VOID;
                                    dec = -3;
                                }
                            } else {
                                //
                            }
                        } else {
                            goto INVALID;
                        }
                    } else if(dec == 1) {
                        v = addvar(f, var_names, v, a, len, type);
                        if(!v) {
                            goto INVALID;
                        }
                        dec = -1;
                    } else if(dec == 3) {
                        k = match_v(a, var_names, v);
                        if(k < 0) {
                            goto INVALID;
                        }

                        i->args[j++] = k;
                        dec = -2;
                    } else {
                        goto INVALID;
                    }

                    continue;
                } else if(c >= '0' && c <= '9') {
                    a = b; b = getword(b); c = *b; *b = 0;
                    len = strlen(a);
                    //printf("const: %s\n", a);

                    if(dec == 3) {
                        i->args[j++] = 128;
                        i->constant = strtol(a, NULL, 0);
                        dec = -2;
                    }
                    continue;
                } else if(isop(c)) {
                    a = b; b = getop(b); c = *b; *b = 0;
                    len = strlen(a);

                    if(dec == 2) {
                        op = match(a, op_set);
                        if(op < 0) {
                            goto INVALID;
                        }

                        i->op = op;
                        dec = 3;
                    } else if(dec == -2) {
                        op = match(a, op_double);
                        if(op < 0) {
                            goto INVALID;
                        }

                        i->args[j++] = op;
                        dec = 3;
                    } else {
                        goto INVALID;
                    }
                }

            skip:
                c = *(++b);
            } while(1);

            f->code_length = (i - f->code);
            i = realloc(f->code, f->code_length * sizeof(INSTRUCTION));
            if(i) {
                f->code = i;
            }
        } else if(c == ';') {
            if(dec != 4) {
                goto ERROR;
            }
            dec = 0;
        } else if(c == '(') {
            if(dec == 2) {
                dec = 4;
            } else {
                goto ERROR;
            }
        } else if(c == ')' || c == ',') {
            if(dec == 5) {
                dec = 4;
            } else {
                goto ERROR;
            }
        } else if(c >= 'a' && c <= 'z') {
            a = b; b = getword(b); c = *b; *b = 0;
            len = strlen(a);
            //printf("w: %s\n", a);

            if(!(dec & 3)) { //dec == 0, dec == 4
                type = match(a, type_name);
                if(type == -1) {
                    goto INVALID;
                }
            }

            if(!dec) {
                f++;
                v = 0;
                f->ret_type = type;
                i = f->code = malloc(4096 * sizeof(INSTRUCTION)); //check error, free on failure
                ii = 0;
                dec = 1;
            } else if(dec == 1) {
                if(f != functions && func_find(functions, f, a)) {
                    goto INVALID;
                }

                if(len >= sizeof(f->name)) {
                    goto INVALID;
                }

                strcpy(f->name, a);
                dec = 2;
            } else if(dec == 4) {
                if(type == VOID) {
                    if(f->args) {
                        goto INVALID;
                    }
                } else {
                    f->args++;
                    dec = 5;
                }
            } else if(dec == 5) {
                v = addvar(f, var_names, v, a, len, type);
                if(!v) {
                    goto INVALID;
                }
            }
            continue;
        }
        c = *(++b); //continue; skips this
    } while(c);

    if(dec) {
        goto ERROR;
    }

    if(!functions[0].name[0]) {
        goto ERROR;
    }

    return functions;

INVALID:
    printf("invalid (%s %s) ", a, b);
ERROR:
    printf("(error, dec=%u)\n", dec);
    free(functions);
    return NULL;
}

static void i32(uint8_t *dest, uint32_t i)
{
    memcpy(dest, &i, 4);
}

static const uint8_t reg_order[] = {
    0, 7, 6, 2, 1, 8, 9, 10, 11, 0xFF
};

static VAR* usevar(FUNC *f, uint8_t var, uint16_t *reg, uint16_t ii)
{
    VAR *v;
    const uint8_t *r;

    v = &f->var[var];
    if(ii > v->last_use) {
        printf("%u %u %u\n", var, v->last_use, ii);
        return NULL;
    }

    if(v->reg == 0xFF) {
        r = reg_order;
        while(reg[*r] >= ii && reg[*r] != 0xFFFF) {r++;}
        v->reg = *r;
        reg[*r] = v->last_use;
    }

    return v;
}

static uint8_t* prefix2(uint8_t *p, uint8_t r1, uint8_t r2)
{
    if((r1 & 8) || (r2 & 8)) {
        *p++ = 0x40 | ((r1 & 8) >> 1) | ((r2 & 8) >> 3);
    }
    return p;
}

static uint8_t combine2(uint8_t r1, uint8_t r2)
{
    return 0xC0 | ((r2 & 7) << 3) | (r1 & 7);
}

static uint8_t* op_direct(uint8_t *p, uint8_t opcode, uint8_t r1, uint8_t r2)
{
    p = prefix2(p, r1, r2);
    *p++ = opcode;
    *p++ = combine2(r1, r2);
    return p;
}

void* compile_main(FUNC *f, void (*func_out)(char*, void*))
{
    #define TODO(x) printf("TODO %u\n", x);
    uint8_t *data, *p;
    INSTRUCTION *i, *end;
    VAR *v, *v2;
    int ii, j, k;

    uint16_t reg[16];

    p = data = mmap(NULL, 65536, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_ANONYMOUS | MAP_PRIVATE, 0, 0);

    do {
        memset(reg, 0xFF, sizeof(reg));
        for(j = 0, k = 1; j != f->args; j++) {
            v = &f->var[j];
            if(v->last_use != 0xFFFF) {
                v->reg = reg_order[k++];
                reg[v->reg] = v->last_use;
            }
        }

        func_out(f->name, p);


        ii = 0; i = f->code; end = i + f->code_length;
        do {
            if(i->op == SET) {
                v = usevar(f, i->args[0], reg, ii);
                if(!v) {
                    continue;
                }

                if(i->args[1] >= 128) {
                    if(v->reg & 8) {
                        *p++ = 0x41;
                    }
                    *p++ = 0xB8 | (v->reg & 7);
                    i32(p, i->constant); p += 4;
                } else {
                    v2 = usevar(f, i->args[1], reg, ii);

                    p = op_direct(p, 0x89, v->reg, v2->reg);
                }
            } else if(i->op == RET) {
                if(i->args[0] >= 128) {
                    *p++ = 0xB8;
                    i32(p, i->constant); p += 4;
                } else {
                    v = usevar(f, i->args[0], reg, ii);

                    if(v->reg) {
                        p = op_direct(p, 0x89, 0, v->reg);
                    }
                }
                *p++ = 0xC3;
            } else if(i->op == RET_VOID) {
                *p++ = 0xC3;
            } else if(i->op == CALL) {
            } else {
                v = usevar(f, i->args[0], reg, ii);
                if(!v) {
                    continue;
                }

                if(i->args[1] >= 128) {
                    if(v->reg & 8) {
                        *p++ = 0x41;
                    }

                    if(i->op == ADD || i->op == SUB) {
                        *p++ = 0x83;
                    } else if(i->op == MUL) {
                        *p++ = 0x6B;
                    } else {
                        TODO(0);
                    }

                    *p++ = combine2(v->reg, (i->op == MUL) ? v->reg : (i->op == SUB ? 5 : 0
                                                                       ));
                    *p++ = i->constant;
                } else {
                    v2 = usevar(f, i->args[1], reg, ii);

                    if(i->op == ADD) {
                        p = op_direct(p, 0x01, v->reg, v2->reg);
                    } else if(i->op == MUL) {
                        p = prefix2(p, v->reg, v2->reg);
                        *p++ = 0x0F;
                        *p++ = 0xAF;
                        *p++ = combine2(v2->reg, v->reg);
                    } else {
                        TODO(1);
                    }
                }
            }
        } while(++ii, ++i != end);
    } while((++f)->name[0]);

    FILE *test;

    test = fopen("testasm", "wb");
    fwrite(data, p - data, 1, test);
    fclose(test);

    return data;
}

int (*test)(int);
int (*test2)(int);

void callback_func(char *name, void *ptr)
{
    printf("%s\n", name);
    if(*name == 'h') {
        test = ptr;
    } else {
        test2 = ptr;
    }
}

int main(int argc, char *argv[])
{
    FILE *file;
    int len, i;
    char *data;
    FUNC *f, *g;
    void *x;

    if(argc != 2) {
        printf("invalid arguments\n");
        return 1;
    }

    file = fopen(argv[1], "rb");
    if(!file) {
        printf("cannot open input file (%s)\n", argv[1]);
        return 1;
    }

    fseek(file, 0, SEEK_END);
    len = ftell(file);
    fseek(file, 0, SEEK_SET);

    data = malloc(len + 1);
    if(!data) {
        fclose(file);
        return 1;
    }

    data[len] = 0;
    len = fread(data, len, 1, file);
    fclose(file);

    if(len != 1) {
        return 1;
    }

    g = f = parse_main(data);
    if(!f) {
        return 1;
    }

    while(f->name[0]) {
        printf("%s %s (", type_name[f->ret_type], f->name);
        for(i = 0; i != f->args; i++) {
            printf("%s ", type_name[f->var[i].type]);
        }
        printf(");\n{\n");
        INSTRUCTION *i;
        for(i = f->code; i != f->code + f->code_length; i++) {
            printf("%u %u %u %u %u %u (%u)\n", i->op, i->args[0], i->args[1], i->args[2], i->args[3],
                   i->args[4], (int)i->constant);
        }
        printf("}\n");
        f++;
    }

    x = compile_main(g, callback_func);

    printf("%u %u %u\n", test(1), test(2), test(3));
    printf("%i %i %i\n", test2(1), test2(2), test2(3));

    //free(x);

    return 0;
}
