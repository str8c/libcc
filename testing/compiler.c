#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>

int compile(void *dest, char *src, bool (*cb_functions)(char*, void*), void* (*cb_linker)(char*));

int (*test)(int, int, int, int*);

bool callback_func(char *name, void *ptr)
{
    printf("callback: %s\n", name);
    test = ptr;

    return 1;
}

void* callback_link(char *name)
{
    printf("callback2: %s\n", name);
    return NULL;
}

int main(int argc, char *argv[])
{
    FILE *file;
    int len;
    char *src;
    void *exec;

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

    src = malloc(len + 1);
    if(!src) {
        fclose(file);
        return 1;
    }

    src[len] = 0;
    len = fread(src, len, 1, file);
    fclose(file);

    if(len != 1) {
        return 1;
    }

    exec = mmap(NULL, 65536, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_ANONYMOUS | MAP_PRIVATE, 0, 0);
    len = compile(exec, src, callback_func, callback_link);
    if(len < 0) {
        printf("error: %i\n", len);
        return 1;
    }

    file = fopen("test", "wb");
    fwrite(exec, len, 1, file);
    fclose(file);

    int q = 5, w = 10;
    printf("%i %i\n", test(0, 10, 50, &q), test(10, 5, 110, &w));
    //printf("%i %i %i\n", test2(1), test2(2), test2(3));

    //free(x);

    return 0;
}
