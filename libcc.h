/* compiles src (C code) into into dest (machine code)
    dest must be large enough (TODO: pass size of dest and make it SAFE)
    src must have non-zero length and will be modified
    cb_func() called for each (non-static) defined function, with its name and address
        cb_func() should return 0 if the function will not be needed and 1 otherwise
        note: cb_func gives a pointer to a function, but it can only be called after
            compile() has returned
    cb_link() called for each function used but not defined in the code, passing the name
        and expecting the function's address in return
    cb_data pointer is passed as the first argument in the callbacks
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

int compile(void *dest, char *src, _Bool (*cb_func)(void*, char*, void*), void* (*cb_link)(void*, char*),
            void *cb_data);
