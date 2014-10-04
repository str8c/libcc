
int hello(int a, int b, int c, int *d)
{
    int i, j, k, *p;

    i = (((a + b) * (c + b)) * ((a + c) * (c + b)));

    if(a) {
        i += b;
    }

    j = c;
    do {
        j = (j + 1);
    } while(j < 100);

    return ((*d + i) + j);
}
