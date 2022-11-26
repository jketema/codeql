typedef void FILE;
FILE *fopen(const char *path, const char *mode);
int fclose(FILE *fp);

bool function(char *pathName) {
    FILE* f = fopen(pathName, "r");
    if (!f) {
        return false;
    }

    fclose(f);
    return true;
}
