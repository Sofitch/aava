#include <stdio.h>
#include <string.h>
#include <stdlib.h>

/* ========================================================== */
/* ====[              Auxiliary functions               ]==== */
/* ========================================================== */

int max_of_two(int x, int y) {
   return (x > y) ? x : y;
}

int max_of_three(int m, int n, int p) {
   return max_of_two(max_of_two(m, n), p);
}

char *strrev(char *str) {
    char *p1, *p2;
    if (! str || ! *str)
        return str;
    for (p1 = str, p2 = str + strlen(str) - 1; p2 > p1; ++p1, --p2) {
        *p1 ^= *p2;
        *p2 ^= *p1;
        *p1 ^= *p2;
    }
    return str;
}

void get_input(int* size_ptr, char** buf_ptr) {
    int i = 0, size = *size_ptr;
    char* buffer = *buf_ptr;
    char c = getchar();
  
    while (c != '\n' && c != EOF) {
        if (i + 2 > size) { /* expand buffer */
            size = size * 2;
            buffer = (char*) realloc(buffer, size);
        }

        buffer[i++] = c;
        c = getchar();
    }
    buffer[i] = '\0';

    /* update passed pointers */
    *size_ptr = size;
    *buf_ptr = buffer;
}


/* ========================================================== */
/* ====[                     Naive                      ]==== */
/* ========================================================== */

void naive_search(char* p, char* t) {
    int i, j, n, m;
    n = strlen(t);
    m = strlen(p);

    for (i = 0; i < n; i++) {
        for (j = 0; j < m && p[j] == t[i+j]; j++);
        if (j == m) printf("%d ", i);
    } /* O(n*m) ex: P -> 'aa', T -> 'aaaaaaaaa' */
    printf("\n");
}



/* ========================================================== */
/* ====[               Knuth-Morris-Pratt               ]==== */
/* ========================================================== */

void kmp_search(char* p, char* t) {
    int i, k = 0, count = 0;
    int n = strlen(t);
    int m = strlen(p);
    int* pi = (int*) malloc(sizeof(int) * m);

    /* compute pi */    
    pi[0] = 0; /* one char cannot have proper prefix */
    for (i = 1; i < m; i++) {
        while (k > 0 && p[k] != p[i]) /* no match and prefix available */
            k = pi[k-1];

        if (p[k] == p[i]) /* match -> write len of prefix */
            pi[i] = ++k; 

        else /* no prefix available */
            pi[i] = 0;
    }

    /* kmp search */
    k = 0;
    for (i = 0; i < n; i++) {
        while (k > 0 && p[k] != t[i]) { /* no match, prefix available */
            k = pi[k-1];
            count++;
        }

        if (p[k] == t[i]) /* char match */
            k++;

        if (k == m) { /* complete match */
            printf("%d ", i-(m-1));
            if (i+1 != n) {
                k = pi[k-1];
                count++;
            }
        }
    }
    count += n; /* count is len(text)+number of accesses to pi */
    printf("\n%d \n", count);

    free(pi);
}



/* ========================================================== */
/* ====[                  Boyer-Moore                   ]==== */
/* ========================================================== */

/* =========[              Preprocess              ]========= */

void bad_char_preprocess(char* p, int* r) {
    int c, ascii;
    int m = strlen(p);

    /* bad char search - compute r */ 
    for (c = 0; c < 256; c++)
        r[c] = -1;
    for (c = 0; c < m; c++) {
        ascii = (int) p[c];
        r[ascii] = c;
    }
}


void z_preprocess(char* t, int* z) {
    int i, l = 0, r = 0;
    int n = strlen(t);

    /* z search - compute z values */ 
    for (i = 1; i < n; i++) {
        if (i > r) { /* case 1 - compare starting at i */
            l = i;
            r = i;
            while (r < n && t[r] == t[r-l]) r++;
            z[i] = r - l;
            r--;
        }

        else if (z[i-l] < r-i+1) /* case 2a */
            z[i] = z[i-l];

        else { /* case 2b - compare starting at r */
            l = i;
            while (r < n && t[r] == t[r-l]) r++;
            z[i] = r - l;
            r--;
        }
    }
}



void good_suf_preprocess(char* p, int* shift) {
    int i, j, m = strlen(p), latest_l;
    char *p_rev = (char*) malloc(sizeof(char) * (m+1));
    int *z = (int*) malloc(sizeof(int) * m);
    int *n = (int*) malloc(sizeof(int) * m);

    /* good suffix search - compute shift vector */ 
    for (i = 0; i < m+1; i++) shift[i] = 0;

    /* get z values for reversed p */
    p_rev = strrev(strcpy(p_rev, p));
    z_preprocess(p_rev, z);
    
    /* get n values */
    for (j = 1; j <= m; j++)
        n[j-1] = z[m-j];

    /* ================ case 1 ================ */
    /* get L values */
    for (j = 1; j <= m - 1; j++) {
        i = m - n[j-1] + 1;
        shift[i-1] = m - j; /* shift is m - L */
    }

    /* ================ case 2 ================ */    
    /* get l values where L is 0 */
    latest_l = 0;
    for (i = 1; i < m+1; i++) {
        if (i != m && i == n[i-1]) latest_l = i; /* look for prefixes that are suffixes */
        if (shift[m-i] == 0) shift[m-i] = m - latest_l; /* shift is m - l */
    }

    /* ================ case 3 ================ */
    /* shift past char where l is 0 */
    for (i = 0; i < m+1; i++) 
        if (shift[i] == 0) shift[i] = m; 

    free(p_rev);
    free(z);
    free(n);
}


/* =========[                Search                ]========= */

void bm_search(char* p, char* t) {
    int i, delta, ascii, bc_shift, gs_shift, count = 0;
    int m = strlen(p);
    int n = strlen(t);    
    int *r = (int*) malloc(sizeof(int) * 256); /* bad char - considering ASCII chars */
    int *shift = (int*) malloc(sizeof(int) * (m+1)); /* good suf - distance p will shift if mismatch at i-1 */

    bad_char_preprocess(p, r);
    good_suf_preprocess(p, shift);

    delta = 0;
    while (m + delta <= n) {
        i = m-1;
        
        /* ============== char match ============== */
        while (i >= 0 && p[i] == t[i+delta]) {
            i--;
            count++;
        }

        /* ============ complete match ============ */
        if (i < 0) {
            printf("%d ", delta);
            delta += shift[0];
        }

        /* =============== no match =============== */
        else {
            count++;

            /* == bad character choice == */
            ascii = (int) t[i+delta]; /* realign p to mismatched char in t */
            bc_shift = i - r[ascii];
            if (bc_shift < 0) bc_shift = 1; /* do not shift backwards */

            /* === good suffix choice === */
            gs_shift = shift[i+1];
            if (gs_shift < 0) gs_shift = 1; /* do not shift backwards */

            delta += max_of_three(1, bc_shift, gs_shift);
        }
    }
    printf("\n%d \n", count);

    free(r);
    free(shift);
}



/* ========================================================== */
/* ====[                 Main Functions                 ]==== */
/* ========================================================== */

void set_text(int* buf_size_ptr, char** buf_ptr, char* text) {
    int buf_size = *buf_size_ptr, txt_size = strlen(text);
    char* buffer = *buf_ptr;
    
    if (txt_size+1 > buf_size) { /* expand buffer */
        buf_size = txt_size+1;
        buffer = (char*) realloc(buffer, buf_size);
    }
    strcpy(buffer, text);

    /* update passed pointers */
    *buf_size_ptr = buf_size;
    *buf_ptr = buffer;
}


void do_operation(int* txt_size, char** txt_ptr, char* op) {
    char* arg = op + 2;  /* string without first 2 chars */
    char* text = *txt_ptr;

    switch (op[0]) {
        case 'T':  /* set text to T */  
            set_text(txt_size, txt_ptr, arg);
            break;

        case 'N':  /* naive search for P in T */
            naive_search(arg, text);
            break;

        case 'K':  /* KMP search for P in T */
            kmp_search(arg, text);
            break;

        case 'B':  /* BM search for P in T */
            bm_search(arg, text);
            break;

        default:  /* unknown command */
            break;
    }

}


int main() {
    int op_size = 256, t_size = 256;
    char* text = (char*) malloc(sizeof(char)*t_size);
    char* op = (char*) malloc(sizeof(char)*op_size);

    get_input(&op_size, &op);
    while (op[0] != 'X') {  /* X -> exit program */
        do_operation(&t_size, &text, op);
        get_input(&op_size, &op); 
    }

    free(text);
    free(op);
    return 0;
}