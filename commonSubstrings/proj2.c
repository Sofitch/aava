#include <stdio.h>
#include <string.h>
#include <stdlib.h>

/* ========================================================== */
/* ====[                     Naive                      ]==== */
/* ========================================================== */

void naive_search(int k, char** ti, int* ni) {
    int i, j, c, start_j, start_i, len, d;
    int* count = (int*) malloc(sizeof(int)*(k+1));

    for (i = k; i >= 2; i--) count[i] = 0;

    /* choose Sj */
    for (j = 0; j < k; j++)
        /* choose substring of Sj */
        for (start_j = 0; start_j < ni[j]; start_j++)
            for (len = 1; start_j+len <= ni[j]; len++) { 
                d = 1;
                /* choose Si */
                for (i = 0; i < k; i++) {
                    if (i == j) continue; /* don't compare with itself */
                    /* choose suffix of Si */
                    for (start_i = 0; start_i < ni[i]; start_i++) {            
                        /* compare strings */
                        for (c = 0; ti[j][start_j+c] == ti[i][start_i+c] && ti[i][c] != '\0' && c != len; c++);
                        if (c == len) { /* match: increment d counter */
                            d++;
                            break;
                        }
                    }
                }
                /* update counter array */
                if (d > 1 && len > count[d]) count[d] = len;  
            }

    /* count[i-1] is at least count[i] */
    for (i = k-1; i > 2; i--)
        if (count[i] > count[i-1]) count[i-1] = count[i];

    /* print result */
    for (i = 2; i <= k; i++)
        printf("%d ", count[i]);
    printf("\n");

    free(count);
}


/* ========================================================== */
/* ====[                    Ukkonen                     ]==== */
/* ========================================================== */

/* =========[               Structs                ]========= */

typedef struct node* Node;
struct node {
    int str_i; /* The value of i in Ti */
    int head; /* The path-label start at &(Ti[head]) */
    int sdep; /* String-Depth */
    Node child;
    Node parent;
    Node brother;
    Node prevBrother;
    Node slink; /* Suffix link */
    int count; /* number of str_i for which it has descendents */
};

typedef struct point* Point;
struct point {
    Node a; /* node above */
    Node b; /* node bellow */
    int sdep; /* String-Depth */
};


/* =========[          Auxiliary functions         ]========= */

/* returns a new node in memory */
Node newNode(void** memory, int str_i, int head, int sdep, Node child) {
    Node node = (Node) *memory;
    *memory += sizeof(struct node);
    node->str_i = str_i;
    node->head = head;
    node->sdep = sdep;
    node->child = child;
    node->brother = NULL;
    node->prevBrother = NULL;
    node->parent = NULL;
    node->slink = NULL;
    node->count = 0;
    return node;
}

/* returns root node for a new tree */
Node getRoot(void** memory) {
    Node root = newNode(memory, -1, -1, 0, NULL);
    Node sentinel = newNode(memory, -1, -1, -1, root);
    root->parent = sentinel;
    root->slink = sentinel;
    return root;
}

/* resets 'p' to root */
void setInitialPoint(Point p, Node root) {
    p->sdep = 0;
    p->a = root;
    p->b = root;
}

/* returns new vector for suffix count in memory */
int* getCounterVector(void** memory, int k) {
    int i;
    int *c = (int*) *memory;
    *memory += sizeof(int*) * k;
    for (i = 0; i < k; i++) c[i] = 0;
    return c;
}

/* finds child of node whose edge path starts with c */
Node findChild(char** ti, Node node, char c) {
    Node child;
    int string_i, char_i;

    /* is in sentinel - return root */
    if (node->sdep == -1)
        return node->child;

    /* go through all children */
    for (child = node->child; child != NULL; child = child->brother) {
        string_i = child->str_i;
        char_i = (child->head + node->sdep) - 1;
        if (ti[string_i][char_i] == c)
            return child;
    }
    return NULL;
}

/* adds 'new' as child of parent */
void addChild(Node parent, Node new) {
    Node child = parent->child;
    parent->child = new;
    new->parent = parent;
    new->brother = child;
    new->prevBrother = NULL; /* set as first child */
    if (child != NULL) child->prevBrother = new;
}

/* adds 'new' between child and child's parent */
void addInternal(Node new, Node child) {
    Node prevBrother = child->prevBrother, brother = child->brother, parent = child->parent;

    /* set internal's parent and brothers */
    new->parent = parent;
    new->prevBrother = prevBrother;
    new->brother = brother;

    /* update parent and brothers */
    if (prevBrother != NULL) prevBrother->brother = new;
    else parent->child = new; /* is the first child - update parent */ 
    if (brother != NULL) brother->prevBrother = new;

    /* set previous child to be child of internal */
    addChild(new, child);
}

/* sets slink of last internal node that was inserted */
void setLastInternalSuffixLink(Node* pointer, Node newInternal) {
    Node lastInternal = *pointer;
    if (lastInternal != NULL) {
        lastInternal->slink = newInternal;
        *pointer = NULL;
    }
}


/* =========[         Main Ukkonen functions       ]========= */

/* returns 1 if can descend from p with char c and 0 if not */
int descendQ(char** ti, Point p, char c) {
    int string_i, char_i;

    /* pointer is in a node */
    if (p->sdep == p->b->sdep) {
        if (findChild(ti, p->b, c) != NULL) return 1;
    }

    /* pointer is in an edge */
    else {
        string_i = p->b->str_i;
        char_i = (p->b->head + p->sdep) - 1;
        if (ti[string_i][char_i] == c) return 1;
    }

    return 0;
}

/* descends pointer with c */
void descend(char** ti, Point p, char c) {
    if (p->sdep == p->b->sdep) { /* p in a node */
        p->a = p->b;
        p->b = findChild(ti, p->b, c);
    }
    p->sdep++;
}

/* adds a new leaf to the suffix tree */
void addLeaf(void** memory, Node* lastInternal, Point p, int i, int j, int ni) {
    Node leaf, internal;
    int head = j - (p->sdep-1);
    int depth = (ni - (head-1)) + 1; /* add leaf with path until $ (at index ni) */
    leaf = newNode(memory, i, head, depth, NULL);

    /* p is in an node - add leaf node */
    if (p->b->sdep == p->sdep)
        addChild(p->b, leaf);

    /* p is in an edge - add internal and leaf nodes */
    else {
        /* add internal to tree, with leaf and p->b as children */
        internal = newNode(memory, i, head, p->sdep, leaf);
        addInternal(internal, p->b);
        
        /* handle suffix links */
        setLastInternalSuffixLink(lastInternal, internal);
        *lastInternal = internal;
    }
}


/* jumps to the suffix of p in the tree */
void suffixLink(char** ti, Node* lastInternal, Point p) {
    Node current, next;
    int dist, g = 0, start;

    /* at root jump to sentinel */
    if (p->sdep == 0) {
        p->a = p->b = p->b->slink;
        p->sdep = -1;
        return;
    }

    /* start at p->a->slink and go down sdep */
    current = next = p->a->slink;
    dist = p->sdep - p->a->sdep;
    
    /* skip cut trick */
    start = p->b->head + p->a->sdep;
    while (g < dist) {
        current = next;
        next = findChild(ti, current, ti[p->b->str_i][(start + g) - 1]);
        g += next->sdep - current->sdep;
    }

    /* set pointer */
    p->a = current;
    p->b = next;
    p->sdep = (next->sdep - g) + dist;

    /* if jump ends at node, handle suffix links */
    if (p->sdep == p->b->sdep)
        setLastInternalSuffixLink(lastInternal, next);
}


/* =========[               Ukkonen                ]========= */

void ukkonen(void* memory, int k, char** ti, int* ni, Node root) {
    Point p = (Point) malloc(sizeof(struct point));
    Node *lastInternal = (Node*) malloc(sizeof(Node)); /* keep track of last internal node created */
    int i, j;

    for (i = 0; i < k; i++) {
        /* setup for new string */
        setInitialPoint(p, root);
        *lastInternal = NULL;
        ti[i][ni[i]] = '\1';
        
        /* add string to tree */
        j = 0;
        while (j <= ni[i]) {
            while (!descendQ(ti, p, ti[i][j])) {
                addLeaf(&memory, lastInternal, p, i, j, ni[i]);
                suffixLink(ti, lastInternal, p);
            }
            descend(ti, p, ti[i][j]);
            j++;
        }
        ti[i][ni[i]] = '\0';
    }

    free(lastInternal);
    free(p);
}


/* ========================================================== */
/* ====[               Longest Substrings               ]==== */
/* ========================================================== */

/* dfs to get the # of str_i in the descendants of each node  */
void countNodeSuffixes(void* memory, int k, Node parent, int* count) {
    Node child;
    int i,* aux;

    /* is a leaf */
    if (parent->child == NULL) {
        parent->count = 1; /* leafs will only have one str_i */
        count[parent->str_i] = 1;
    }

    else {
        /* not a leaf - get children's counts */
        aux = getCounterVector(&memory, k);
        for (child = parent->child; child != NULL; child = child->brother)
            countNodeSuffixes(memory, k, child, aux);

        /* merge counts */
        for (i = 0; i < k; i++) if (aux[i] == 1) count[i] = 1;
        for (i = 0; i < k; i++) if (aux[i] == 1) parent->count++;
    }
}

/* dfs to get the len of the longest substrings */
void getLongestSubstrings(int k, int* l, Node parent) {
    Node child;

    /* visit itself */
    if (parent->count >= 2 && parent->sdep > l[parent->count])
        l[parent->count] = parent->sdep;

    /* visit children */
    for (child = parent->child; child != NULL; child = child->brother)
        getLongestSubstrings(k, l, child);
}


/* ========================================================== */
/* ====[                 Main Functions                 ]==== */
/* ========================================================== */

void ukkonenLongestSubstrings(int k, int m, char** ti, int* ni) {
    Node root;
    int i, maxNodes = 2 * m + 2;
    int *final, *count;

    /* setup */
    void* nMemory = malloc(sizeof(struct node) * maxNodes); /* preallocate all nodes */ 
    void* vMemory = malloc((sizeof(int) * k) * (maxNodes/2)); /* preallocate aux vectors for all internal nodes */
    final = (int*) malloc(sizeof(int)*(k+1));
    for (i = 2; i <= k; i++) final[i] = 0;

    /* build suffix tree */
    root = getRoot(&nMemory);
    ukkonen(nMemory, k, ti, ni, root);

    /* get len of longest substrings */ 
    count = getCounterVector(&vMemory, k);
    countNodeSuffixes(vMemory, k, root, count);
    getLongestSubstrings(k, final, root);
        
    for (i = k-1; i > 2; i--) /* final[i-1] is at least final[i] */
        if (final[i] > final[i-1]) final[i-1] = final[i];

    /* print result */
    for (i = 2; i <= k; i++)
        printf("%d ", final[i]);
    printf("\n");

    free(root);
    free(count);
    free(final);
}


void get_input(int* size_ptr, char** buf_ptr) {
    int i = 0, size = *size_ptr;
    char* buffer = *buf_ptr;
    char c = getchar();
  
    while (c != ' ' && c != '\n' && c != EOF) {
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


int main() {
    int line_size = 500, i, k;
    char* line = (char*) malloc(sizeof(char)*line_size);
    char** ti;
    int* ni, m = 0;

    /* first line: integer k */
    get_input(&line_size, &line);
    k = atoi(line);
    ti = (char**) malloc(sizeof(char*)*k);
    ni = (int*) malloc(sizeof(int)*k);

    for (i = 0; i < k; i++) {
        /* get size of string i */
        get_input(&line_size, &line);
        ni[i] = atoi(line);
        ti[i] = (char*) malloc(sizeof(char)*(ni[i]+1));

        /* get string i */
        get_input(&line_size, &line);
        strcpy(ti[i], line);

        m += ni[i] + 1;
    }

    /* naive_search(k, ti, ni); */
    ukkonenLongestSubstrings(k, m, ti, ni);

    free(line);
    for (i = 0; i < k; i++) free(ti[i]);
    free(ti);
    free(ni);
    return 0;
}