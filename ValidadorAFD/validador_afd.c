/*
 * Proyecto - Análisis Lexicográfico
 * Validador de Cadenas mediante AFD en C
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdbool.h>

#define MAX_ER           4096
#define MAX_POSTFIX      8192
#define MAX_POSICIONES   1024
#define MAX_ESTADOS_AFD  4096

typedef struct {
    unsigned long long lo;
    unsigned long long hi;
} Bitset;

static Bitset bs_empty() { return (Bitset) { 0ULL, 0ULL }; }

static void bs_add(Bitset* b, int pos) {
    if (pos < 64) b->lo |= (1ULL << pos);
    else       b->hi |= (1ULL << (pos - 64));
}
static bool bs_has(Bitset b, int pos) {
    return pos < 64 ? (b.lo & (1ULL << pos)) : (b.hi & (1ULL << (pos - 64)));
}
static Bitset bs_or(Bitset a, Bitset b) {
    return (Bitset) { a.lo | b.lo, a.hi | b.hi };
}
static bool bs_eq(Bitset a, Bitset b) {
    return a.lo == b.lo && a.hi == b.hi;
}

typedef struct { char v[MAX_ER]; int top; } PilaChar;
static void pc_init(PilaChar* p) { p->top = -1; }
static bool pc_empty(PilaChar* p) { return p->top < 0; }
static void pc_push(PilaChar* p, char c) { p->v[++p->top] = c; }
static char pc_pop(PilaChar* p) { return pc_empty(p) ? '\0' : p->v[p->top--]; }
static char pc_peek(PilaChar* p) { return pc_empty(p) ? '\0' : p->v[p->top]; }

static int prec(char op) {
    return op == '*' ? 3 : op == '.' ? 2 : op == '|' ? 1 : 0;
}

static void insertar_puntos(const char* in, char* out) {
    int j = 0;
    for (size_t i = 0; in[i]; i++) {
        char c = in[i];
        out[j++] = c;

        char sig = in[i + 1];
        if (c == '\0')break;

        if (c != '(' && c != '|' && c != '\0' &&
            sig != ')' && sig != '|' && sig != '*' && sig != '\0') {
            out[j++] = '.';
        }
    }
    out[j] = '\0';
}

static void a_postfijo(const char* in, char* post) {
    PilaChar pila; pc_init(&pila); int j = 0;
    for (size_t i = 0; in[i]; i++) {
        char c = in[i];
        if (isalnum(c) || c == '#') {
            post[j++] = c;
        }
        else if (c == '(') {
            pc_push(&pila, c);
        }
        else if (c == ')') {
            while (!pc_empty(&pila) && pc_peek(&pila) != '(')
                post[j++] = pc_pop(&pila);
            pc_pop(&pila);
        }
        else {
            while (!pc_empty(&pila) && prec(pc_peek(&pila)) >= prec(c))
                post[j++] = pc_pop(&pila);
            pc_push(&pila, c);
        }
    }
    while (!pc_empty(&pila)) post[j++] = pc_pop(&pila);
    post[j] = '\0';
}

typedef struct Nodo {
    char op;
    char simbolo;
    int  pos;
    int  nullable;
    Bitset firstpos, lastpos;
    struct Nodo* izq, * der;
} Nodo;

typedef struct { Nodo* v[MAX_POSTFIX]; int top; } PilaNodo;
static void pn_init(PilaNodo* p) { p->top = -1; }
static void pn_push(PilaNodo* p, Nodo* n) { p->v[++p->top] = n; }
static Nodo* pn_pop(PilaNodo* p) { return p->v[p->top--]; }

static Nodo* hojas[MAX_POSICIONES];
static Bitset followpos[MAX_POSICIONES];
static char   simbolo_hoja[MAX_POSICIONES];

static int posiciones_total = 0;
static char alfabeto[32]; int sigma_sz = 0;

static Nodo* nuevo_hoja(char simbolo) {
    Nodo* n = (Nodo*)malloc(sizeof(Nodo));
    n->op = 0; n->simbolo = simbolo; n->izq = n->der = NULL;
    n->nullable = 0;
    n->firstpos = bs_empty();
    n->lastpos = bs_empty();
    n->pos = posiciones_total;
    bs_add(&n->firstpos, posiciones_total);
    bs_add(&n->lastpos, posiciones_total);
    hojas[posiciones_total] = n;
    followpos[posiciones_total] = bs_empty();
    simbolo_hoja[posiciones_total] = simbolo;
    posiciones_total++;

    if (simbolo != '#') {
        bool found = false;
        for (int i = 0; i < sigma_sz; i++) if (alfabeto[i] == simbolo) { found = true; break; }
        if (!found) alfabeto[sigma_sz++] = simbolo;
    }
    return n;
}

static Nodo* construir_arbol(const char* post) {
    PilaNodo pila; pn_init(&pila);

    for (size_t i = 0; post[i]; i++) {
        char c = post[i];
        if (isalnum(c) || c == '#') {
            pn_push(&pila, nuevo_hoja(c));
        }
        else if (c == '*') {
            Nodo* n = (Nodo*)malloc(sizeof(Nodo));
            n->op = '*'; n->simbolo = 0; n->der = NULL;
            n->izq = pn_pop(&pila);
            n->nullable = 1;
            n->firstpos = n->izq->firstpos;
            n->lastpos = n->izq->lastpos;

            for (int p = 0; p < posiciones_total; p++)
                if (bs_has(n->izq->lastpos, p))
                    followpos[p] = bs_or(followpos[p], n->izq->firstpos);
            pn_push(&pila, n);
        }
        else if (c == '.' || c == '|') {
            Nodo* der = pn_pop(&pila);
            Nodo* izq = pn_pop(&pila);
            Nodo* n = (Nodo*)malloc(sizeof(Nodo));
            n->op = c; n->simbolo = 0; n->izq = izq; n->der = der;
            
            if (c == '|') n->nullable = izq->nullable || der->nullable;
            else       n->nullable = izq->nullable && der->nullable;
            
            if (c == '|') n->firstpos = bs_or(izq->firstpos, der->firstpos);
            else {
                n->firstpos = izq->nullable ? bs_or(izq->firstpos, der->firstpos)
                    : izq->firstpos;
            }

            if (c == '|') n->lastpos = bs_or(izq->lastpos, der->lastpos);
            else {
                n->lastpos = der->nullable ? bs_or(izq->lastpos, der->lastpos)
                    : der->lastpos;
            }

            if (c == '.') {
                for (int p = 0; p < posiciones_total; p++)
                    if (bs_has(izq->lastpos, p))
                        followpos[p] = bs_or(followpos[p], der->firstpos);
            }
            pn_push(&pila, n);
        }
    }
    return pn_pop(&pila);
}

static Bitset Dstates[MAX_ESTADOS_AFD];
static bool   Dmarked[MAX_ESTADOS_AFD];
static int    Dtrans[MAX_ESTADOS_AFD][32];
static int    Dstates_count = 0;

static int dstate_index(Bitset s) {
    for (int i = 0; i < Dstates_count; i++)
        if (bs_eq(Dstates[i], s)) return i;
    return -1;
}

static int construir_afd(Nodo* raiz) {
    Dstates[0] = raiz->firstpos;
    Dmarked[0] = false;
    for (int i = 0; i < 32; i++) Dtrans[0][i] = -1;
    Dstates_count = 1;

    while (true) {
        int i_unmarked = -1;
        for (int i = 0; i < Dstates_count; i++) if (!Dmarked[i]) { i_unmarked = i; break; }
        if (i_unmarked == -1) break;

        Bitset S = Dstates[i_unmarked];
        Dmarked[i_unmarked] = true;

        for (int a = 0; a < sigma_sz; a++) {
            char simbolo = alfabeto[a];
            Bitset U = bs_empty();

            for (int p = 0; p < posiciones_total; p++) {
                if (bs_has(S, p) && simbolo_hoja[p] == simbolo) {
                    U = bs_or(U, followpos[p]);
                }
            }
            if (U.lo == 0ULL && U.hi == 0ULL) continue;

            int j = dstate_index(U);
            if (j == -1) {
                j = Dstates_count;
                Dstates[Dstates_count] = U;
                Dmarked[Dstates_count] = false;
                for (int k = 0; k < 32; k++) Dtrans[Dstates_count][k] = -1;
                Dstates_count++;
            }
            Dtrans[i_unmarked][a] = j;
        }
    }
    return 0;
}

static int pos_hash = -1;
static bool es_final(Bitset S) {
    return pos_hash != -1 && bs_has(S, pos_hash);
}

static int ind_simbolo(char c) {
    for (int a = 0; a < sigma_sz; a++) if (alfabeto[a] == c) return a;
    return -1;
}

static void validar_cadena(const char* cad) {
    if (sigma_sz == 0) { puts("AFD vacío."); return; }

    Bitset estado = Dstates[0];
    int     pos_err = -1;
    char    char_err = '\0';

    for (int i = 0; cad[i] != '\0'; i++) {
        char c = cad[i];
        int idx = ind_simbolo(c);
        if (idx == -1) {
            printf("Cadena RECHAZADA: caracter '%c' fuera del alfabeto en posicion %d\n",
                c, i + 1);
            return;
        }
        int e_actual = dstate_index(estado);
        int e_sig = Dtrans[e_actual][idx];
        if (e_sig == -1) {
            printf("Cadena RECHAZADA en el caracter %d ('%c')\n", i + 1, c);
            return;
        }
        estado = Dstates[e_sig];
        pos_err = i;
        char_err = c;
    }


    if (es_final(estado)) {
        puts("Cadena ACEPTADA.");
    }
    else {
        printf("Cadena RECHAZADA: Falta transicion en el caracter %d (finaliza con '%c').\n",
            pos_err + 1, char_err);
    }
}

bool parentesis_balanceados(const char* s) {
    int balance = 0;
    for (int i = 0; s[i]; i++) {
        if (s[i] == '(') balance++;
        else if (s[i] == ')') {
            balance--;
            if (balance < 0) return false;
        }
    }
    return balance == 0;
}

bool caracteres_validos(const char* s) {
    for (int i = 0; s[i]; i++) {
        char c = s[i];
        if (!(isalnum(c) || c == '(' || c == ')' || c == '|' || c == '*' || c == '#')) {
            return false;
        }
    }
    return true;
}

int main(void) {
    char er_in[MAX_ER];
    char er_concat[MAX_POSTFIX];
    char er_post[MAX_POSTFIX];

    printf("Ingrese una expresion regular: ");
    fgets(er_in, sizeof(er_in), stdin);
    er_in[strcspn(er_in, "\n")] = '\0';
    if (strlen(er_in) == 0) { puts("Expresion vacia. Terminando."); return 0; }

    char er_con_hash[MAX_ER + 2];
    snprintf(er_con_hash, sizeof(er_con_hash), "(%s)#", er_in);

    insertar_puntos(er_con_hash, er_concat);
    a_postfijo(er_concat, er_post);

    posiciones_total = 0; sigma_sz = 0;
    Nodo* raiz = construir_arbol(er_post);

    for (int p = 0; p < posiciones_total; p++) if (simbolo_hoja[p] == '#') { pos_hash = p; break; }

    construir_afd(raiz);

    puts("\n[AFD construido. Modo validacion activo.]");

    char buffer[256];
    while (1) {
        printf("Ingrese cadena: ");
        fgets(buffer, sizeof(buffer), stdin);
        buffer[strcspn(buffer, "\n")] = '\0';

        if (strlen(buffer) == 0) {
            printf("[ENTER]\n");
            break;
        }

        validar_cadena(buffer);
        puts("");
    }
    puts("Programa terminado.");
    return 0;
}