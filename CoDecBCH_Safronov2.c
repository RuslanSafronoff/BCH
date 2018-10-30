/* ===============  Encoder/Decoder for binary BCH codes =================
 *
 * m = порядок поля Галуа GF(2**m)
 * N = размер мультипликативной группы GF(2**m)
 * n = 2**m - 1 длина примитивного БЧХ-кода
 * t = исправляющая способность (максимальное количество ошибок, исправляемых кодом)
 * d = 2*t + 1 = минимальное расстояние = число последовательных корней g(x) + 1
 * k = N - deg(g(x)) = измерение (число информационных битов)
 * p[] = коэффициенты примитивного неприводимого многочлена, используемого для генерации GF(2**m)
 * g[] = коэффициенты порождающего многочлена, g(x)
 * alpha_to [] =  таблица логарифмов GF(2**m)
 * index_of[] =  таблица обратных логарифмов GF(2**m)
 * data[] = информационные биты = коэффициенты многочлена данных, i(x)
 * bb[] = коэффициенты проверочного многочлена x^(n-k) i(x) modulo g(x)
 * numerr = число ошибок
 * errpos[] = позиции ошибок
 * recd[] = коэффициенты полученного многочлена
 * decerror = число декодированных ошибок (в позициях сообщения)
 *
 */

#include <math.h>
#include <stdio.h>
#include <stdlib.h>

int             m, N, n, k, t, d, ff, fff;
int             p[11];
int             alpha_to[128], index_of[128], g[128];
int             recd[128], data[128], bb[128];
int             seed;
int             numerr, errpos[64], decerror = 0;

void
GetGF()
/*
 * Получение поля GF(2**m) из примитивного неприводимого многочлена p(x)
 * с коэффициентами p[0]..p[m].
 *
 * Получение таблицы:
 *   индексная форма -> полиномиальная форма: alpha_to[] содержит j=alpha^i;
 *   полиномиальная форма -> индексная форма:	index_of[j=alpha^i] = i
 *
 * alpha = 2 примитивный элемент GF(2**m)
 */
{
    register int    i, mask;

    mask = 1;
    alpha_to[m] = 0;
    for (i = 0; i < m; i++) {
        alpha_to[i] = mask;
        index_of[alpha_to[i]] = i;
        if (p[i] != 0)
            alpha_to[m] ^= mask;
        mask <<= 1;
    }
    index_of[alpha_to[m]] = m;
    mask >>= 1;
    for (i = m + 1; i < N; i++) {
        if (alpha_to[i - 1] >= mask)
            alpha_to[i] = alpha_to[m] ^ ((alpha_to[i - 1] ^ mask) << 1);
        else
            alpha_to[i] = alpha_to[i - 1] << 1;
        index_of[alpha_to[i]] = i;
    }
    index_of[0] = -1;
}


void
GetGenPoly()
/*
 * Вычисление порождающего многочлена бинарного БЧХ-кода. Сначала генерируются
 * циклические множества modulo 2**m - 1, cycle[][] =  (i, 2*i, 4*i, ..., 2^l*i). Затем
 * определяются множества, которые содержат целые числа из {1..(d-1)}.
 * Порождающий многочлен вычисляется
 * как продукт линейных факторов формы (x+alpha^i), для каждого i в
 * циклических множествах.
 */
{
    register int	ii, jj, ll, kaux;
    register int	test, aux, nocycles, root, noterms, rdncy;
    int             cycle[1024][21], size[1024], min[1024], zeros[1024];

    /* Генерируются циклические множества modulo N, N = 2**m - 1*/
    cycle[0][0] = 0;
    size[0] = 1;
    cycle[1][0] = 1;
    size[1] = 1;
    jj = 1;			/* индекс циклического множества */
    do {
        /* Генерируется jj-ое килическое множество */
        ii = 0;
        do {
            ii++;
            cycle[jj][ii] = (cycle[jj][ii - 1] * 2) % N;
            size[jj]++;
            aux = (cycle[jj][ii] * 2) % N;
        } while (aux != cycle[jj][0]);
        /* Следующий представитель циклического множества */
        ll = 0;
        do {
            ll++;
            test = 0;
            for (ii = 1; ((ii <= jj) && (!test)); ii++)
                /* Проверяется предыдущее циклическое множество */
                for (kaux = 0; ((kaux < size[ii]) && (!test)); kaux++)
                    if (ll == cycle[ii][kaux])
                        test = 1;
        } while ((test) && (ll < (N - 1)));
        if (!(test)) {
            jj++;	/* следующий индекс циклического множества */
            cycle[jj][0] = ll;
            size[jj] = 1;
        }
    } while (ll < (N - 1));
    nocycles = jj;		/* число циклических множеств modulo N */

    printf("==>Введите исправляющую способность, t: ");
    scanf("%d", &t);

    d = 2 * t + 1;

    /* Поиск корней 1, 2, ..., d-1 в циклических множествах */
    kaux = 0;
    rdncy = 0;
    for (ii = 1; ii <= nocycles; ii++) {
        min[kaux] = 0;
        test = 0;
        for (jj = 0; ((jj < size[ii]) && (!test)); jj++)
            for (root = 1; ((root < d) && (!test)); root++)
                if (root == cycle[ii][jj])  {
                    test = 1;
                    min[kaux] = ii;
                }
        if (min[kaux]) {
            rdncy += size[min[kaux]];
            kaux++;
        }
    }
    noterms = kaux;
    kaux = 1;
    for (ii = 0; ii < noterms; ii++)
        for (jj = 0; jj < size[min[ii]]; jj++) {
            zeros[kaux] = cycle[min[ii]][jj];
            kaux++;
        }

    k = n - rdncy;

    if (k<0)
    {
        printf("==Недопустимые параметры!==\n");
        exit(0);
    }

    printf("==Это (%d, %d, %d) бинарный БЧХ-код==\n", n, k, d);

    /* Вычисление порождающего многочлена */
    g[0] = alpha_to[zeros[1]];
    g[1] = 1;		/* g(x) = (X + zeros[1]) изначально */
    for (ii = 2; ii <= rdncy; ii++) {
        g[ii] = 1;
        for (jj = ii - 1; jj > 0; jj--)
            if (g[jj] != 0)
                g[jj] = g[jj - 1] ^ alpha_to[(index_of[g[jj]] + zeros[ii]) % N];
            else
                g[jj] = g[jj - 1];
        g[0] = alpha_to[(index_of[g[0]] + zeros[ii]) % N];
    }
    printf("Порождающий многочлен:\ng(x) = ");
    for (ii = 0; ii <= rdncy; ii++) {
        printf("%d", g[ii]);
        if (ii && ((ii % 50) == 0))
            printf("\n");
    }
    printf("\n");
}


void
EncoderBCH()
/*
 * Вычисление проверочного bb[], коэффициентов b(x). Проверочный
 * многочлен b(x) является остатком от деления x^(n-k)*data(x)
 * на порождающий многочлен g(x)
 */
{
    register int    i, j;
    register int    feedback;

    for (i = 0; i < n - k; i++)
        bb[i] = 0;
    for (i = k - 1; i >= 0; i--) {
        feedback = data[i] ^ bb[n - k - 1];
        if (feedback != 0) {
            for (j = n - k - 1; j > 0; j--)
                if (g[j] != 0)
                    bb[j] = bb[j - 1] ^ feedback;
                else
                    bb[j] = bb[j - 1];
            bb[0] = g[0] && feedback;
        } else {
            for (j = n - k - 1; j > 0; j--)
                bb[j] = bb[j - 1];
            bb[0] = 0;
        }
    }
}


void
DecoderBCH()
/*
 * Мы получили биты в recd[i], i=0..(N-1).
 *
 * Вычисление 2*t синдромов подстановкой alpha^i в rec(X) и
 * оценкой, синдромы хранятся в s[i], i=1..2t (s[0] = 0).
 * Затем мы используем алгоритм Берлекэмпа, чтобы найти
 * многочлен  локаторов ошибки elp[i].
 *
 * Если степень elp > t, мы не сможем исправить все ошибки, и
 * и мы обнаружили неисправляемый шаблон ошибок. Мы выводим
 * информационные биты неисправленными
 *
 * Если степень elp is <= t, мы последовательно подставляем alpha^i , i=1..N в elp,
 * чтобы найти корни, затем инвертированные корни, номера локации ошибок.
 * Эта так называемая процедура Ченя.
 *
 * Если число ошибок не равно степени elp,
 * декодер предполагает, что ошибок больше чем t и не может исправить
 * их, а только обнаружить. Мы выводим
 * информационные биты неисправленными.
 */
{
    register int    i, j, u, q, t2, count = 0, syn_error = 0;
    int             elp[1026][1024], d[1026], l[1026], u_lu[1026], s[1025];
    int             root[200], loc[200], err[1024], reg[201];

    t2 = 2 * t;

    /* Сначала формируются синдромы */
    printf("S(x) = ");
    for (i = 1; i <= t2; i++) {
        s[i] = 0;
        for (j = 0; j < n; j++)
            if (recd[j] != 0)
                s[i] ^= alpha_to[(i * j) % N];
        if (s[i] != 0)
            syn_error = 1; /* установить флаг ошибки, если синдром ненулевой */
/*
 * Заметьте: Выйдите из программы здесь,
 *           если используете код только для индикации ошибок
 */
        /* конвертирование синдрома из полиномиальной формы в индексную  */
        s[i] = index_of[s[i]];
        printf("%3d ", s[i]);
    }
    printf("\n");

    if (syn_error) {	/* если есть ошибки, пытаемся исправить их */
        /*
         * Вычисление многочлена локаторов ошибки с помощью
         * итеративного алгоритма Берлекэмпа-Мэсси.
         * d[u] – mu-ое расхождение, где
         * u='mu'+1 and 'mu' (греческая буква) – номер шага
         * от -1 до 2*t, l[u] – степень
         * elp на том шаге, и u_l[u] – различие между
         * номером шага и степенью elp.
         */
        printf("==Обнаружены ошибки==\n");
        ff = 1;
        /* инициализация табличных записей */
        d[0] = 0;			/* индексная форма */
        d[1] = s[1];		/* индексная форма */
        elp[0][0] = 0;		/* индексная форма */
        elp[1][0] = 1;		/* полиномиальная форма */
        for (i = 1; i < t2; i++) {
            elp[0][i] = -1;	/* индексная форма */
            elp[1][i] = 0;	/* полиномиальная форма */
        }
        l[0] = 0;
        l[1] = 0;
        u_lu[0] = -1;
        u_lu[1] = 0;
        u = 0;

        do {
            u++;
            if (d[u] == -1) {
                l[u + 1] = l[u];
                for (i = 0; i <= l[u]; i++) {
                    elp[u + 1][i] = elp[u][i];
                    elp[u][i] = index_of[elp[u][i]];
                }
            } else
                /*
                 * поиск слов с наибольшим u_lu[q], для которых d[q]!=0
                 */
            {
                q = u - 1;
                while ((d[q] == -1) && (q > 0))
                    q--;
                /* нашли первый ненулевой d[q]  */
                if (q > 0) {
                    j = q;
                    do {
                        j--;
                        if ((d[j] != -1) && (u_lu[q] < u_lu[j]))
                            q = j;
                    } while (j > 0);
                }

                /*
                 * нашли такое q, что d[u]!=0 и u_lu[q] максимальное
                 */
                /* сохранение степени ноаого многочлена elp */
                if (l[u] > l[q] + u - q)
                    l[u + 1] = l[u];
                else
                    l[u + 1] = l[q] + u - q;

                /* формируем новый elp(x) */
                for (i = 0; i < t2; i++)
                    elp[u + 1][i] = 0;
                for (i = 0; i <= l[q]; i++)
                    if (elp[q][i] != -1)
                        elp[u + 1][i + u - q] =
                                alpha_to[(d[u] + N - d[q] + elp[q][i]) % N];
                for (i = 0; i <= l[u]; i++) {
                    elp[u + 1][i] ^= elp[u][i];
                    elp[u][i] = index_of[elp[u][i]];
                }
            }
            u_lu[u + 1] = u - l[u + 1];

            /* формируем (u+1)-ое различие */
            if (u < t2) {
                /* не вычислено различий на последней итерации */
                if (s[u + 1] != -1)
                    d[u + 1] = alpha_to[s[u + 1]];
                else
                    d[u + 1] = 0;
                for (i = 1; i <= l[u + 1]; i++)
                    if ((s[u + 1 - i] != -1) && (elp[u + 1][i] != 0))
                        d[u + 1] ^= alpha_to[(s[u + 1 - i]
                                              + index_of[elp[u + 1][i]]) % N];
                /* кладём d[u+1] в индексную форму */
                d[u + 1] = index_of[d[u + 1]];
            }
        } while ((u < t2) && (l[u + 1] <= t));

        u++;
        if (l[u] <= t) {/* Можем исправить ошибки */
            /* кладём elp в индексную форму */
            fff = 1;
            for (i = 0; i <= l[u]; i++)
                elp[u][i] = index_of[elp[u][i]];

            printf("sigma(x) = ");
            for (i = 0; i <= l[u]; i++)
                printf("%3d ", elp[u][i]);
            printf("\n");
            printf("Корни: ");

            /* Процедура Ченя: находим корни многочлена локаторов ошибки */
            for (i = 1; i <= l[u]; i++)
                reg[i] = elp[u][i];
            count = 0;
            for (i = 1; i <= N; i++) {
                q = 1;
                for (j = 1; j <= l[u]; j++)
                    if (reg[j] != -1) {
                        reg[j] = (reg[j] + j) % N;
                        q ^= alpha_to[reg[j]];
                    }
                if (!q) {	/* сохраняем корень и индексы
						 * номеров локации ошибки */
                    root[count] = i;
                    loc[count] = N - i;
                    count++;
                    printf("%3d ", N - i);
                }
            }
            printf("\n");
            if (count == l[u])
                /* число корней = степени elp, значит <= t ошибок */
                for (i = 0; i < l[u]; i++)
                    recd[loc[i]] ^= 1;
            else {
                fff = 0;
                printf("==Незавершённое декодирование==\n");
            }	/* elp имеет степень >t, значит неразрешимо */
        } else
            printf("==Незавершённое декодирование==\n");
    }
}


void main()
{
    int             i, j, kk, NN, flag, f1 = 0, f2 = 0;
    printf("==Кодировщик/декодировщик для бинарных БЧХ-кодов==\n");
    do {
        printf("==>Введите m (4 или 7): ");
        scanf("%d", &m);
    } while ((m != 4) && (m != 7));
    for (i=1; i<m; i++)
        p[i] = 0;
    p[0] = p[m] = 1;
    if (m == 4)	p[1] = 1;
    else if (m == 7)	p[1] = 1;
    printf("p(x) = ");
    N = 1;
    for (i = 0; i <= m; i++) {
        N *= 2;
        printf("%1d", p[i]);
    }
    printf("\n");
    N = N / 2 - 1;
    n = N;
    GetGF();            /* Получение поля Галуа GF(2**m), таблицы логарифмов и обратных логарифмов */
    GetGenPoly();       /* Получение порождающего многочлена БЧХ-кода */
    do {
        printf("==>Введите 1, чтобы ошибок было <= t,\n"
               "           2, чтобы ошибок было > t и <= 2t,\n"
               "           3, чтобы ошибок было > 2t\n");
        scanf("%d", &flag);
    } while (flag > 3 || flag < 1);
    if (flag == 1){
        f1 = 0; f2 = t + 1;
    } else if (flag == 2) {
        f1 = t + 1; f2 = t;
    } else {
        f1 = 2*t + 1; f2 = n - f1 + 1;
    }
    do {
        printf("==>Введите число сессий от 1 до 50: ");
        scanf("%d", &NN);
    } while (NN > 50 || NN < 1);
    int sc[n], sc_n, sc_, a, b, random;
    for (kk = 0; kk < NN; kk++) {
        ff = 0, fff = 0;
        sc_ = 1;
        /* Генерация случайной информации */
        for (i = 0; i < k; i++)
            data[i] = ( rand() & 65536 ) >> 16;
        EncoderBCH();
        for (i = 0; i < n - k; i++)
            recd[i] = bb[i];
        for (i = 0; i < k; i++)
            recd[i + n - k] = data[i];
        printf("Полиномиальный код:\nc(x) = ");
        for (i = 0; i < n; i++) {
            printf("%1d", recd[i]);
            if (i && ((i % 50) == 0))
                printf("\n");
        }
        printf("\n");
        numerr = rand() % f2 + f1;
        printf("Число ошибок: %d\n", numerr);
        for (i = 0; i < n; i++)
                sc[i] = -1;
        sc[0] = n-1;
        printf("Локации ошибок: ");
        for (int ii = 0; ii < numerr; ii++) {
            sc_n = rand() % sc_ + 1;
            j = 0; i = -1;
            while (j != sc_n) {
                i++;
                if (sc[i] != -1)
                    j++;
            }
            a = i; b = sc[i];
            random = rand() % (b - a + 1) + a;
            errpos[ii] = random;
            printf("%d ", random);
            if (random != a) {
                sc[a] = random - 1;
                if (b != random) {
                    sc[random + 1] = b;
                    sc_++;
                } else {
                    sc[b] = -1;
                }
            } else if (b != random){
                sc[random + 1] = b;
                sc[a] = -1;
            } else {
                sc[a] = -1;
                sc[b] = -1;
                sc_--;
            }
        }
        printf("\n");
        if (numerr)
            for (i = 0; i < numerr; i++)
                recd[errpos[i]] ^= 1;
        printf("r(x) = ");
        for (i = 0; i < n; i++) {
            printf("%1d", recd[i]);
            if (i && ((i % 50) == 0))
                printf("\n");
        }
        printf("\n");
        DecoderBCH();
        /*
        * напечатать исходное и декодированное сообщение
        */
        printf("Результаты:\n");
        printf("Исходное сообщение = ");
        for (i = 0; i < k; i++) {
            printf("%1d", data[i]);
            if (i && ((i % 50) == 0))
                printf("\n");
        }
        printf("\nВосстановленное сообщение = ");
        for (i = n - k; i < n; i++) {
            printf("%1d", recd[i]);
            if ((i-n+k) && (((i-n+k) % 50) == 0))
                printf("\n");
        }
        printf("\n");
        /*
         * Декодировочные ошибки? Сравниваем только информационные символы
         */
        decerror = 0;
        for (i = n - k; i < n; i++)
            if (data[i - n + k] != recd[i])
        decerror++;printf("==Найдено %d декодировочных ошибок в сообщении==\n", decerror);
        printf("\n");
    }
}
