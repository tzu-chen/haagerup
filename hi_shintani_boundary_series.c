/* Certified enclosures of the analytic HI candidate, using FLINT/Arb.
 *
 * Build: cc -O2 -std=c11 -Wall -Wextra -Werror
 *          hi_shintani_boundary_series.c -o /tmp/hi_shintani_boundary_series
 *          $(pkg-config --cflags --libs flint)
 *
 * A residual enclosure containing zero is NOT a proof of exact equality.
 * Section 90 supplies a separate sufficient inequality for correcting
 * these trials. The program reports whether that inequality is met.
 * The upper-half-plane series, its tail, and the real-axis extrapolation
 * remainder are justified in Section 80.7 of the research notes.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/resource.h>
#include <flint/arb.h>
#include <flint/acb.h>

#ifndef PREC
#define PREC 256
#endif
#ifndef LEVELS
#define LEVELS 8
#endif

typedef struct {
    slong n;
    arb_t d, A, B, AB, delta, pi, divisor_bound, remainder, target;
    arb_ptr heights, weights, rx, rv;
} context;

static void require(int ok, const char *message)
{
    if (!ok) { fprintf(stderr, "FAILED: %s\n", message); exit(1); }
}

static void one_minus(arb_t result, const arb_t value)
{
    arb_sub_ui(result, value, 1, PREC);
    arb_neg(result, result);
}

static void init_context(context *ctx, slong n)
{
    ctx->n = n;
    arb_init(ctx->d); arb_init(ctx->A); arb_init(ctx->B); arb_init(ctx->AB);
    arb_init(ctx->delta); arb_init(ctx->pi); arb_init(ctx->divisor_bound);
    arb_init(ctx->remainder); arb_init(ctx->target);
    ctx->heights = _arb_vec_init(LEVELS); ctx->weights = _arb_vec_init(LEVELS);
    ctx->rx = _arb_vec_init(LEVELS); ctx->rv = _arb_vec_init(LEVELS);
    arb_t t, u, v, sum;
    arb_init(t); arb_init(u); arb_init(v); arb_init(sum);
    arb_sqrt_ui(ctx->d, (ulong) (n*n+4), PREC);
    arb_set(ctx->divisor_bound, ctx->d);
    arb_add_ui(ctx->d, ctx->d, (ulong) n, PREC);
    arb_mul_2exp_si(ctx->d, ctx->d, -1);
    arb_add_ui(ctx->A, ctx->d, 1, PREC);
    arb_inv(ctx->B, ctx->d, PREC);
    arb_neg(ctx->delta, ctx->B);
    arb_add_ui(ctx->B, ctx->B, 1, PREC);
    arb_mul(ctx->AB, ctx->A, ctx->B, PREC);
    arb_const_pi(ctx->pi, PREC);
    arb_one(t); arb_mul_2exp_si(t, t, -1);
    arb_add(ctx->divisor_bound, ctx->divisor_bound, t, PREC);
    arb_mul_2exp_si(ctx->divisor_bound, ctx->divisor_bound, -2);
    arb_one(ctx->target);
    arb_mul_2exp_si(ctx->target, ctx->target, -(LEVELS*LEVELS+5*LEVELS+20));
    arb_one(ctx->remainder);
    for (slong k = 1; k < LEVELS; ++k) {
        arb_one(t); arb_mul_2exp_si(t, t, -2*k);
        arb_add_ui(u, t, 1, PREC);
        one_minus(v, t);
        arb_div(u, u, v, PREC);
        arb_mul(ctx->remainder, ctx->remainder, u, PREC);
    }
    arb_mul_ui(ctx->remainder, ctx->remainder, 5, PREC);
    arb_div_ui(ctx->remainder, ctx->remainder, 2*LEVELS, PREC);
    arb_mul_2exp_si(ctx->remainder, ctx->remainder, -(LEVELS*LEVELS+5*LEVELS));
    for (slong j = 0; j < LEVELS; ++j) {
        arb_one(ctx->heights+j);
        arb_mul_2exp_si(ctx->heights+j, ctx->heights+j, -2-j);
        arb_one(ctx->weights+j);
        arb_one(t); arb_mul_2exp_si(t, t, -2*j);
        for (slong k = 0; k < LEVELS; ++k) if (k != j) {
            arb_one(u); arb_mul_2exp_si(u, u, -2*k);
            arb_sub(v, u, t, PREC);
            arb_div(u, u, v, PREC);
            arb_mul(ctx->weights+j, ctx->weights+j, u, PREC);
        }
        arb_add(sum, sum, ctx->weights+j, PREC);
        arb_mul(t, ctx->pi, ctx->heights+j, PREC);
        arb_mul_si(t, t, -2, PREC);
        arb_div(u, t, ctx->A, PREC); arb_exp(ctx->rx+j, u, PREC);
        arb_div(u, t, ctx->B, PREC); arb_exp(ctx->rv+j, u, PREC);
    }
    require(arb_contains_si(sum, 1), "Richardson weights sum to one");
    for (slong k = 1; k < LEVELS; ++k) {
        arb_zero(sum);
        for (slong j = 0; j < LEVELS; ++j) {
            arb_pow_ui(t, ctx->heights+j, (ulong) (2*k), PREC);
            arb_addmul(sum, t, ctx->weights+j, PREC);
        }
        require(arb_contains_zero(sum), "Richardson even moment cancellation");
    }
    arb_clear(t); arb_clear(u); arb_clear(v); arb_clear(sum);
}

static void clear_context(context *ctx)
{
    arb_clear(ctx->d); arb_clear(ctx->A); arb_clear(ctx->B); arb_clear(ctx->AB);
    arb_clear(ctx->delta); arb_clear(ctx->pi); arb_clear(ctx->divisor_bound);
    arb_clear(ctx->remainder); arb_clear(ctx->target);
    _arb_vec_clear(ctx->heights, LEVELS); _arb_vec_clear(ctx->weights, LEVELS);
    _arb_vec_clear(ctx->rx, LEVELS); _arb_vec_clear(ctx->rv, LEVELS);
}

static void series_tail(arb_t tail, const context *ctx, slong j,
                        const arb_t px, const arb_t pv)
{
    arb_t t, u;
    arb_init(t); arb_init(u);
    arb_mul(t, px, ctx->rx+j, PREC);
    one_minus(u, ctx->rx+j);
    arb_div(t, t, u, PREC);
    arb_set(tail, t);
    arb_mul(t, pv, ctx->rv+j, PREC);
    one_minus(u, ctx->rv+j);
    arb_div(t, t, u, PREC);
    arb_add(tail, tail, t, PREC);
    arb_mul(tail, tail, ctx->divisor_bound, PREC);
    arb_clear(t); arb_clear(u);
}

static slong positive_F(arb_t answer, const context *ctx, slong w)
{
    require(w >= 1 && w <= (ctx->n-1)/2, "positive canonical half interval");
    arb_ptr values = _arb_vec_init(LEVELS);
    arb_ptr px = _arb_vec_init(LEVELS), pv = _arb_vec_init(LEVELS);
    arb_t t, tail, result;
    arb_init(t); arb_init(tail); arb_init(result);
    acb_t q, a, qk, ak, coefficient, denominator, z;
    acb_init(q); acb_init(a); acb_init(qk); acb_init(ak);
    acb_init(coefficient); acb_init(denominator); acb_init(z);
    arb_inv(acb_realref(z), ctx->d, PREC);
    arb_mul_2exp_si(acb_realref(z), acb_realref(z), 1);
    acb_exp_pi_i(q, z, PREC);
    arb_set_si(acb_realref(z), 2*w);
    arb_div(acb_realref(z), acb_realref(z), ctx->A, PREC);
    acb_exp_pi_i(a, z, PREC);
    acb_one(qk); acb_one(ak);
    for (slong j = 0; j < LEVELS; ++j) {
        arb_one(px+j); arb_one(pv+j);
        arb_mul_si(t, ctx->pi, ctx->n-2*w, PREC);
        arb_mul_2exp_si(t, t, -1);
        arb_mul(t, t, ctx->heights+j, PREC);
        arb_div(values+j, t, ctx->AB, PREC);
    }
    slong terms;
    for (terms = 1; terms <= 2000000; ++terms) {
        /* Re-anchor to prevent rectangular complex balls from wrapping up
         * exponentially under a long sequence of unit-circle rotations. */
        if (terms % 32 == 1) {
            arb_inv(acb_realref(z), ctx->d, PREC);
            arb_mul_ui(acb_realref(z), acb_realref(z), (ulong) (2*terms), PREC);
            acb_exp_pi_i(qk, z, PREC);
            arb_set_si(acb_realref(z), 2*w*terms);
            arb_div(acb_realref(z), acb_realref(z), ctx->A, PREC);
            acb_exp_pi_i(ak, z, PREC);
        } else {
            acb_mul(qk, qk, q, PREC); acb_mul(ak, ak, a, PREC);
        }
        acb_sub_ui(denominator, qk, 1, PREC);
        acb_mul(coefficient, qk, ak, PREC);
        acb_div(coefficient, coefficient, denominator, PREC);
        acb_div_ui(coefficient, coefficient, (ulong) terms, PREC);
        if (!acb_is_finite(coefficient)) {
            fprintf(stderr, "n=%ld w=%ld term=%ld\n", ctx->n, w, terms);
            require(0, "finite small-divisor coefficient");
        }
        for (slong j = 0; j < LEVELS; ++j) {
            arb_mul(px+j, px+j, ctx->rx+j, PREC);
            arb_mul(pv+j, pv+j, ctx->rv+j, PREC);
            arb_sub(t, px+j, pv+j, PREC);
            arb_addmul(values+j, acb_realref(coefficient), t, PREC);
        }
        if (terms % 256 == 0) {
            series_tail(tail, ctx, LEVELS-1, px+LEVELS-1, pv+LEVELS-1);
            if (arb_lt(tail, ctx->target)) break;
        }
    }
    require(terms <= 2000000, "term cap reached; no partial value certified");
    for (slong j = 0; j < LEVELS; ++j) {
        series_tail(tail, ctx, j, px+j, pv+j);
        arb_add_error(values+j, tail);
        arb_addmul(result, values+j, ctx->weights+j, PREC);
    }
    arb_add_error(result, ctx->remainder);
    arb_exp(answer, result, PREC);
    require(arb_is_positive(answer), "positive real F enclosure");
    printf("BALL n=%ld w=%ld terms=%ld ", ctx->n, w, terms);
    arb_printn(answer, 45, 0); putchar('\n'); fflush(stdout);
    acb_clear(q); acb_clear(a); acb_clear(qk); acb_clear(ak);
    acb_clear(coefficient); acb_clear(denominator); acb_clear(z);
    arb_clear(t); arb_clear(tail); arb_clear(result);
    _arb_vec_clear(values, LEVELS); _arb_vec_clear(px, LEVELS); _arb_vec_clear(pv, LEVELS);
    return terms;
}

static void set_exact_mag(arb_t target, const mag_t value)
{
    arf_set_mag(arb_midref(target), value);
    mag_zero(arb_radref(target));
}

static void check_correction(const context *ctx, arb_srcptr matrix,
                             const mag_t q_error, const mag_t c_error)
{
    /* Bounds for the actual transparent associators, not just their core.
     * R is the maximum absolute discrete Fourier coefficient of a
     * nonexceptional row, hence its anti-circulant operator norm.
     * M0 >= max(2*d, R / (1-n*epsilon_Q)).
     * q <= (n^2+2)*M0^2*max(epsilon_C,sqrt(d)*epsilon_Q).
     * The unit-channel balance is exact, by Section 90.
     */
    slong n = ctx->n;
    arb_t row, term, eq, ec, denominator, m0, m, q, ratio, margin, threshold, one;
    arb_init(row); arb_init(term); arb_init(eq); arb_init(ec);
    arb_init(denominator); arb_init(m0); arb_init(m); arb_init(q);
    arb_init(ratio); arb_init(margin); arb_init(threshold); arb_init(one);
    arb_one(one);
    mag_t rows, current;
    mag_init(rows); mag_init(current);
    acb_ptr roots = _acb_vec_init(n);
    acb_t z, fourier;
    acb_init(z); acb_init(fourier);
    for (slong k = 0; k < n; ++k) {
        arb_set_si(acb_realref(z), 2*k);
        arb_div_si(acb_realref(z), acb_realref(z), n, PREC);
        acb_exp_pi_i(roots+k, z, PREC);
    }
    for (slong g = 1; g < n; ++g) for (slong k = 0; k < n; ++k) {
        acb_zero(fourier);
        for (slong h = 0; h < n; ++h) {
            acb_addmul_arb(fourier, roots+(k*h)%n, matrix+g*n+h, PREC);
        }
        acb_abs(term, fourier, PREC);
        arb_get_mag(current, term); mag_max(rows, rows, current);
    }
    set_exact_mag(eq, q_error); set_exact_mag(ec, c_error);
    arb_mul_si(denominator, eq, n, PREC); one_minus(denominator, denominator);
    require(arb_is_positive(denominator), "n*epsilon_Q < 1 for inverse bound");
    set_exact_mag(row, rows); arb_div(m0, row, denominator, PREC);
    arb_mul_2exp_si(term, ctx->d, 1); arb_max(m0, m0, term, PREC);
    arb_get_mag(current, m0); set_exact_mag(m0, current);
    arb_mul_2exp_si(m, m0, 1);
    arb_sqrt(term, ctx->d, PREC); arb_mul(term, term, eq, PREC);
    arb_max(q, ec, term, PREC); arb_mul(q, q, m0, PREC);
    arb_mul(q, q, m0, PREC); arb_mul_si(q, q, n*n+2, PREC);
    arb_pow_ui(threshold, m, 14, PREC); arb_mul_ui(threshold, threshold, 870, PREC);
    arb_mul(ratio, threshold, q, PREC); arb_inv(threshold, threshold, PREC);
    arb_pow_ui(margin, m, 3, PREC); arb_mul(margin, margin, q, PREC);
    arb_mul_2exp_si(margin, margin, 1);
    printf("CORRECTION n=%ld M0_upper=", n); arb_printn(m0, 14, 0);
    printf(" full_pentagon_upper="); arb_printn(q, 14, 0);
    printf(" threshold="); arb_printn(threshold, 14, 0); putchar('\n');
    printf("CORRECTION n=%ld sufficient_ratio=", n); arb_printn(ratio, 14, 0);
    printf(" unit_coefficient_change_upper="); arb_printn(margin, 14, 0);
    printf(" result=%s\n", arb_lt(ratio, one) && arb_lt(margin, one)
           ? "VERIFIED_EXISTENCE_BY_CORRECTION" : "SUFFICIENT_BOUND_NOT_MET");
    fflush(stdout);
    _acb_vec_clear(roots, n); acb_clear(z); acb_clear(fourier);
    mag_clear(rows); mag_clear(current);
    arb_clear(row); arb_clear(term); arb_clear(eq); arb_clear(ec);
    arb_clear(denominator); arb_clear(m0); arb_clear(m); arb_clear(q);
    arb_clear(ratio); arb_clear(margin); arb_clear(threshold); arb_clear(one);
}

static void check_izumi(const context *ctx, arb_srcptr F)
{
    slong n = ctx->n;
    arb_ptr W = _arb_vec_init(n), matrix = _arb_vec_init(n*n);
    arb_t root, denominator, sum, t, u, invdelta, bound;
    arb_init(root); arb_init(denominator); arb_init(sum); arb_init(t);
    arb_init(u); arb_init(invdelta); arb_init(bound);
    arb_sqrt(root, ctx->d, PREC);
    arb_sub_ui(denominator, ctx->delta, 1, PREC);
    arb_inv(invdelta, ctx->delta, PREC);
    arb_set_si(W, -1);
    for (slong a = 1; a < n; ++a) {
        arb_div(W+a, F+a, root, PREC);
        if ((a*(a+n)/2) % 2 == 0) arb_neg(W+a, W+a);
    }
    for (slong g = 0; g < n; ++g) for (slong h = 0; h < n; ++h) {
        if (g == 0 && h == 0) arb_sub_ui(t, ctx->delta, 2, PREC);
        else if (g == 0 || h == 0 || g == h) arb_set_si(t, -1);
        else {
            arb_mul(t, W+g, W+(h-g+n)%n, PREC);
            arb_div(t, t, W+h, PREC);
        }
        arb_div(matrix+g*n+h, t, denominator, PREC);
    }
    mag_t worst, current, q_error, c_error;
    mag_init(worst); mag_init(current); mag_init(q_error); mag_init(c_error);
    for (int cubic = 0; cubic <= 1; ++cubic) {
        mag_zero(worst);
        slong count = 0, zero_contained = 0;
        for (slong g = 0; g < n; ++g) for (slong h = 0; h < n; ++h)
        for (slong k = 0; k < (cubic ? n : 1); ++k)
        for (slong l = 0; l < (cubic ? n : 1); ++l) {
            arb_zero(sum);
            for (slong m = 0; m < n; ++m) {
                if (!cubic) arb_mul(t, matrix+((g+m)%n)*n+h, matrix+h*n+m, PREC);
                else {
                    arb_mul(t, matrix+m*n+(g+h)%n, matrix+g*n+(m+k)%n, PREC);
                    arb_mul(t, t, matrix+h*n+(m+l)%n, PREC);
                }
                arb_add(sum, sum, t, PREC);
            }
            if (!cubic) {
                if (g == 0) arb_sub_ui(sum, sum, 1, PREC);
                if (h == 0) arb_add(sum, sum, invdelta, PREC);
            } else {
                arb_mul(u, matrix+((g+l)%n)*n+k, matrix+((h+k)%n)*n+l, PREC);
                arb_sub(sum, sum, u, PREC);
                if (g == 0 && h == 0) arb_add(sum, sum, invdelta, PREC);
            }
            require(arb_is_finite(sum), "finite core residual enclosure");
            if (arb_contains_zero(sum)) ++zero_contained;
            arb_get_mag(current, sum); mag_max(worst, worst, current); ++count;
        }
        arb_zero(bound); arb_add_error_mag(bound, worst);
        printf("ENCLOSURE n=%ld %s count=%ld every residual lies in ", n, cubic ? "C" : "Q", count);
        arb_printn(bound, 12, 0);
        printf(" zero_contained=%ld/%ld\n", zero_contained, count); fflush(stdout);
        mag_set(cubic ? c_error : q_error, worst);
    }
    check_correction(ctx, matrix, q_error, c_error);
    mag_clear(worst); mag_clear(current); mag_clear(q_error); mag_clear(c_error);
    arb_clear(root); arb_clear(denominator); arb_clear(sum); arb_clear(t);
    arb_clear(u); arb_clear(invdelta); arb_clear(bound);
    _arb_vec_clear(W, n); _arb_vec_clear(matrix, n*n);
}

int main(int argc, char **argv)
{
    slong defaults[] = {3, 7, 11};
    for (int index = 0; index < (argc > 1 ? argc-1 : 3); ++index) {
        slong n = argc > 1 ? strtol(argv[index+1], NULL, 10) : defaults[index];
        require(n >= 3 && n % 2 == 1 && n <= 101, "require odd n between 3 and 101");
        context ctx; init_context(&ctx, n);
        printf("PARAMETERS n=%ld precision=%d levels=%d uniform log remainder=", n, PREC, LEVELS);
        arb_printn(ctx.remainder, 12, 0); putchar('\n'); fflush(stdout);
        arb_ptr F = _arb_vec_init(n);
        arb_sqrt(F, ctx.d, PREC);
        for (slong w = 1; w <= (n-1)/2; ++w) positive_F(F+w, &ctx, w);
        for (slong w = (n+1)/2; w < n; ++w) arb_inv(F+w, F+n-w, PREC);
        check_izumi(&ctx, F);
        _arb_vec_clear(F, n); clear_context(&ctx);
    }
    struct rusage usage;
    if (getrusage(RUSAGE_SELF, &usage) == 0)
        printf("Peak RSS: %.1f MiB\n", usage.ru_maxrss/1024.0);
    puts("COMPLETE: certified candidate and residual enclosures; exact Q/C and infinitude are NOT proved.");
    flint_cleanup();
    return 0;
}
