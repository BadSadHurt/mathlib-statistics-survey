---
title: "Variance, covariance expansions, and deviation bounds"
source_module: "Mathlib.Probability.Moments.Variance"
source_path: "Mathlib/Probability/Moments/Variance.lean"
mathlib_commit: "3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6"
lean_toolchain: "leanprover/lean4:v4.36.0-rc1"
last_update: "2026-10-23"
topics:
  - variance
  - covariance
  - square integrability
  - independence
  - Chebyshev inequality
---

# Variance, covariance expansions, and deviation bounds

Mathlib source: [Mathlib.Probability.Moments.Variance](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L1-L544)

Companion Lean file: [VarianceChecks.lean](VarianceChecks.lean)

The review fixes Mathlib at `3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6`, obtained from `master` on 2026-10-23. The survey repository at `6a06fe5890e09d1bf3b090e5d9d41d980c65f9b4` specifies no common Mathlib version. All Mathlib links below refer to this one snapshot. Verification details are in section 5.

## 1. Mathematical result and Lean translation

### Structure and reading conventions

The file develops several connected result families. It defines an extended nonnegative variance and a real variance, relates them to integrals and L² membership, proves transformation and covariance identities, and then derives deviation and boundedness inequalities. The independent-sum results specialize the covariance expansion. The final product-measure results reuse independence and change of variables.

| Source region | Role in the development |
| --- | --- |
| [Lines 53-85][V53-85] | Definitions and four variance notations |
| [Lines 87-184][V87-184] | Almost-everywhere congruence, finiteness, integral representation, zero variance |
| [Lines 186-307][V186-307] | Scaling, second moments, translations, covariance expansions |
| [Lines 311-339][V311-339] | Dirac measures and transport along maps |
| [Lines 341-405][V341-405] | Second-moment bounds and two Chebyshev inequalities |
| [Lines 407-462][V407-462] | Independent sums and finite product measures |
| [Lines 464-507][V464-507] | Bhatia-Davis and Popoviciu bounds |
| [Lines 509-542][V509-542] | Binary products and continuous linear functionals |

The single public import is `Mathlib.Probability.Moments.Covariance`. The two proof imports are `Mathlib.MeasureTheory.Function.LpSeminorm.Prod` and `Mathlib.Probability.Independence.Integrable` ([imports][V6-12]). Thus covariance, expectation notation, and independence already exist before this file. In contrast, `covariance_self`, despite its name and a mention in the covariance module's introductory comment, is proved in **this** file ([lines 197-201][V197-201]).

The following source context applies to the scalar results:

```lean
open MeasureTheory Filter Finset

noncomputable section

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal

namespace ProbabilityTheory
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X Y : Ω → ℝ} {μ : Measure Ω}
```

`Ω : Type*` is an arbitrary type of outcomes; `{mΩ : MeasurableSpace Ω}` supplies its measurable sets. Braces denote implicit arguments. Lean can infer the measurable-space structure from this local context even though the source binder uses braces rather than square brackets. `{μ : Measure Ω}` is an arbitrary measure unless an individual result adds a typeclass assumption. Square brackets such as `[IsProbabilityMeasure μ]` request an instance, which Lean may derive from another instance or a local proof.

`X` and `Y` are real-valued functions, not structures that carry measurability proofs. `μ[X]` means the Bochner integral `∫ ω, X ω ∂μ`; it is an expectation in the usual sense when `μ` is a probability measure and `X` is integrable. `X ^ 2`, `X + Y`, and sums of functions use pointwise operations. `Var[X]` uses the ambient volume measure; that abbreviation does not itself assume a probability measure. This review writes the measure explicitly.

The Lean blocks labeled “source declaration” reproduce complete declaration headers, with proof bodies omitted; the common context above supplies their implicit space, functions, and measure. A header alone is not a runnable example. Complete source proofs are identified separately. The companion contains executable `#check`/`#print` commands and examples, with explicit-argument printing for representative results. No Infoview or tactic-state transcript is inferred from the source.

### 1.1 Finiteness, centered integrals, and zero variance

For an a.e. measurable real function on a finite measure space,

\[
\operatorname{eVar}_\mu(X)<\infty \quad\Longleftrightarrow\quad X\in L^2(\mu).
\]

Source declaration ([lines 126-129][V126-129]):

```lean
theorem evariance_lt_top_iff_memLp [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ) :
    evariance X μ < ∞ ↔ MemLp X 2 μ
```

Here `∞ : ℝ≥0∞`; `MemLp X 2 μ` includes a.e. strong measurability. Finite measure makes every constant, including the totalized integral `μ[X]`, an L² function. If `X` is L², subtracting that constant stays in L², and the L² seminorm formula gives a finite centered-square integral. Conversely, finite extended variance makes `X - μ[X]` L²; adding back the constant makes `X` L². The code implements the reverse implication by contradiction in `evariance_eq_top`, then packages the equivalence ([lines 98-132][V98-132]).

The real integral representation holds under a weaker condition and with no finiteness assumption on the measure:

\[
\operatorname{Var}_\mu(X)=\int (X-\mu[X])^2\,d\mu.
\]

Source declaration ([lines 157-159][V157-159]):

```lean
lemma variance_eq_integral (hX : AEMeasurable X μ) : Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ
```

Both sides are real-valued totalized expressions. The proof uses `integral_toReal`: the pointwise squared extended norm is finite, even when its integral is infinite. This identity does **not** assert integrability of the squared deviation. Section 4 explains the infinite case.

The extended zero criterion also needs only a.e. measurability:

```lean
theorem evariance_eq_zero_iff (hX : AEMeasurable X μ) :
    evariance X μ = 0 ↔ X =ᵐ[μ] fun _ => μ[X]
```

Its proof applies `lintegral_eq_zero_iff'` to the nonnegative squared deviation ([lines 181-184][V181-184]). In words, the extended integral vanishes exactly when `X` equals its integral a.e. This formulation is deliberate for general measures: an arbitrary constant need not equal its unnormalized integral.

For the real variance, the file proves the familiar implication with L² and finite-measure hypotheses:

```lean
lemma ae_eq_integral_of_variance_eq_zero [IsFiniteMeasure μ] (hX : MemLp X 2 μ)
    (h : Var[X; μ] = 0) :
    ∀ᵐ ω ∂μ, X ω = μ[X]
```

The proof rewrites by `variance_eq_integral`, applies the zero-integral criterion for a nonnegative integrable function, and concludes that a square is zero only when the deviation is zero. It explicitly proves integrability after expanding the square using `hX.integrable_sq`, `hX.integrable`, and `integrable_const` ([lines 162-172][V162-172]). Without L² membership, real variance can vanish because of `toReal ∞ = 0`.

### 1.2 Second moments and transformations

On a probability space, for `X ∈ L²(μ)`, expanding the centered square gives

\[
\operatorname{Var}_\mu(X)=\mathbb E_\mu[X^2]-(\mathbb E_\mu X)^2.
\]

Complete source declaration and proof ([lines 226-228][V226-228]):

```lean
theorem variance_eq_sub [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    variance X μ = μ[X ^ 2] - μ[X] ^ 2 := by
  rw [← covariance_self hX.aemeasurable, covariance_eq_sub hX hX, pow_two, pow_two]
```

The proof goes through covariance: replace variance by `cov[X,X;μ]`, apply `covariance_eq_sub`, and rewrite squares as products. The imported [covariance proof](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Covariance.lean#L54-L66) expands the product of centered functions, uses integrability to split the integrals, and uses `μ(Ω)=1` to evaluate the constant term. Thus probability normalization is used in a dependency even though it does not appear explicitly in the short variance proof. For a general finite measure of mass `M`, expansion instead gives `μ[X²] + (M - 2) μ[X]²`; this is a mathematical derivation, not the statement of `variance_eq_sub`.

Two broader statements use a.e. strong measurability, without requiring L²:

```lean
theorem variance_le_expectation_sq [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hm : AEStronglyMeasurable X μ) : variance X μ ≤ μ[X ^ 2]

theorem evariance_def' [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : AEStronglyMeasurable X μ) :
    evariance X μ = (∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂μ) - ENNReal.ofReal (μ[X] ^ 2)
```

In `variance_le_expectation_sq`, the L² branch subtracts a nonnegative square using `variance_eq_sub`. The other branch works with the default-zero Bochner integral: it splits on integrability of `X`, and, when needed, shows integrability of the centered square would contradict failure of L² membership ([lines 341-360][V341-360]). The inequality therefore remains formally true when the usual finite second moment is unavailable.

`evariance_def'` retains an infinite second moment. Subtraction occurs in `ℝ≥0∞`, so it is truncated subtraction; a finite real number is embedded by `ENNReal.ofReal`. The L² branch follows the real identity; otherwise both the extended second moment and extended variance are infinite, and subtracting the finite squared mean leaves infinity ([lines 362-377][V362-377]).

Scaling is valid for **every** measure and function:

```lean
theorem evariance_mul (c : ℝ) (X : Ω → ℝ) (μ : Measure Ω) :
    evariance (fun ω => c * X ω) μ = ENNReal.ofReal (c ^ 2) * evariance X μ

theorem variance_const_mul (c : ℝ) (X : Ω → ℝ) (μ : Measure Ω) :
    variance (fun ω => c * X ω) μ = c ^ 2 * variance X μ
```

The proof uses the unconditional scalar identity for the Bochner integral, rewrites the centered difference as `c * (X - μ[X])`, and takes `c²` out of the nonnegative integral. The real statement follows by `ENNReal.toReal_mul` ([lines 186-210][V186-210]). These identities include `c=0` and the default-zero infinite-variance case.

Translation requires probability normalization:

```lean
lemma variance_add_const [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ) (c : ℝ) :
    Var[fun ω ↦ X ω + c; μ] = Var[X; μ]
```

In the L² branch, integrability allows `μ[X+c]=μ[X]+c`, so the centered functions agree. In the non-L² branch, adding a constant cannot turn `X` into an L² function, since one could subtract the L² constant again. Both real variances are then zero by `variance_of_not_memLp` ([lines 230-241][V230-241]). This explains why the public hypothesis is weaker than L², while its usual statistical interpretation still requires finite variance.

The companion's `affine_variance` combines translation with scaling to obtain `Var[aX+b;μ]=a² Var[X;μ]` under the same measurability and probability hypotheses. It is a new example, not a declaration from the reviewed source.

### 1.3 Covariance expansions and independent sums

For a finite measure and L² functions,

\[
\operatorname{Var}_\mu(X+Y)=\operatorname{Var}_\mu(X)
  +2\operatorname{Cov}_\mu(X,Y)+\operatorname{Var}_\mu(Y),
\]

and for a finite index set `s`,

\[
\operatorname{Var}_\mu\!\left(\sum_{i\in s}X_i\right)
  =\sum_{i\in s}\sum_{j\in s}\operatorname{Cov}_\mu(X_i,X_j).
\]

Source declarations ([binary sum][V263-270], [finite sum][V285-293]):

```lean
lemma variance_add [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Var[X + Y; μ] = Var[X; μ] + 2 * cov[X, Y; μ] + Var[Y; μ]

variable {ι : Type*} {s : Finset ι} {X : (i : ι) → Ω → ℝ}

lemma variance_sum' [IsFiniteMeasure μ] (hX : ∀ i ∈ s, MemLp (X i) 2 μ) :
    Var[∑ i ∈ s, X i; μ] = ∑ i ∈ s, ∑ j ∈ s, cov[X i, X j; μ]
```

`ι` need not be a finite type in the primed statement; only `s : Finset ι` is finite. The notation `∑ i ∈ s, ...` is a bounded finite sum. The unprimed `ProbabilityTheory.variance_sum` instead assumes `[Fintype ι]` and sums over every index. Neither statement assumes independence. The proof changes variance into self-covariance and expands covariance in each argument using the imported finite-sum lemmas. The L² sum is supplied by `memLp_finsetSum'`; its measurability justifies `covariance_self`.

The independent binary-sum theorem has this exact source header:

```lean
nonrec theorem IndepFun.variance_add {X Y : Ω → ℝ} (hX : MemLp X 2 μ)
    (hY : MemLp Y 2 μ) (h : X ⟂ᵢ[μ] Y) : Var[X + Y; μ] = Var[X; μ] + Var[Y; μ]
```

`X ⟂ᵢ[μ] Y` is `ProbabilityTheory.IndepFun X Y μ`, independence under the specified measure. There is **no** `[IsFiniteMeasure μ]` or `[IsProbabilityMeasure μ]` binder ([lines 408-415][V408-415]). The code first treats `X=0` a.e. Otherwise, the imported `MemLp.isProbabilityMeasure_of_indepFun` provides a local probability-measure instance. Covariance expansion then applies, and independence makes the cross covariance zero.

The finite-sum version needs pairwise independence only for distinct indices in `s`. `Set.Pairwise ↑s` is a predicate on the set underlying `s`; it does not assert joint independence or independence of a variable from itself. Its conclusion is a real equality. Complete source declaration and proof ([lines 424-447][V424-447]):

```lean
nonrec theorem IndepFun.variance_sum {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι}
    (hs : ∀ i ∈ s, MemLp (X i) 2 μ)
    (h : Set.Pairwise ↑s fun i j => X i ⟂ᵢ[μ] X j) :
    variance (∑ i ∈ s, X i) μ = ∑ i ∈ s, variance (X i) μ := by
  by_cases h'' : ∀ i ∈ s, X i =ᵐ[μ] 0
  · rw [variance_congr (Y := 0), variance_zero]
    · symm
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      simp [variance_congr (h'' i hi)]
    · have := fun (i : s) ↦ h'' i.1 i.2
      filter_upwards [ae_all_iff.2 this] with ω hω
      simp only [Finset.sum_apply, Pi.zero_apply]
      exact Finset.sum_eq_zero fun i hi ↦ hω ⟨i, hi⟩
  obtain ⟨j, hj1, hj2⟩ := not_forall₂.1 h''
  obtain rfl | h' := s.eq_singleton_or_nontrivial hj1
  · simp
  obtain ⟨k, hk1, hk2⟩ := h'.exists_ne j
  have := (hs j hj1).isProbabilityMeasure_of_indepFun (X j) (X k) (by simp) (by simp) hj2
    (h hj1 hk1 hk2.symm)
  rw [variance_sum' hs]
  refine Finset.sum_congr rfl (fun i hi ↦ ?_)
  rw [← covariance_self (hs i hi).aemeasurable]
  refine Finset.sum_eq_single_of_mem i hi fun j hj1 hj2 ↦ ?_
  exact (h hi hj1 hj2.symm).covariance_eq_zero (hs i hi) (hs j hj1)
```

Here `Ω`, `mΩ`, and `μ` are the common implicit context. The declaration itself binds `ι`, `X`, and `s`, overriding earlier section variables. The full name is `ProbabilityTheory.IndepFun.variance_sum`. `nonrec` controls resolution of the declaration's own short name while its body is elaborated, permitting reference to a previously defined namesake. The actual covariance expansion used in this proof has the distinct name `ProbabilityTheory.variance_sum'`.

The mathematical proof has three cases, all needed to justify the absence of a measure-normalization assumption.

1. If every summand is zero a.e., their finite sum is zero a.e., and all variances vanish. The proof combines the finitely many a.e. statements using `ae_all_iff` on the subtype `i : s`. This includes the empty sum.
2. Otherwise, choose `j ∈ s` with `X j` not zero a.e. If `s={j}`, the identity is simply equality of a singleton sum with its term, and no measure class is needed.
3. If another index `k` exists, pairwise independence of `X j` and `X k`, together with L² membership and nonvanishing of `X j`, implies `μ(Ω)=1`. Now expand the variance as the double covariance sum. Each diagonal covariance is a variance. Each off-diagonal covariance vanishes by `IndepFun.covariance_eq_zero`.

Why does independence force normalization in the third case? The [imported proof](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Independence/Integrable.lean#L31-L51) finds a level set of the nonzero Lᵖ function with measure `a` satisfying `0<a<∞`. Independence with the other variable's whole space gives `a=a·μ(Ω)`. Cancellation in `ℝ≥0∞` gives `μ(Ω)=1`. The finite positive level-set measure follows from the Lᵖ tail bound with exponent neither zero nor infinity. This is how the local `have := ...` supplies the typeclass used by the later covariance theorem.

### 1.4 Chebyshev inequalities

For a positive threshold `c`, integrate the pointwise inequality
`c² 1_{|X-μ[X]|≥c} ≤ |X-μ[X]|²` to obtain

\[
\mu\{|X-\mu[X]|\ge c\}\le \operatorname{eVar}_\mu(X)/c^2.
\]

Source declarations ([extended version][V380-394], [real version][V398-405]):

```lean
theorem meas_ge_le_evariance_div_sq {X : Ω → ℝ} (hX : AEStronglyMeasurable X μ) {c : ℝ≥0}
    (hc : c ≠ 0) : μ {ω | ↑c ≤ |X ω - μ[X]|} ≤ evariance X μ / c ^ 2

theorem meas_ge_le_variance_div_sq [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) {c : ℝ}
    (hc : 0 < c) : μ {ω | c ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (variance X μ / c ^ 2)
```

The first inequality is valid for arbitrary measures, and both sides lie in `ℝ≥0∞`. `c : ℝ≥0` is coerced to `ℝ` inside the event and to `ℝ≥0∞` on the right. Nonzeroness of a nonnegative real is positivity. The proof applies `meas_ge_le_mul_pow_eLpNorm_enorm` with exponent `2` to the centered function, rewrites the L² seminorm as a nonnegative integral, and simplifies its powers and reciprocal. `hX` is passed to the seminorm formula through measurability of the centered function.

The second version assumes a finite measure and L² membership, so `ofReal_variance` converts real variance back to extended variance without losing infinity. `ENNReal.ofReal_div_of_pos` and the conversion of the positive real threshold to `NNReal` finish the proof. The left side is still an extended measure, not a real probability. Only when the measure is a probability measure does it have the usual tail-probability interpretation. No probability-measure assumption is needed for the stated inequality.

### 1.5 Bounds from an almost-everywhere interval constraint

Let `μ` be a probability measure and `a ≤ X ≤ b` a.e. An a.e. measurable bounded real function is L². Writing `m=μ[X]`, nonnegativity of `(b-X)(X-a)` gives

\[
0\le -\mathbb E[X^2]+(a+b)m-ab,
\quad
\operatorname{Var}(X)\le(b-m)(m-a).
\]

This is the Bhatia-Davis bound. Complete source declaration and proof ([lines 468-495][V468-495]):

```lean
lemma variance_le_sub_mul_sub [IsProbabilityMeasure μ] {a b : ℝ} {X : Ω → ℝ}
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hX : AEMeasurable X μ) :
    variance X μ ≤ (b - μ[X]) * (μ[X] - a) := by
  have ha : ∀ᵐ ω ∂μ, a ≤ X ω := h.mono fun ω h => h.1
  have hb : ∀ᵐ ω ∂μ, X ω ≤ b := h.mono fun ω h => h.2
  have hX_int₂ : Integrable (fun ω ↦ -X ω ^ 2) μ :=
    (memLp_of_bounded h hX.aestronglyMeasurable 2).integrable_sq.neg
  have hX_int₁ : Integrable (fun ω ↦ (a + b) * X ω) μ :=
    ((integrable_const (max |a| |b|)).mono' hX.aestronglyMeasurable
      (by filter_upwards [ha, hb] with ω using abs_le_max_abs_abs)).const_mul (a + b)
  have h0 : 0 ≤ -μ[X ^ 2] + (a + b) * μ[X] - a * b :=
    calc
      _ ≤ ∫ ω, (b - X ω) * (X ω - a) ∂μ := by
        apply integral_nonneg_of_ae
        filter_upwards [ha, hb] with ω ha' hb'
        exact mul_nonneg (by linarith : 0 ≤ b - X ω) (by linarith : 0 ≤ X ω - a)
      _ = ∫ ω, -X ω ^ 2 + (a + b) * X ω - a * b ∂μ :=
        integral_congr_ae <| ae_of_all μ fun ω ↦ by ring
      _ = ∫ ω, - X ω ^ 2 + (a + b) * X ω ∂μ - ∫ _, a * b ∂μ :=
        integral_sub (by fun_prop) (integrable_const (a * b))
      _ = ∫ ω, - X ω ^ 2 + (a + b) * X ω ∂μ - a * b := by simp
      _ = - μ[X ^ 2] + (a + b) * μ[X] - a * b := by
        simp [← integral_neg, ← integral_const_mul, integral_add hX_int₂ hX_int₁]
  calc
    _ ≤ (a + b) * μ[X] - a * b - μ[X] ^ 2 := by
      rw [variance_eq_sub (memLp_of_bounded h hX.aestronglyMeasurable 2)]
      linarith
    _ = (b - μ[X]) * (μ[X] - a) := by ring
```

`a` and `b` are arbitrary real parameters. The theorem does not separately assume `a≤b`: the a.e. interval membership on a probability space already rules out an empty interval. `hX` is a measurability assumption, not an integrability assumption. `memLp_of_bounded` derives the required L² membership.

The proof's first two local statements, `ha` and `hb`, extract the lower and upper bounds. `hX_int₂` obtains integrability of `-X²` from boundedness and L². `hX_int₁` bounds `|X|` by `max |a| |b|`, derives integrability, and multiplies by `a+b`. These facts license the later `integral_sub` and `integral_add`; pointwise polynomial algebra alone would not license splitting arbitrary Bochner integrals.

The calculation for `h0` first integrates a nonnegative function, then expands its polynomial using `ring`, and then splits the integrals. The probability-measure instance evaluates the integral of the constant `ab` as `ab`. Finally `variance_eq_sub` changes variance to the second-moment expression, `linarith` rearranges `h0`, and `ring` factors the result. The finite-measure requirements of the integrability lemmas are inferred from the probability instance.

Completing the square yields Popoviciu's bound:

\[
(b-m)(m-a)=\left(\frac{b-a}{2}\right)^2
 -\left(m-\frac{b+a}{2}\right)^2
 \le \left(\frac{b-a}{2}\right)^2.
\]

Complete source declaration and proof ([lines 501-507][V501-507]):

```lean
lemma variance_le_sq_of_bounded [IsProbabilityMeasure μ] {a b : ℝ} {X : Ω → ℝ}
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hX : AEMeasurable X μ) :
    variance X μ ≤ ((b - a) / 2) ^ 2 :=
  calc
    _ ≤ (b - μ[X]) * (μ[X] - a) := variance_le_sub_mul_sub h hX
    _ = ((b - a) / 2) ^ 2 - (μ[X] - (b + a) / 2) ^ 2 := by ring
    _ ≤ ((b - a) / 2) ^ 2 := sub_le_self _ (sq_nonneg _)
```

### 1.6 Where assumptions enter

“Direct” means the proof explicitly uses the hypothesis; “via lemma” means it passes it to a dependency; “instance” means typeclass inference supplies the required structure. The categories can overlap.

| Assumption | Mathematical role | Use in the source proof |
| --- | --- | --- |
| `AEStronglyMeasurable X μ` in finiteness equivalence | Makes the centered norm integral describe L² membership | Via lemma: the seminorm formula in `evariance_eq_top`, [lines 115-120][V111-124] |
| `[IsFiniteMeasure μ]` in finiteness equivalence | Constants are L², allowing centering and uncentering | Instance: `memLp_const` in [lines 99-101][V98-106] and [line 122][V111-124] |
| `AEMeasurable X μ` in `variance_eq_integral` | Measurability of the pointwise squared norm | Via lemma: `integral_toReal`, [lines 157-159][V157-159] |
| `MemLp X 2 μ` in the real zero criterion | Integrability prevents a default-zero integral from masquerading as zero dispersion | Via lemma: `integrable_sq`, `integrable`, [lines 165-172][V162-172] |
| `[IsProbabilityMeasure μ]` in `variance_eq_sub` | The integral of the constant squared mean equals that square | Instance in imported `covariance_eq_sub`, [Covariance lines 54-66](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Covariance.lean#L54-L66) |
| L² hypotheses in covariance expansions | Products of centered functions and finite sums are integrable | Via lemma: covariance bilinearity and `memLp_finsetSum'`, [lines 263-293][V263-293] |
| `[IsFiniteMeasure μ]` in covariance expansions | Constants are L² and L² implies L¹ | Instance in [covariance_add_left](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Covariance.lean#L113-L122) and finite-sum covariance lemmas |
| `hs` in the independent finite sum | L² for normalization and covariance calculations | Via lemma: [lines 441-447][V424-447] |
| `h : Set.Pairwise ...` | Eliminates cross covariances and permits normalization in the nontrivial case | Direct choice of pair at line 442; via `covariance_eq_zero` at line 447 |
| Nonzero summand and distinct second index, derived inside the proof | Avoids cancelling zero or an infinite level-set measure | Direct case split, [lines 428-442][V424-447]; via the normalization lemma |
| `hc` in extended Chebyshev | Division by a positive threshold is legitimate | Direct coercion to `ℝ≥0∞`; via the Lᵖ tail lemma, [lines 382-386][V380-394] |
| L² and finite measure in real Chebyshev | Extended variance is finite and equals `ofReal` of real variance | Via `hX.ofReal_variance_eq`, [line 400][V398-405] |
| `h : ∀ᵐ ω, X ω ∈ Icc a b` in Bhatia-Davis | Nonnegative product and finite moments | Direct `ha`, `hb` and `mul_nonneg`; via `memLp_of_bounded`, [lines 471-493][V468-495] |
| `hX : AEMeasurable X μ` in Bhatia-Davis | Turns a.e. boundedness into integrability | Via `aestronglyMeasurable`, `memLp_of_bounded`, and `mono'` |
| Probability instance in Bhatia-Davis | Normalizes the constant integral and the second-moment identity | Instance: `integrable_const`, `simp` at line 488, `variance_eq_sub` at line 493 |
| Both hypotheses in Popoviciu | Supply Bhatia-Davis; remaining step is real algebra | Via `variance_le_sub_mul_sub`, [line 505][V501-507] |

No assumption is claimed redundant merely because its name is absent from tactic text.

## 2. Core definitions

### Extended and real variance: defined in this file

For a real function `X`, put `m=∫X dμ`. Then

\[
\operatorname{eVar}_\mu(X)=\int^-\|X-m\|_e^2\,d\mu\in[0,\infty],
\qquad
\operatorname{Var}_\mu(X)=\operatorname{toReal}(\operatorname{eVar}_\mu(X))\in\mathbb R.
\]

Exact source definitions with their local parameter directives ([lines 53-64][V53-64]):

```lean
variable (X μ) in
-- TODO: Consider if `evariance` or `eVariance` is better. Also,
-- consider `eVariationOn` in `Mathlib.Analysis.BoundedVariation`.
/-- The `ℝ≥0∞`-valued variance of a real-valued random variable defined as the Lebesgue integral of
`‖X - 𝔼[X]‖^2`. -/
def evariance : ℝ≥0∞ := ∫⁻ ω, ‖X ω - μ[X]‖ₑ ^ 2 ∂μ

variable (X μ) in
/-- The `ℝ`-valued variance of a real-valued random variable defined by applying `ENNReal.toReal`
to `evariance`. -/
@[wikidata Q175199]
def variance : ℝ := (evariance X μ).toReal
```

`variable (X μ) in` makes both arguments explicit for that declaration. With the enclosing context, the type of each definition has implicit `{Ω : Type*}` and `{mΩ : MeasurableSpace Ω}`, followed by explicit `(X : Ω → ℝ)` and `(μ : Measure Ω)`. `‖·‖ₑ` is the extended nonnegative norm; for a real input its square agrees with `ENNReal.ofReal` of the real square. The bridge is unconditional:

```lean
variable (X μ) in
theorem evariance_eq_lintegral_ofReal :
    evariance X μ = ∫⁻ ω, ENNReal.ofReal ((X ω - μ[X]) ^ 2) ∂μ := by
  simp [evariance, ← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
```

The four scoped notations are `eVar[X; μ]`, `Var[X; μ]`, and their volume-measure versions `eVar[X]`, `Var[X]` ([lines 66-85][V66-85]). The namespace is `ProbabilityTheory`. `open scoped ProbabilityTheory` enables its notations without bringing all its declaration names into scope; `open ProbabilityTheory` also makes the declaration names available.

### Integration and measurability: imported concepts

Expectation notation is defined in [Probability.Notation](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Notation.lean#L46-L56). It abbreviates integration and adds no assumptions. The [Bochner integral definition](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean#L152-L170) returns zero when its integrability condition fails; for the complete real codomain this is recorded by [integral_undef](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean#L200-L207).

`MemLp X 2 μ` expresses L² membership for a function, without first taking an equivalence class in the `Lp` space. Its exact definition is ([LpSeminorm.Defs](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean#L150-L156)). Besides the binders shown below, the source context supplies `{α ε : Type*}`, `{m0 : MeasurableSpace α}`, and `[ENorm ε]`; the reviewed use specializes ε to ℝ:

```lean
def MemLp [TopologicalSpace ε] (f : α → ε) (p : ℝ≥0∞) (μ : Measure α := by volume_tac) : Prop :=
  eLpNorm f p μ < ∞
```

In this snapshot, `eLpNorm` is defined to be infinity when a.e. strong measurability fails; thus finiteness already entails measurability ([definition and consequence](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean#L75-L109), [`MemLp.aestronglyMeasurable`](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean#L159-L167)). For the real-valued functions here, `MemLp X 2 μ` means a.e. measurability and a finite integral of `|X|²`. The general definition also supports other exponents and normed codomains; those features are not needed for this review. `Integrable X μ` similarly combines a.e. strong measurability with finite integral of the norm. The companion prints both definitions and checks their fully instantiated uses.

The exact `Integrable` definition is below. Its enclosing context provides `{ε : Type*}`, `[TopologicalSpace ε]`, and `[ContinuousENorm ε]` ([source](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean#L47-L60)). `HasFiniteIntegral` requires a finite nonnegative integral of the norm, which for real functions is `∫⁻ ω, ‖X ω‖ₑ ∂μ < ∞`.

```lean
def Integrable {α} {_ : MeasurableSpace α} (f : α → ε)
    (μ : Measure α := by volume_tac) : Prop :=
  AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ
```

`AEMeasurable X μ` says there exists a measurable function equal to `X` a.e. `AEStronglyMeasurable` uses a strongly measurable representative. For real-valued functions the file passes between them using `.aemeasurable` and `.aestronglyMeasurable`. These conversions should not be presumed for arbitrary codomains without the relevant topological hypotheses. The notation `X =ᵐ[μ] Y` means that the equality holds outside a μ-null set; `∀ᵐ ω ∂μ, P ω` is the corresponding a.e. predicate. These notions let the variance API depend only on the a.e. class of `X`, as proved by `variance_congr` and `evariance_congr`.

Definitions: [AEMeasurable](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean#L404-L412), [AEStronglyMeasurable](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean#L60-L70), and [Integrable](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean#L50-L62).

### Covariance and independence: imported concepts

For the same totalized means, covariance is a real integral:

\[
\operatorname{Cov}_\mu(X,Y)=\int(X-\mu[X])(Y-\mu[Y])\,d\mu.
\]

Exact definition in [Moments.Covariance](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Covariance.lean#L40-L48), under the same measurable-space and measure context:

```lean
noncomputable def covariance (X Y : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∫ ω, (X ω - μ[X]) * (Y ω - μ[Y]) ∂μ
```

The present file supplies `covariance_self (hX : AEMeasurable X μ)`. Covariance bilinearity, finite-sum expansion, and independence implying zero covariance come from the imported module. This direction of dependency avoids using variance to define covariance.

`IndepFun X Y μ` is defined through independence of the measurable structures pulled back by the functions. For real-valued functions it implies the usual factorization
`μ(X⁻¹(A) ∩ Y⁻¹(B)) = μ(X⁻¹(A)) * μ(Y⁻¹(B))` for measurable real sets `A,B`. The definition itself does not carry a probability-measure hypothesis. See [Independence.Basic](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Independence/Basic.lean#L130-L153); this explains why the normalization argument in section 1.3 is meaningful.

## 3. Other public declarations

The following inventory includes the definitions, the core results already discussed, supporting lemmas, and protected aliases. Every name is fully qualified. “Any μ” means no finite/probability-measure instance is required. “L²” always includes a.e. strong measurability; “AE” in a condition refers to measurability under the stated measure. All variances are real unless `evariance` or `eVar` is written.

### Definition, representation, and degeneracy

| Full declaration name | Mathematical meaning | Key conditions | Typical use | Source |
| --- | --- | --- | --- | --- |
| `ProbabilityTheory.evariance`; `ProbabilityTheory.variance` | Extended centered-square integral; its `toReal` | Any μ and real function | Choose codomain | [53-64][V53-64] |
| `ProbabilityTheory.evariance_congr`; `ProbabilityTheory.variance_congr` | A.e. equality preserves variance | `X =ᵐ[μ] Y` | Replace representatives | [87-93][V87-93] |
| `ProbabilityTheory.evariance_zero_measure`; `ProbabilityTheory.variance_zero_measure` | Zero measure gives zero | Any X | Degenerate measure | [95-96][V95-96] |
| `ProbabilityTheory.evariance_lt_top`; `ProbabilityTheory.evariance_ne_top` | Extended variance is finite | Finite μ, L² X | Permit `toReal` conversion | [98-109][V98-109] |
| `ProbabilityTheory.evariance_eq_top` | Non-L² implies infinite extended variance | Finite μ, AE strong measurability | Diagnose infinite moments | [111-124][V111-124] |
| `ProbabilityTheory.evariance_lt_top_iff_memLp`; `ProbabilityTheory.evariance_eq_top_iff` | Finiteness iff L²; infinity iff not L² | Finite μ, AE strong measurability | Rewrite finiteness goals | [126-132][V126-132] |
| `ProbabilityTheory.variance_of_not_memLp`; `ProbabilityTheory.memLp_two_of_variance_ne_zero` | Non-L² real variance is zero; nonzero real variance implies L² | Finite μ, AE strong measurability | Handle totalization | [134-141][V134-141] |
| `ProbabilityTheory.ofReal_variance` | `ofReal (Var X) = eVar X` | Finite μ, L² X | Transfer real bounds | [143-146][V143-146] |
| `MeasureTheory.MemLp.evariance_lt_top`; `MeasureTheory.MemLp.evariance_ne_top`; `MeasureTheory.MemLp.ofReal_variance_eq` | Protected aliases of the finiteness and conversion lemmas | Same as originals | Dot notation on an L² proof | [148-150][V148-150] |
| `ProbabilityTheory.evariance_eq_lintegral_ofReal` | Replace extended norm square by `ofReal` of a real square | Any μ, any X | Compare integral conventions | [152-155][V152-155] |
| `ProbabilityTheory.variance_eq_integral` | Real integral of centered square | AE measurable X, any μ | Use Bochner integration | [157-159][V157-159] |
| `ProbabilityTheory.ae_eq_integral_of_variance_eq_zero` | Zero real variance implies X equals its integral a.e. | Finite μ, L² X, zero variance | Prove degeneracy | [162-172][V162-172] |
| `ProbabilityTheory.variance_of_integral_eq_zero` | Variance is the second-moment integral if the integral of X is zero | AE measurable X, any μ | Centered variables | [174-176][V174-176] |
| `ProbabilityTheory.evariance_zero`; `ProbabilityTheory.variance_zero` | Zero function has zero variance | Any μ | Simplification | [178-184][V178-184], [193-195][V193-195] |
| `ProbabilityTheory.evariance_eq_zero_iff` | Zero extended variance iff X equals its integral a.e. | AE measurable X, any μ | Nonnegative integral criterion | [181-184][V181-184] |
| `ProbabilityTheory.covariance_self` | Self-covariance is variance | AE measurable X, any μ | Enter covariance API | [197-201][V197-201] |
| `ProbabilityTheory.variance_nonneg` | Real variance is nonnegative | Any μ, any X | Order arguments | [203-205][V203-205] |
| `ProbabilityTheory.variance_eq_sub` | Second moment minus squared mean | Probability μ, L² X | Moment calculations | [226-228][V226-228] |

### Transformations, addition, and transport

| Full declaration name | Mathematical meaning | Key conditions | Typical use | Source |
| --- | --- | --- | --- | --- |
| `ProbabilityTheory.evariance_mul` | Multiply extended variance by `ofReal(c²)` | Real c, any μ/X | Extended scaling | [186-191][V186-191] |
| `ProbabilityTheory.variance_const_mul`; `ProbabilityTheory.variance_mul_const`; `ProbabilityTheory.variance_smul` | Multiply variance by c², in function or scalar-action syntax | Real c, any μ/X | Rescale variables | [207-218][V207-218] |
| `ProbabilityTheory.variance_smul'` | Scalar-action variant `Var[c • X] = c² • Var[X]` | `[CommSemiring A] [Algebra A ℝ]`, c in A; any μ/X | Scalars acting through an algebra map | [220-224][V220-224] |
| `ProbabilityTheory.variance_add_const`; `ProbabilityTheory.variance_const_add`; `ProbabilityTheory.variance_sub_const`; `ProbabilityTheory.variance_const_sub` | Translation/reflection by a constant preserves variance | Probability μ, AE strong measurability | Center or change location | [230-245][V230-245], [254-261][V254-261] |
| `ProbabilityTheory.variance_fun_neg`; `ProbabilityTheory.variance_neg` | Negation preserves variance | Any μ/X | Change sign | [247-252][V247-252] |
| `ProbabilityTheory.variance_add`; `ProbabilityTheory.variance_fun_add` | Binary sum includes twice covariance | Finite μ, both functions L² | Dependent sums | [263-274][V263-274] |
| `ProbabilityTheory.variance_sub`; `ProbabilityTheory.variance_fun_sub` | Binary difference subtracts twice covariance | Finite μ, both functions L² | Contrasts | [276-283][V276-283] |
| `ProbabilityTheory.variance_sum'`; `ProbabilityTheory.variance_fun_sum'` | Finset sum is the double covariance sum | Finite μ, L² on s | Finite collections | [287-293][V287-293], [299-302][V299-302] |
| `ProbabilityTheory.variance_sum`; `ProbabilityTheory.variance_fun_sum` | Sum over all indices is the double covariance sum | Finite μ, `[Fintype ι]`, each function L² | Finite index types | [295-307][V295-307] |
| `ProbabilityTheory.variance_dirac` | A Dirac measure gives zero variance | `[MeasurableSingletonClass Ω]`, any X | Deterministic distribution | [311-315][V311-315] |
| `ProbabilityTheory.variance_map` | `Var[X; μ.map Y] = Var[X ∘ Y; μ]` | X AE measurable under map; Y AE measurable under μ | Work with the distribution | [317-325][V317-325] |
| `MeasureTheory.MeasurePreserving.variance_fun_comp` | Composition with a measure-preserving map preserves variance | `MeasurePreserving X μ ν`, f AE measurable under ν | Change sample space | [327-331][V327-331] |
| `ProbabilityTheory.variance_map_equiv` | Map formula for a measurable equivalence | `Y : Ω' ≃ᵐ Ω`, any X/μ | Relabel a measurable space | [333-336][V333-336] |
| `ProbabilityTheory.variance_id_map` | Variance of identity under the law of X is variance of X | X AE measurable under μ | Distributional reasoning | [338-339][V338-339] |

### Bounds, independent sums, and products

| Full declaration name | Mathematical meaning | Key conditions | Typical use | Source |
| --- | --- | --- | --- | --- |
| `ProbabilityTheory.variance_le_expectation_sq` | Real variance ≤ real second-moment integral | Probability μ, AE strong measurability | Upper bounds; beware totalization | [341-360][V341-360] |
| `ProbabilityTheory.evariance_def'` | Extended second moment minus embedded squared mean | Probability μ, AE strong measurability | Allow infinite second moment | [362-377][V362-377] |
| `ProbabilityTheory.meas_ge_le_evariance_div_sq` | Extended Chebyshev bound | Any μ, AE strong measurability, nonzero NNReal threshold | Tail control without L² | [380-394][V380-394] |
| `ProbabilityTheory.meas_ge_le_variance_div_sq` | Chebyshev with real variance embedded by `ofReal` | Finite μ, L² X, positive real threshold | Finite-variance tail control | [398-405][V398-405] |
| `ProbabilityTheory.IndepFun.variance_add`; `ProbabilityTheory.IndepFun.variance_fun_add` | Independent binary sum has additive variance | Both L², `X ⟂ᵢ[μ] Y`; no measure-class binder | Independent terms | [408-420][V408-420] |
| `ProbabilityTheory.IndepFun.variance_sum` | Pairwise independent finite sum has additive variance | L² on s, pairwise independence on s; no measure-class binder | Finite independent sums | [424-447][V424-447] |
| `ProbabilityTheory.variance_sum_pi` | Coordinate-function sum under `Measure.pi μ` has additive variance | Finite index type, each μᵢ probability, each Xᵢ L² | Independent product construction | [449-462][V449-462] |
| `ProbabilityTheory.variance_le_sub_mul_sub` | Bhatia-Davis bound `(b-m)(m-a)` | Probability μ, AE measurable X, X in `[a,b]` a.e. | Bounded variables with known mean | [468-495][V468-495] |
| `ProbabilityTheory.variance_le_sq_of_bounded` | Popoviciu bound `((b-a)/2)²` | Same as Bhatia-Davis | Bound without knowing the mean | [501-507][V501-507] |
| `ProbabilityTheory.variance_add_prod` | `Var[X(p.1)+Y(p.2); μ.prod ν] = Var[X;μ]+Var[Y;ν]` | Both measures probability; X and Y L² under respective measures | Two independent coordinates | [509-520][V509-520] |
| `ProbabilityTheory.variance_dual_prod'` | Variance of a continuous linear functional on a product splits along its two restrictions | Real normed spaces E,F with measurable structures; probability μ,ν; both restrictions L² | Linear functionals of product variables | [524-535][V524-535] |
| `ProbabilityTheory.variance_dual_prod` | Same conclusion, deriving integrability of the restrictions | Same spaces/measures; `MemLp id 2 μ` and `MemLp id 2 ν` | L² vector-valued inputs | [524-540][V524-540] |

The last two results still return the variance of a **real-valued** function. They do not define a vector-valued variance. `StrongDual ℝ (E × F)` is the space of continuous real linear functionals on the product; `.inl` and `.inr` are the continuous linear inclusions. The source's section context is:

```lean
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {mE : MeasurableSpace E}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {mF : MeasurableSpace F}
  {μ : Measure E} [IsProbabilityMeasure μ] {ν : Measure F} [IsProbabilityMeasure ν]
```

No Borel compatibility or completeness assumption is added in this section. The hypotheses already supply the necessary L² facts. `variance_dual_prod'` writes a linear functional as the sum of its restrictions and uses `variance_add_prod`; the unprimed result obtains L² of those restrictions via `ContinuousLinearMap.comp_memLp'`. For the earlier `Prod` section, the context separately requires measurable spaces `Ω, Ω'`, probability measures `μ,ν`, and real functions on their respective domains ([lines 511-516][V511-516]).

## 4. Boundary conditions

### Total definitions and infinite values

Neither variance definition asks for measurability or integrability. This makes expressions available for all real functions, but the usual statistical meaning needs the appropriate hypotheses. `ENNReal.toReal` sends both zero and infinity to zero ([source](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Basic/ENNReal/Basic.lean#L281-L286)). On a finite measure space, an a.e. strongly measurable function outside L² therefore has real variance zero by `variance_of_not_memLp`, while its extended variance is infinite. A zero real variance alone cannot certify constancy.

If `X` is not integrable, `μ[X]=0` by `integral_undef`. Thus extended variance is then the nonnegative second-moment integral centered at the default zero. If `X` is integrable but its centered square is not integrable, `variance_eq_integral` still holds: both real-valued sides use a zero default. If measurability is absent, the unconditional definition still exists, but the finiteness equivalence, integral representation, and zero criterion cannot simply be invoked. No claim about arbitrary nonmeasurable functions is inferred from those lemmas.

### Finite measure is not probability normalization

`μ[X]` is an unnormalized integral. As a derived calculation, for finite mass `M=μ(Ω)` and constant `X=c`, the definition gives `Varμ(c)=M(c-Mc)²`. For example, mass `M=2` and `c=1` gives `2`, not zero. This explains why the file does not state a universal constant-variance-zero theorem for finite measures. Under a probability measure, constants do have zero variance; the companion derives that fact from `variance_eq_integral`. General translations likewise need normalization, while scaling is valid unconditionally.

### Zero measures, point masses, and empty sums

The two zero-measure lemmas and two zero-function lemmas are explicit. `variance_dirac` requires measurable singletons but does not require measurability of `X`, since every real function is a.e. measurable under that Dirac measure. Empty finite sums reduce to the zero function. The independent finite-sum proof covers them in its all-zero branch; its singleton branch also avoids assuming normalization. A probability measure on an empty sample space is impossible, so theorems with that typeclass do not introduce an unmentioned nonempty-space case.

### Thresholds and intervals

Both Chebyshev statements exclude a zero threshold. Extended Chebyshev remains true with infinite extended variance, where it gives no finite tail bound. Bhatia-Davis and Popoviciu allow `a=b`; the bound is zero. If `a>b`, the a.e. interval hypothesis cannot hold on a probability space. No strict endpoint inequality is required.

### Measure transport

`variance_map` needs a.e. measurability of the map and observable; `variance_map_equiv` uses the stronger structure of a measurable equivalence and accepts an arbitrary observable. Omitting these distinctions would overstate the general map theorem.

## 5. Discussion

The file's main design choice is to retain infinite dispersion in `evariance`, then expose a convenient real-valued interface through `variance`. L² lemmas connect the two. Covariance is the algebraic interface for sums, while Lᵖ bounds supply Chebyshev. Boundedness provides L² automatically in the final inequalities. The product results combine these interfaces with measure-preserving coordinate projections.

For a reader following a proof, useful next steps are to inspect the exact covariance dependency at a rewrite, check which measure class is inferred, and determine whether a real-valued expression could be using its default zero. The companion includes an affine transformation example and a weighted covariance-sum example to exercise these interfaces. No change to the Mathlib implementation or weakening of a hypothesis is proposed here.

### Reproducible checks

Verified on 2026-10-23 with Lean `4.36.0-rc1`, Windows x86_64, compiler commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`. The companion elaborated successfully: **exit code 0, no warnings or errors**. All 64 public names and aliases resolved, and every example in the file passed. No proof placeholder or new axiom was used.

The local validation used a source archive addressed by the full Mathlib SHA, the snapshot's unchanged Lake manifest, and dependencies checked out at the manifest's exact revisions. The target cache command downloaded and decompressed 3,021 files successfully. The Mathlib implementation and the survey repository's dependency configuration were not changed.

The survey repository has no Lake project. Use an independent Mathlib checkout or source snapshot at the pinned commit with its unchanged `lean-toolchain` and `lake-manifest.json`:

```text
lake exe cache get Mathlib/Probability/Moments/Variance.lean
lake env lean --version
lake env lean /absolute/path/to/Mathlib/Probability/Moments/Variance/VarianceChecks.lean
```

`VarianceChecks.lean` imports only `Mathlib.Probability.Moments.Variance`. It checks every named public declaration in the inventory, prints the definitions, exposes implicit parameters for selected theorems, and checks examples for affine transformations, covariance sums, independent sums, Chebyshev, boundedness, and boundary cases. Source excerpts in this document are quoted from the fixed snapshot; the newly written examples are identified in the companion. There is no claimed interactive proof-state transcript.

For this run, the final command, from the independent Mathlib source directory, was:

```text
lake env lean '../mathlib-statistics-survey/Mathlib/Probability/Moments/Variance/VarianceChecks.lean'
```

Selected **actual terminal output** from the companion's ordinary `#check` commands (the proof examples themselves produce no messages on success):

```text
ProbabilityTheory.evariance.{u_1} {Ω : Type u_1} {mΩ : MeasurableSpace Ω} (X : Ω → ℝ) (μ : Measure Ω) : ℝ≥0∞
ProbabilityTheory.variance.{u_1} {Ω : Type u_1} {mΩ : MeasurableSpace Ω} (X : Ω → ℝ) (μ : Measure Ω) : ℝ
ProbabilityTheory.variance_eq_sub.{u_1} {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ} (hX : MemLp X 2 μ) : Var[X; μ] = ∫ (x : Ω), (X ^ 2) x ∂μ - (∫ (x : Ω), X x ∂μ) ^ 2
ProbabilityTheory.IndepFun.variance_sum.{u_1, u_3} {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {ι : Type u_3} {X : ι → Ω → ℝ} {s : Finset ι} (hs : ∀ i ∈ s, MemLp (X i) 2 μ)
  (h : (↑s).Pairwise fun i j => X i ⟂ᵢ[μ] X j) : Var[∑ i ∈ s, X i; μ] = ∑ i ∈ s, Var[X i; μ]
ENNReal.toReal_top : ∞.toReal = 0
```

The mathematical calculations for a general finite mass in sections 1.2 and 4 are explanatory derivations. They are not advertised as additional compiled Mathlib theorems.

## 6. References

1. [Variance.lean, fixed snapshot](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L1-L544), the primary source for the definitions, statements, and proofs reviewed here.
2. [Covariance.lean](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Covariance.lean#L40-L66), with [bilinearity](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Covariance.lean#L113-L127), [finite sums](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Covariance.lean#L227-L297), and [independence](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Covariance.lean#L324-L332). These are dependencies, not a separate file review.
3. [Independence.Integrable](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Independence/Integrable.lean#L12-L51), the normalization lemma used by independent-sum proofs.
4. [LpSeminorm.Defs](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean#L150-L156) and [Bochner.Basic](https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean#L152-L207), for the integrability and totalization conventions.

The survey README names *Foundations of Modern Probability* as background. No edition-specific theorem or page is cited here because none was verified for this review; the mathematical statements and proof attributions above are supported by the pinned source.

[V6-12]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L6-L12

[V53-85]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L53-L85

[V53-64]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L53-L64

[V66-85]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L66-L85

[V87-93]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L87-L93

[V87-184]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L87-L184

[V95-96]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L95-L96

[V98-109]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L98-L109

[V98-106]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L98-L106

[V98-132]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L98-L132

[V111-124]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L111-L124

[V126-129]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L126-L129

[V126-132]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L126-L132

[V134-141]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L134-L141

[V143-146]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L143-L146

[V148-150]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L148-L150

[V152-155]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L152-L155

[V157-159]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L157-L159

[V162-172]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L162-L172

[V174-176]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L174-L176

[V178-184]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L178-L184

[V181-184]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L181-L184

[V186-210]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L186-L210

[V186-307]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L186-L307

[V186-191]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L186-L191

[V193-195]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L193-L195

[V197-201]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L197-L201

[V203-205]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L203-L205

[V207-218]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L207-L218

[V220-224]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L220-L224

[V226-228]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L226-L228

[V230-241]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L230-L241

[V230-245]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L230-L245

[V247-252]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L247-L252

[V254-261]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L254-L261

[V263-293]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L263-L293

[V263-270]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L263-L270

[V263-274]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L263-L274

[V276-283]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L276-L283

[V285-293]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L285-L293

[V287-293]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L287-L293

[V295-307]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L295-L307

[V299-302]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L299-L302

[V311-315]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L311-L315

[V311-339]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L311-L339

[V317-325]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L317-L325

[V327-331]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L327-L331

[V333-336]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L333-L336

[V338-339]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L338-L339

[V341-360]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L341-L360

[V341-405]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L341-L405

[V362-377]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L362-L377

[V380-394]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L380-L394

[V398-405]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L398-L405

[V407-462]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L407-L462

[V408-415]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L408-L415

[V408-420]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L408-L420

[V424-447]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L424-L447

[V449-462]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L449-L462

[V464-507]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L464-L507

[V468-495]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L468-L495

[V501-507]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L501-L507

[V509-520]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L509-L520

[V509-542]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L509-L542

[V511-516]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L511-L516

[V524-540]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L524-L540

[V524-535]: https://github.com/leanprover-community/mathlib4/blob/3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6/Mathlib/Probability/Moments/Variance.lean#L524-L535
