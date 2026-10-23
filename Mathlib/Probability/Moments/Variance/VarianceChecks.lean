import Mathlib.Probability.Moments.Variance

/-!
Companion to Variance.md.
Mathlib: 3d14fd9a313ac35ed4b5c653ed5d99157c9e29f6
Toolchain: leanprover/lean4:v4.36.0-rc1
Review date: 2026-10-23
Run from that Mathlib environment: lake env lean <absolute-path-to-this-file>
Only the target module is imported. No additional axioms or proof placeholders.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory ENNReal NNReal BigOperators

-- Public declarations defined in the reviewed file, including protected aliases.
#check ProbabilityTheory.evariance
#check ProbabilityTheory.variance
#check ProbabilityTheory.evariance_congr
#check ProbabilityTheory.variance_congr
#check ProbabilityTheory.evariance_zero_measure
#check ProbabilityTheory.variance_zero_measure
#check ProbabilityTheory.evariance_lt_top
#check ProbabilityTheory.evariance_ne_top
#check ProbabilityTheory.evariance_eq_top
#check ProbabilityTheory.evariance_lt_top_iff_memLp
#check ProbabilityTheory.evariance_eq_top_iff
#check ProbabilityTheory.variance_of_not_memLp
#check ProbabilityTheory.memLp_two_of_variance_ne_zero
#check ProbabilityTheory.ofReal_variance
#check MeasureTheory.MemLp.evariance_lt_top
#check MeasureTheory.MemLp.evariance_ne_top
#check MeasureTheory.MemLp.ofReal_variance_eq
#check ProbabilityTheory.evariance_eq_lintegral_ofReal
#check ProbabilityTheory.variance_eq_integral
#check ProbabilityTheory.ae_eq_integral_of_variance_eq_zero
#check ProbabilityTheory.variance_of_integral_eq_zero
#check ProbabilityTheory.evariance_zero
#check ProbabilityTheory.evariance_eq_zero_iff
#check ProbabilityTheory.evariance_mul
#check ProbabilityTheory.variance_zero
#check ProbabilityTheory.covariance_self
#check ProbabilityTheory.variance_nonneg
#check ProbabilityTheory.variance_const_mul
#check ProbabilityTheory.variance_mul_const
#check ProbabilityTheory.variance_smul
#check ProbabilityTheory.variance_smul'
#check ProbabilityTheory.variance_eq_sub
#check ProbabilityTheory.variance_add_const
#check ProbabilityTheory.variance_const_add
#check ProbabilityTheory.variance_fun_neg
#check ProbabilityTheory.variance_neg
#check ProbabilityTheory.variance_sub_const
#check ProbabilityTheory.variance_const_sub
#check ProbabilityTheory.variance_add
#check ProbabilityTheory.variance_fun_add
#check ProbabilityTheory.variance_sub
#check ProbabilityTheory.variance_fun_sub
#check ProbabilityTheory.variance_sum'
#check ProbabilityTheory.variance_sum
#check ProbabilityTheory.variance_fun_sum'
#check ProbabilityTheory.variance_fun_sum
#check ProbabilityTheory.variance_dirac
#check ProbabilityTheory.variance_map
#check MeasureTheory.MeasurePreserving.variance_fun_comp
#check ProbabilityTheory.variance_map_equiv
#check ProbabilityTheory.variance_id_map
#check ProbabilityTheory.variance_le_expectation_sq
#check ProbabilityTheory.evariance_def'
#check ProbabilityTheory.meas_ge_le_evariance_div_sq
#check ProbabilityTheory.meas_ge_le_variance_div_sq
#check ProbabilityTheory.IndepFun.variance_add
#check ProbabilityTheory.IndepFun.variance_fun_add
#check ProbabilityTheory.IndepFun.variance_sum
#check ProbabilityTheory.variance_sum_pi
#check ProbabilityTheory.variance_le_sub_mul_sub
#check ProbabilityTheory.variance_le_sq_of_bounded
#check ProbabilityTheory.variance_add_prod
#check ProbabilityTheory.variance_dual_prod'
#check ProbabilityTheory.variance_dual_prod

-- Expose every binder, including section parameters and typeclass arguments.
set_option pp.explicit true in
#check @ProbabilityTheory.variance_eq_sub
set_option pp.explicit true in
#check @ProbabilityTheory.variance_sum'
set_option pp.explicit true in
#check @ProbabilityTheory.IndepFun.variance_sum
set_option pp.explicit true in
#check @ProbabilityTheory.meas_ge_le_variance_div_sq
set_option pp.explicit true in
#check @ProbabilityTheory.variance_dual_prod

#print ProbabilityTheory.evariance
#print ProbabilityTheory.variance
#print ProbabilityTheory.covariance
#print MeasureTheory.MemLp
#print MeasureTheory.Integrable
#check MeasureTheory.integral_undef
#check ENNReal.toReal_top

namespace VarianceSurveyChecks

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {X Y : Ω → ℝ}

-- Definition, codomain, and boundary checks.
example : Var[X; μ] = (eVar[X; μ]).toReal := rfl
example : 0 ≤ Var[X; μ] := variance_nonneg X μ
example : Var[X; (0 : Measure Ω)] = 0 := variance_zero_measure
example (hX : AEMeasurable X μ) :
    Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ := variance_eq_integral hX
example [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ)
    (hn : ¬ MemLp X 2 μ) : Var[X; μ] = 0 := variance_of_not_memLp hX hn
example [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hv : Var[X; μ] = 0) :
    ∀ᵐ ω ∂μ, X ω = μ[X] := ae_eq_integral_of_variance_eq_zero hX hv
example [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) :
    Var[X; μ] = μ[X ^ 2] - μ[X] ^ 2 := variance_eq_sub hX

-- A new composition of translation and scaling, requiring no L² hypothesis.
theorem affine_variance [IsProbabilityMeasure μ]
    (hX : AEStronglyMeasurable X μ) (a b : ℝ) :
    Var[fun ω ↦ a * X ω + b; μ] = a ^ 2 * Var[X; μ] := by
  rw [variance_add_const (hX.const_mul a) b, variance_const_mul]

-- Constants under probability measures, derived from the imported API.
example [IsProbabilityMeasure μ] (c : ℝ) : Var[fun _ : Ω ↦ c; μ] = 0 := by
  rw [variance_eq_integral aemeasurable_const]
  simp

-- Covariance terms are retained; independence is not assumed.
example [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Var[X + Y; μ] = Var[X; μ] + 2 * cov[X, Y; μ] + Var[Y; μ] :=
  variance_add hX hY

theorem weighted_sum_variance [IsFiniteMeasure μ] {ι : Type*}
    (s : Finset ι) (Z : ι → Ω → ℝ) (w : ι → ℝ)
    (hZ : ∀ i ∈ s, MemLp (Z i) 2 μ) :
    Var[∑ i ∈ s, w i • Z i; μ] =
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * cov[Z i, Z j; μ] := by
  rw [variance_sum' (fun i hi ↦ (hZ i hi).const_smul (w i))]
  simp_rw [covariance_smul_left, covariance_smul_right, mul_assoc]

example {ι : Type*} (Z : ι → Ω → ℝ) :
    Var[∑ i ∈ (∅ : Finset ι), Z i; μ] = 0 := by simp

-- No IsProbabilityMeasure or IsFiniteMeasure binder is added here.
example (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hi : X ⟂ᵢ[μ] Y) :
    Var[X + Y; μ] = Var[X; μ] + Var[Y; μ] := hi.variance_add hX hY

example {ι : Type*} {s : Finset ι} {Z : ι → Ω → ℝ}
    (hZ : ∀ i ∈ s, MemLp (Z i) 2 μ)
    (hi : Set.Pairwise ↑s fun i j ↦ Z i ⟂ᵢ[μ] Z j) :
    Var[∑ i ∈ s, Z i; μ] = ∑ i ∈ s, Var[Z i; μ] :=
  IndepFun.variance_sum hZ hi

example [IsFiniteMeasure μ] (hX : MemLp X 2 μ) {c : ℝ} (hc : 0 < c) :
    μ {ω | c ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (Var[X; μ] / c ^ 2) :=
  meas_ge_le_variance_div_sq hX hc

example [IsProbabilityMeasure μ] {a b : ℝ}
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hm : AEMeasurable X μ) :
    Var[X; μ] ≤ ((b - a) / 2) ^ 2 := variance_le_sq_of_bounded h hm

-- Explicitly check parameters that originate in the source's Prod section.
example {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {Z : Ω' → ℝ}
    (hX : MemLp X 2 μ) (hZ : MemLp Z 2 ν) :
    Var[fun p ↦ X p.1 + Z p.2; μ.prod ν] = Var[X; μ] + Var[Z; ν] :=
  variance_add_prod hX hZ

end VarianceSurveyChecks
