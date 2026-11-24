import YM.Integration.FullQLocalRetainedOutput
import YM.Comparison.RG02.Step.History

/-! Buy the polar marked radius before selecting an output on a constructed
trajectory. The complete physical input, its native compulsory branch and
all old payments survive on the nose. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedLaurentRadius
open Filter Finset Function Lattice Wilson RG Precision Marker RG3.Script.Picnic
open LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open PhysicalNext.Repeat.Legato Comparison.RG02
open scoped Classical BigOperators Topology

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
    {C : Family G} {J : Request V} {A : NumericSchedule C J} {d : LocalFormal.Datum C Γ}
    (F : AnalyticInput J A d) (r : V→ℝ) (hr : ∀v,0<r v) (hOld : ∀v,r v≤F.outputRadii v)

def atRadius : AnalyticInput J A d :=
  {F with outputRadii := r
          output_radius_positive := hr
          radius_admission := fun v =>
            (mul_le_mul_of_nonneg_right (hOld v) (A.radius_loss_positive d.level).le).trans (F.radius_admission v)}

variable {η : ℝ} (I : FullPreparedInputAt F η)

def prepared : FullPreparedInputAt (atRadius F r hr hOld) η :=
  ⟨I.carrier,I.wellFormed,I.inherited,I.inherited_nonnegative,I.inherited_bound,
    I.error,I.error_paid,I.calibration,I.exponent,I.input,I.multilinear,I.input_retains,
    I.regularPrice,I.forcedPrice,I.forced_bound,I.prepared⟩

theorem native (paid : Retained.NativeIntake I) :
    Retained.NativeIntake (prepared F r hr hOld I) :=
  ⟨paid.original,paid.reserved,paid.ordinary_nonnegative,paid.ordinary_small⟩

theorem input (x : TestSpace J.tests) :
    ((prepared F r hr hOld I).input.leaf x).density=(I.input.leaf x).density := rfl

variable (g gain : ℝ) (k : V→ℕ) (target : V→ℝ)

def radius (v : V) : ℝ :=
  min (F.outputRadii v) (F.kernelCosts v*g^(k v)*target v/gain)

variable (hg : 0<g) (ha : 0<gain) (ht : ∀v,0<target v)

include hg ha ht in
theorem positive (v : V) : 0<radius F g gain k target v :=
  lt_min (F.output_radius_positive v) (div_pos (mul_pos (mul_pos (F.kernel_positive v) (pow_pos hg _)) (ht v)) ha)

def funded : AnalyticInput J A d :=
  atRadius F (radius F g gain k target) (positive F g gain k target hg ha ht)
    (fun _ => min_le_left _ _)

theorem slot (v : V) : ((funded F g gain k target hg ha ht).outputRadii v/F.kernelCosts v)*
    (g^(k v))⁻¹*gain≤target v := by
  let b := F.kernelCosts v
  let q := g^(k v)
  have hb : 0<b := F.kernel_positive v
  have hq : 0<q := pow_pos hg _
  have h : radius F g gain k target v≤b*q*target v/gain := min_le_right _ _
  calc (radius F g gain k target v/b)*q⁻¹*gain ≤ ((b*q*target v/gain)/b)*q⁻¹*gain :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right h hb.le) (inv_nonneg.mpr hq.le)) ha.le
       _=target v := by field_simp

theorem word (s : Γ.Mode) :
    Poly.toll (fun v => (funded F g gain k target hg ha ht).outputRadii v/F.kernelCosts v) s*
      (g^(∑v∈s.val,k v))⁻¹*gain^s.val.card≤Poly.toll target s := by
  have h := Finset.prod_le_prod
    (s:=s.val) (f:=fun v => ((funded F g gain k target hg ha ht).outputRadii v/F.kernelCosts v)*
      (g^(k v))⁻¹*gain) (g:=target)
    (fun v _ => mul_nonneg (mul_nonneg (div_nonneg ((funded F g gain k target hg ha ht).output_radius_positive v).le
      (F.kernel_positive v).le) (inv_nonneg.mpr (pow_pos hg _).le)) ha.le)
    (fun v _ => slot F g gain k target hg ha ht v)
  simpa only [Poly.toll,Finset.prod_mul_distrib,Finset.prod_inv_distrib,Finset.prod_pow_eq_pow_sum,
    Finset.prod_const] using h

theorem laurent (hsmall : g≤1) (s : Γ.Mode) (i j : ℕ) (law : j ≤ i + ∑v∈s.val,k v) :
    Poly.toll (fun v => (funded F g gain k target hg ha ht).outputRadii v/F.kernelCosts v) s*
      ‖(g:ℂ)^((i:ℤ)-(j:ℤ))‖*gain^s.val.card≤Poly.toll target s := by
  have power : ‖(g:ℂ)^((i:ℤ)-(j:ℤ))‖≤(g^(∑v∈s.val,k v))⁻¹ := by
    rw [norm_zpow,Complex.norm_real,Real.norm_of_nonneg hg.le]
    calc g^((i:ℤ)-j) ≤ g^(-(↑(∑v∈s.val,k v):ℤ)) :=
          zpow_le_zpow_right_of_le_one₀ hg hsmall (by exact_mod_cast (show -(↑(∑v∈s.val,k v):ℤ)≤(i:ℤ)-j by omega))
         _=_ := by rw [zpow_neg,zpow_natCast]
  have hw (v) : 0<(funded F g gain k target hg ha ht).outputRadii v/F.kernelCosts v :=
    div_pos ((funded F g gain k target hg ha ht).output_radius_positive v) (F.kernel_positive v)
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left power (Poly.worth hw s).le)
    (pow_nonneg ha.le _)).trans (word F g gain k target hg ha ht s)

end YM.Integration.WilsonLimitConstruction.FundedLaurentRadius
end
