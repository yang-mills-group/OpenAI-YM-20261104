import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskPlaced

/-! The original cubic and quartic use their own individual masks even when
some other plaquette in the same physical sample is rejected. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice RG Wilson MeasureTheory OPE.Therm
open IterationFour IterationFour.Vacuum PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G : Gauge} {n : Side} {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem mean_mask (μ : Measure Ω) [IsFiniteMeasure μ] (f : Signed→Ω→ℝ) {A L : ℝ}
    (h : ∀s,Measurable (f s) ∧ (∀U,‖f s U‖≤A) ∧ (∫U,‖f s U‖ ∂μ)≤L) :
    Measurable (fun U=>Patch.average (fun s=>f s U)) ∧
      (∀U,‖Patch.average (fun s=>f s U)‖≤A) ∧
        (∫U,‖Patch.average (fun s=>f s U)‖ ∂μ)≤L := by
  refine ⟨measurable_const.mul (Finset.measurable_fun_sum _ fun s _=>(h s).1),
    fun U=>mean_bound _ _ (fun s=>(h s).2.1 U),?_⟩
  exact mask_average_price μ f (fun s=>(h s).1) (fun s=>(h s).2.1) (fun s=>(h s).2.2)

theorem mean_diff (f g : Signed→ℝ) : Patch.average f-Patch.average g=Patch.average (fun s=>f s-g s) := by
  simp only [Patch.average,sum_sub_distrib,mul_sub]

def maskedSitePacket (A : ℕ→Atom G k) (p : BudgetPoint) (x : Site n) (U : Config G n) : ℝ:=
  Patch.average fun s : Signed=>∑'i,(A i).placed p (pull s 0 U) x

theorem spring_mask_atom_at (R : Run G) (simple : G.Simple) (heat : Poetry R.family.path.levels) (q : ℕ) :
    ∀ᶠ j : ℕ in atTop,∀N,j≤N→∀per(h : ℕ) (A : ℕ→Atom G h) (σ C : ℝ),0<σ→
      SumBudget (fun i=>(A i).budget σ) C→∀ (x : Site (R.family.side j per)),
      let p:=(R.family.path.rep N per j).p
      let fee:=(625*(Fintype.card PlaqAxes:ℝ))*R.family.path.levels.clock.forcedAllowance j^q
      let f (U : Config G (R.family.side j per)):=maskedSitePacket A p x U-sitePacket A x U
      Measurable f ∧ (∀U,‖f U‖≤C*2^h) ∧
        (∫U,‖f U‖ ∂scene R.family.path N per j) ≤ C*(2^h*(1+2*h+σ⁻¹)*fee) := by
  filter_upwards [spring_mask_series R simple heat q] with j paid N live per h A σ C hs bill x p fee f
  let n:=R.family.side j per
  let F (s : Signed) (U : Config G n):=(∑'i,(A i).placed p (pull s 0 U) x)-∑'i,(A i).unmasked (pull s 0 U) x
  have same : f=fun U=>Patch.average (fun s=>F s U) := by funext U;exact mean_diff .. 
  rw [same]
  letI : IsProbabilityMeasure (scene R.family.path N per j):=probability R.makes.wilson live
  apply mean_mask
  intro s
  have raw:=paid N live per h A σ C 1 hs zero_le_one bill s 0 x (fun i=>(A i).footprint x) 0
    (fun i U=>(A i).unmasked U x) (fun _=>by simp) (fun i=>((A i).unmasked_cont x).measurable)
    (fun i U=>by simpa only [Real.norm_eq_abs,mul_one] using (A i).unmasked_bound U x)
  simpa only [F,Pi.sub_def,Atom.placed,mul_one,Nat.cast_zero,add_zero,p,fee] using raw

end YM.Integration.OriginalMarkedRunAction
