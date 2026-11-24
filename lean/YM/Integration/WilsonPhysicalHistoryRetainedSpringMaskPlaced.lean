import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskPrism
import YM.Integration.WilsonVacuumPreResetModelBoard

/-! Group the very same signed seats at a submitted physical site. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice RG Wilson MeasureTheory OPE.Therm
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open Comparison.Density Comparison.Density.Render AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Collection
open IterationFour IterationFour.Vacuum PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G : Gauge} {n : Side} {k : ℕ}

theorem shifted_atom (A : Atom G k) (s : Signed) (x : Site n) (U : Config G n) :
    A.unmasked ((Song.splay n (s,x)).view U) 0=A.unmasked (pull s 0 U) x := by
  have he : (Song.splay n (s,x)).view U=translate x (pull s 0 U) := by
    rw [←pull_one,pull_pull,mul_one,affine,add_zero];rfl
  rw [he,←pull_one]
  unfold Atom.unmasked RG.Slot.atSite
  simp_rw [expandAt_pull,pull_id,affine,Signed.act_one]
  simp

theorem summed_seats (a : PrismA G) (x : Site n) (U : Config G n) :
    ∑s : Signed,unmaskedSeat a (Song.splay n (s,x)) U=sitePacket a.cells x U := by
  unfold unmaskedSeat sitePacket Patch.average
  simp_rw [shifted_atom]
  rw [←mul_sum]
  rfl

def maskedPrismAt (a : PrismA G) (B : BudgetPoint) (σ C θ : ℝ) (x : Site n) (U : Config G n) : ℝ:=
  ∑s : Signed,maskedSeat (FundedCorrectedPeriod.piece n B σ C a).packet θ (Song.splay n (s,x)) U

theorem finite_mask_sum {Ω α : Type*} [MeasurableSpace Ω] [Fintype α]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : α→Ω→ℝ) {A B : ℝ}
    (h : ∀i,Measurable (f i) ∧ (∀U,‖f i U‖≤A) ∧ (∫U,‖f i U‖ ∂μ)≤B) :
    Measurable (fun U=>∑i,f i U) ∧ (∀U,‖∑i,f i U‖≤Fintype.card α*A) ∧
      (∫U,‖∑i,f i U‖ ∂μ)≤Fintype.card α*B := by
  have fi (i) : Integrable (f i) μ := Integrable.of_bound (h i).1.aestronglyMeasurable A
    (Filter.Eventually.of_forall (h i).2.1)
  refine ⟨Finset.measurable_fun_sum _ (fun i _=>(h i).1),?_,?_⟩
  · intro U
    exact (norm_sum_le ..).trans (by simpa using sum_le_sum (s:=(univ:Finset α)) (g:=fun _=>A) (fun i _=>(h i).2.1 U))
  have sumI:=integrable_finsetSum (s:=(univ:Finset α)) (fun i _=>(fi i).norm)
  apply (integral_mono (integrable_finsetSum _ (fun i _=>fi i)).norm sumI fun U=>norm_sum_le ..).trans
  rw [integral_finsetSum _ (fun i _=>(fi i).norm)]
  simpa using sum_le_sum (s:=(univ:Finset α)) (g:=fun _=>B) (fun i _=>(h i).2.2)

theorem spring_mask_at (R : Run G) (simple : G.Simple) (heat : Poetry R.family.path.levels) (q : ℕ) :
    ∀ᶠ j : ℕ in atTop,∀ N,j≤N→∀per (a : PrismA G) (σ C : ℝ),0<σ→0<a.grade→
      Commission a.cells σ C a.grade→∀ (B : BudgetPoint) (x : Site (R.family.side j per)),
      let θ:=(R.family.path.rep N per j).p.threshold
      let fee:=(625*(Fintype.card PlaqAxes:ℝ))*R.family.path.levels.clock.forcedAllowance j^q
      let f (U : Config G (R.family.side j per)):=maskedPrismAt a B σ C θ x U-sitePacket a.cells x U
      Measurable f ∧ (∀U,‖f U‖≤Fintype.card Signed*(C*(2^(a.rise+2)*2))) ∧
      (∫U,‖f U‖ ∂scene R.family.path N per j)≤Fintype.card Signed*(C*(2^(a.rise+2)*(1+2*(a.rise+2)+625+σ⁻¹)*2*fee)) := by
  filter_upwards [spring_mask_prism R simple heat q] with j earned N live per a σ C hs pos bill B x θ fee f
  let n:=R.family.side j per
  let F (s : Signed) (U : Config G n):=maskedSeat (FundedCorrectedPeriod.piece n B σ C a).packet
    θ (Song.splay n (s,x)) U-unmaskedSeat a (Song.splay n (s,x)) U
  have same : f=fun U=>∑s,F s U := by
    funext U
    change _-sitePacket a.cells x U=_
    rw [←summed_seats a x U]
    exact (sum_sub_distrib ..).symm
  rw [same]
  letI : IsProbabilityMeasure (scene R.family.path N per j):=probability R.makes.wilson live
  exact finite_mask_sum _ F fun s=>earned N live per a σ C hs pos bill B (Song.splay n (s,x))

end YM.Integration.OriginalMarkedRunAction
