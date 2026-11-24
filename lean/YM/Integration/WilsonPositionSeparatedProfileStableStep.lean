import YM.Integration.WilsonPositionSeparatedProfileCenteredReadout
import YM.OPE.Replicas.Budget

/-! The original single-marker step accepts any captured formatted coefficient.
At scalar output its emitted coordinate is a constant on the actual gauge field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileStableStep
open Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open ProjectorNext.Equivariance Trace.Physical Push.Local RG05Readout Address Native
open MergeProof MergeProof.Ribbons.ManyCopies.Cadet.Studio.ZeroDegree
open PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Legato.Bandage
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G)

theorem primary {n : Side} {F : Labels.Frame G 0} (S : SectionData F)
    (H : RG.Rep G n) (o : Site n) (v : F.Coeff) (V : Config G n) :
    part S o H V v = v 0 := by
  have h : F.core v=0 := by
    funext j
    obtain rfl:=one_at (F:=F) j
    simp [Frame.core]
  change v 0+masked H.p.threshold (S.footprint o) (S.places (F.scaled H.p.threshold⁻¹ (F.core v)) o) V=v 0
  rw [h,map_zero]
  by_cases good : Healthy H.p.threshold (S.footprint o) V
  · simp [masked_eq _ _ _ _ good,SectionData.places,S.eval_linear.map_zero]
  · simp [good]

def strip {n : Side} {F : Labels.Frame G 0} (X : Coefficient F n) : Coefficient F n := {X with x:=0}

theorem density {n : Side} {F : Labels.Frame G 0} (S : SectionData F)
    (H : RG.Rep G n) (X : Coefficient F n) :
    (strip X).density 0 S H = fun V=>X.density 0 S H V-(H.eval V : ℂ)*(X.x 0) := by
  funext V
  let f:=∑'i,X.maskedTerm H i V
  let r:=(Real.exp (H.exponent V):ℂ)*∑'z,X.marked H z V
  change (H.eval V:ℂ)*(part S 0 H V 0+f)+r=(H.eval V:ℂ)*(part S 0 H V X.x+f)+r-(H.eval V:ℂ)*(X.x 0)
  rw [map_zero,zero_add,primary S]
  ring

def shrink : ℝ := ((3:ℝ)^(1/8:ℝ))⁻¹^(3:ℕ)

private theorem decay (i : ℕ) : Bid.barunit (R.family.S.block i) ≤ shrink := by
  have h : (3:ℝ)≤(R.family.S.block i).val := by exact_mod_cast R.family.S.block_large i
  have bound := Real.rpow_le_rpow (by norm_num : (0:ℝ)≤3) h (by norm_num : (0:ℝ)≤1/8)
  exact pow_le_pow_left₀ (by positivity) (inv_anti₀ (by positivity) bound) _

theorem shrink_pos : 0<shrink := by unfold shrink; positivity

theorem shrink_lt : shrink<1 := by
  unfold shrink
  exact pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by norm_num))) (by decide)

theorem issued (D : OPE.Package R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors)
    {N per i : ℕ} (grade : R.family.ref 0 ≤ i) (live : i < N)
    (X : Coefficient (R.family.labels.level 0) (R.family.side (i+1) per)) {w : ℝ}
    (form : X.Format 0 R.family.params (R.family.path.rep N per (i+1)))
    (cost : X.remBound 0 (R.family.path.rep N per (i+1))
      (Real.sqrt (R.family.path.levels.clock.forcedAllowance (i+1))) w) :
    ∃(Y : Coefficient (R.family.labels.level 0) (R.family.side i per)) (a : ℝ),
      0≤a ∧ a≤ shrink*w ∧ a≤Bid.barunit (R.family.S.block i)*w ∧ Y.Format 0 R.family.params (R.family.path.rep N per i) ∧
      Y.remBound 0 (R.family.path.rep N per i) (Real.sqrt (R.family.path.levels.clock.forcedAllowance i)) a ∧
      ‖Y.x 0‖≤a ∧ Y.density 0 (R.family.localSection 0) (R.family.path.rep N per i)=
        blast R.family.path N per i 0 ((strip X).density 0 (R.family.localSection 0) (R.family.path.rep N per (i+1))) := by
  let C:=R.family
  let A:=C.path.rep N per
  let F:=C.labels.level 0
  have zero : (strip X).Format 0 C.params (A (i+1)) :=
    ⟨form.smooth,form.origin,form.identity_null,form.projects,form.forcing,form.carried,form.invariant,form.supported,form.borel⟩
  obtain ⟨η,tone⟩:=D.system.listens 0 N per i grade live
  obtain ⟨_,_,market⟩:=tone.priced
  obtain ⟨Y,gig,_⟩:=market (strip X) w rfl zero cost
  have ep:=tone.tuned.2.2.2
  have pos : 0≤w := by obtain ⟨v,z,hv,hz,h,_⟩:=cost;exact (add_nonneg hv hz).trans h
  have small : η≤Bid.barunit (C.S.block i) :=
    (le_mul_of_one_le_left ep (le_add_of_nonneg_right (by positivity [(C.path.levels.params i).columns_ge]))).trans tone.tuned.1
  have norm : ‖Y.x 0‖≤F.coeffSize Y.x := Finset.single_le_sum (fun k _=>norm_nonneg (Y.x k)) (Finset.mem_univ 0)
  have head : Motion.orbitCost F*F.coeffSize Y.x≤η*w := by simpa only [sub_zero] using gig.leadP
  refine ⟨Y,η*w,mul_nonneg ep pos,mul_le_mul_of_nonneg_right (small.trans (decay R i)) pos,mul_le_mul_of_nonneg_right small pos,gig.format,gig.bound,?_,gig.agrees⟩
  exact norm.trans ((le_mul_of_one_le_left ((norm_nonneg _).trans norm) (Motion.orbitCost_one_le F)).trans head)

end YM.Integration.WilsonPositionSeparatedProfileStableStep
