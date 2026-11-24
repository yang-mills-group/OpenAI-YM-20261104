import YM.Integration.FVA1Physical.Sources.Round2.CurrentBoundary
import YM.MSbar.LocalSD.Escrow
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Blush.Sails

/-! Price the full signed outgoing forced fraction inside its next actual
normalized posterior. A forced source carries exactly the original exterior
gas, the measured exponential and the same marked owner. -/
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Finset MeasureTheory Lattice RG YM.Wilson Source Labels Extra.Histories
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus MSbar MSbar.Bulk
open Push Push.AbsoluteSums RGComparison.Core16.Spool
open scoped Classical BigOperators Topology
variable {G:Gauge} {n c:Side} (S:StepData c n) (R:Rep G n)

private def asFibre (M:Leaf R) : Fibre S R where
  turn:=M.turn
  ingredient:=M.ingredient
  scopedR:=M.scopedR
  grant:=M.grant
  blank:=M.blank
  weight:=M.weight
  earn:=M.earn
  glows:=fun k _=>M.glows k
  borel:=M.borel

private def ownerPart (z:Site n) (i:ℕ) (f:Config G n→ℂ) (a:ℝ)
    (cap:∀ U, ‖f U‖ ≤ a) (fit:SlotFit R z i f) (part:Bool) : Fibre S R :=
  asFibre S R (if part then Blush.fim R z i f a cap fit else Blush.frev R z i f a cap fit)

private theorem ownerPart_eq (z:Site n) (i:ℕ) (f:Config G n→ℂ) (a:ℝ)
    (cap:∀ U, ‖f U‖ ≤ a) (fit:SlotFit R z i f) (part:Bool) (U:Config G n) :
    (ownerPart S R z i f a cap fit part).cicada U=look part (fare R i f U) := by
  have both:=congrFun (Blush.rose R z i f a cap fit) U
  cases part
  · change (Blush.frev R z i f a cap fit).cicada U=(fare R i f U).re
    simpa [Pi.add_apply,Pi.smul_apply,Function.comp_apply,smul_eq_mul] using (congrArg Complex.re both).symm
  · change (Blush.fim R z i f a cap fit).cicada U=(fare R i f U).im
    simpa [Pi.add_apply,Pi.smul_apply,Function.comp_apply,smul_eq_mul] using (congrArg Complex.im both).symm

theorem signed_host_posterior {k:ℕ} {F:Frame G k} (Q:Coefficient F n) (z:Site n) {P:Hol G}
    (form:Q.Format z P R) {κ M t K σ C δ Λ w:ℝ} (fund:Q.remBound z R κ M)
    (U:Config G c) (adm:Admitted U R S σ C δ Λ w) (positive:∀ W,0 < R.eval W)
    (storm:Psalm S R t K) (clear:flags t U=∅) (hK:0 ≤ K) (part:Bool) :
    |expect S R U (fun W=>look part (forcedShare Q R W))| ≤ K*(κ*M) := by
  obtain ⟨a,b,ha,_,bill,hκ,_,cap,fees,price⟩:=fund
  have fit (i):SlotFit R z i (Q.forced i):=
    ⟨form.invariant i,form.borel i,form.supported i,form.carried i,form.forcing i⟩
  let T:=fun i=>ownerPart S R z i (Q.forced i) (cap i) (price i).2 (fit i) part
  have hz (i):∃ j,(T i).turn=Wing.gasKey j := by cases part <;> exact ⟨i,rfl⟩
  have budget:SumBudget (fun i=>R.p.mass (T i).crest (T i).weight) (κ*b):=by cases part <;> exact fees
  have dom:Dominated Q.forced:=by
    exact ⟨_,fees.2.1,fun i W=>((price i).2 W).trans (R.p.loMass _ _ (price i).1)⟩
  have pays (W:Config G n):HasSum (fun i=>(T i).cicada W) (look part (forcedShare Q R W)*R.eval W) := by
    have g:(R.activities.gas R.p W:ℂ)≠0:=by
      apply Complex.ofReal_ne_zero.mpr
      intro hh;apply (positive W).ne';rw [Rep.eval,hh,mul_zero]
    have val: (R.eval W:ℂ)*forcedShare Q R W=(Real.exp (R.exponent W):ℂ)*(∑' j,Q.marked R j W):=by
      rw [Rep.eval,Complex.ofReal_mul,forcedShare]
      field_simp [g]
    have h:=(((dress_abs adm.lawful dom).summable W).hasSum.mul_left (Real.exp (R.exponent W):ℂ)).map
      (look part).toAddMonoidHom (look part).continuous
    rw [dress_eq adm.lawful dom W] at val
    change HasSum _ (look part ((Real.exp (R.exponent W):ℂ)*∑' i,Q.forced i W*dressed R i W)) at h
    rw [←val,←Complex.real_smul,map_smul,smul_eq_mul,mul_comm (R.eval W)] at h
    exact h.congr_fun fun i=>ownerPart_eq S R z i (Q.forced i) (cap i) (price i).2 (fit i) part W
  have bound:=remit U adm.lawful T storm adm.kernel clear _ pays budget hz hK adm.mass.le
  change |S.push R.beta (fun W=>look part (forcedShare Q R W)*R.eval W) U/S.push R.beta R.eval U| ≤ _
  rw [abs_div,abs_of_pos adm.mass,div_le_iff₀ adm.mass,mul_comm _ (S.push ..)]
  exact bound.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (by linarith only [ha,bill]) hκ.le) hK) adm.mass.le)

end YM.Integration.FVA1Physical.Round2.Curvature
