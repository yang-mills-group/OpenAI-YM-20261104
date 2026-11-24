import YM.Integration.WilsonIndependentCollarOrbitalPeg
import YM.Integration.WilsonReceivedDepositedOrbitalNamedWage
import YM.Integration.WilsonIndependentCollarOriginalDose

/-! The compatible binder census counts each active physical source dose once.
The number of candidates here is finite even for a countable incoming word. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarOrbitalDose
open Finset Function Lattice Marker Multi RG05Readout.Many QuadraticLocal QuadraticLocal.Earn
open WilsonCoeffUV.Wheel WilsonCoeffUV.Embroider
open WilsonIndependentCollarOrbitalPeg (ink)
open WilsonOriginalCensusStagedCopies (pupil)
open WilsonOriginalCensusCompatibleCopies (entry)
open WilsonReceivedDepositedOrbitalNamedWage (wages)
open WilsonOriginalMixedBlockRows (room)
open scoped Classical BigOperators

theorem joint {V I M:Type}[Fintype V][DecidableEq V][DecidableEq I][CommMonoid M]
    {C:Census V}{mode:I→Hot C}{J:Finset I}(live:Lit (parts C) mode J)(f:V→M) :
    (∏i∈J,∏v∈(mode i).val.val, f v) = ∏v∈(unionOf live.climb).val,f v := by
  change _ = ∏v∈(J.image mode).biUnion Hot.sites,f v
  have disj : ((J.image mode):Set (Hot C)).Pairwise (fun i j=>Disjoint i.sites j.sites) := parts_wise live.climb
  rw [Finset.prod_biUnion disj, Finset.prod_image live.2]

variable {n:ℕ}{I:Type}[DecidableEq I][Fintype I]{side:Side}
  {P:Earn.Passport side (Fin n)}(B:I→Earn.Binder P (Stock.census (Fin n)))(x:Affinity.Wallet (room (Fin n)))
  {D:Fin n→ℕ}(t:Case D)(target:(Stock.census (Fin n)).Mode)

omit [Fintype I] in
theorem block (s:Finset I):
    ‖wages B x target s‖ * (∏i∈s,‖ink t (B i).mode.val‖) ≤
      ∏v∈target.val,‖(x v).val‖*‖t v‖ := by
  unfold wages entry
  split
  next live =>
    split
    next selected =>
      subst target
      rw [norm_prod]
      simp_rw [norm_prod]
      have cut:(∏i∈s,‖ink t (B i).mode.val‖)≤∏i∈s,∏v∈(B i).mode.val,‖t v‖:=
        prod_le_prod (fun i _=>(ink t (B i).mode.val).opNorm_nonneg) (fun i _=>(WilsonIndependentCollarOrbitalPeg.inner t (B i).mode.val).2)
      apply (mul_le_mul_of_nonneg_left cut (prod_nonneg (fun _ _=>prod_nonneg fun _ _=>norm_nonneg _))).trans_eq
      rw [Finset.prod_mul_distrib]
      exact congrArg₂ (·*·) (joint live (fun v=>‖(x v).val‖)) (joint live (fun v=>‖t v‖))
    next => simp only [norm_zero,zero_mul]; exact prod_nonneg (fun _ _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))
  next => simp only [norm_zero,zero_mul]; exact prod_nonneg (fun _ _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem original :
    (∑s:Finset I,‖wages B x target s‖ * ∏i∈s,‖ink t (B i).mode.val‖) ≤
      (2:ℝ)^(Fintype.card I) * ∏v∈target.val,‖(x v).val‖*‖t v‖ := by
  apply (Finset.sum_le_sum (fun s _=>block B x t target s)).trans_eq
  simp [Fintype.card_finset]

end YM.Integration.WilsonIndependentCollarOrbitalDose
end
