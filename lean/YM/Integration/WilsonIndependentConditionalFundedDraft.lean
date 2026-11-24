import YM.Integration.WilsonIndependentConditionalCoverDraft

/-! The complete post-heat bulk draft on an original anchored angular word,
against the actual free predictor. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalFundedDraft
open Filter Function RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet
open Lattice Laurent Bloch Matrix WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Soil
open scoped Topology Classical BigOperators
variable {α β:Type}{r:ℕ}

theorem salary [Fintype α] {p:Cover}{P:raw α ℝ r}{T:Ten ℝ (Cloth α) r}(h:Bends p P T):Summable (fun y=>‖T y‖):=by
  cases r with
  | zero=>exact Summable.of_finite
  | succ r=>
    obtain ⟨s,A,hs,hA⟩:=h.land
    let k:=r+1
    have hv:0<(s-0)/(k:ℝ):=by dsimp [k];positivity
    have cash:Summable (fun y:dock Cover α k=>A*sail ((s-0)/k) Bank.terrain p y):=
      (train_pay (α:=α) hv p k).2.1.mul_left _
    apply cash.of_nonneg_of_le (fun _=>norm_nonneg _)
    intro y
    apply (hA.2 y).trans (mul_le_mul_of_nonneg_left _ hA.1)
    have dist (i:Fin k):terrain.gap p (y i).1≤tread terrain p y:=
      leg_le terrain (stud p y) 0 i.succ
    simpa only [neg_zero,zero_mul,Real.exp_zero,one_mul] using
      (sail_cut (v:=0) (Nat.zero_le _) le_rfl hs (show 0<k by omega) p y dist)

theorem coefficients {F:(n:Side)→ ropes (Site n) α β}{U:ropes Cover α β}(h:Pilots F U):
    ∃ C:ℝ,1≤C ∧∀x y,|U x y|≤C:=by
  obtain ⟨s,A,hs,hA⟩:=h.fees
  refine ⟨max 1 A,le_max_left ..,fun x y=>?_⟩
  apply le_trans _ (le_max_right ..)
  apply le_of_tendsto (h.point x y).abs
  filter_upwards [hA] with n hn
  exact (hn.2 _ _).trans (mul_le_of_le_one_right hn.1 (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) (Nat.cast_nonneg _))))

theorem folded {I:Type}{K:Layer I I}{T:Packet I r}{C:ℝ}(c1:1≤C)(coeff:∀x y,|K x y|≤C)
    (h:Summable fun y=>‖T y‖)(sym:IsSym T)(z:Tuple I r):
    draft K T z=∑' y,(∏ i,K (z i) (y i))*T y:=by
  classical
  rw [WilsonIndependentConditionalCoverDraft.original c1 coeff h]
  let F:Packet I r:=fun z=>∑' y,(∏ i,K (z i) (y i))*T y
  change Packet.symmetry F z=F z
  apply congrFun (symmetric_already F _) z
  intro π x
  change (∑' y,(∏ i,K (x (π i)) (y i))*T y)=_
  rw [←(Tuple.perm I π).tsum_eq]
  apply tsum_congr;intro y
  change (∏ i,K (x (π i)) (y (π i)))*T (y∘π)=(∏ i,K (x i) (y i))*T y
  rw [sym π y]
  exact congrArg (fun t=>t*T y) (Equiv.prod_comp π fun i=>K (x i) (y i))

theorem original [Fintype α] {p:Cover}{F:(n:Side)→ ropes (Site n) α α}{K:ropes Cover α α}
    (pilot:Pilots F K){P:raw α ℝ r}{T:Ten ℝ (Cloth α) r}(word:Bends p P T)(sym:Smooth T):
    draft K T=reflectCut K.transpose T:=by
  obtain ⟨C,one,hC⟩:=coefficients pilot
  funext z
  rw [folded one hC (salary word) sym,climb_cut]
  apply tsum_congr;intro y;rfl

end YM.Integration.WilsonIndependentConditionalFundedDraft
