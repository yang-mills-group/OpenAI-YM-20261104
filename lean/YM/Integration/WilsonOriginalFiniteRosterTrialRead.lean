import YM.Integration.WilsonOriginalUnconditionedTrialRead

/-! Bochner income on the same unconditioned N-inherited vacuum for a
complete square-free roster. Only the one-arm absolute cost is used for
each multiplier. All named arms enter a single original integral. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalFiniteRosterTrialRead
open Finset Set Function MeasureTheory Lattice RG Wilson Source Labels
open PhysicalNext.Repeat.Legato Extra.Histories OPE.Therm OPE.Strobe
open WilsonOriginalMicroscopicGuardedTrial (unary raw)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntranceCellWords (submitted)
open WilsonOriginalMicroscopicGuardedWallet (loss)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonPositionProgramBlockedTrialAddBack (uncut)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)

theorem arm (d N per K:ℕ)(live:K≤N)(o:Site (R.family.side K per))(v:R.family.label d):
    Measurable (uncut R d N per K o v) ∧ ∀U,‖uncut R d N per K o v U‖≤
      loss R d K*(R.family.labels.level d).coeffSize v:=by
  let ds:=fun _:Fin 3=>d
  let sites:=fun _:Fin 3=>o
  let word:∀i:Fin 3,R.family.label (ds i):=fun _=>v
  have a:=unary R ds N per K sites word 0
  exact ⟨a.2.1,fun U=>(a.2.2 U).2.trans (WilsonOriginalMicroscopicGuardedWallet.one R ds N per K live word 0)⟩

variable {n:ℕ}(d:Fin n → ℕ){N per f K requested power t:ℕ}{B:ℝ}{fk:f≤K}{cut:K≤N}
variable (A:Panel R d N per f K fk cut requested power t B)(file:Filed R d K)
variable (station:A.slot=file.station)(axes:A.axis=file.A N per)
variable {j:ℕ}(road:j≤K)(sites:Fin n → Site (R.family.side j per))(s:(Stock.census (Fin n)).Mode)

def value:ℂ:=∫U,submitted R d (N:=N) file road A.names A.turn sites s U ∂scene R.family.path N per K

include station axes in
theorem original:
    Integrable (submitted R d (N:=N) file road A.names A.turn sites s) (scene R.family.path N per K) ∧
    ‖value R d A file road sites s‖≤∏i∈s.val,loss R (d i) K*(B*(R.family.path.levels.clock.hatBeta K)^power):=by
  classical
  letI:IsProbabilityMeasure (scene R.family.path N per K):=probability R.makes.wilson cut
  let v:=votes R d (N:=N) (per:=per) file A.names A.turn
  let z:=fun i:Fin n=>(R.family.S.toDepth road per).embed (sites i)
  have charge (i:Fin n):=arm R (d i) N per K cut (z i) (v i)
  have m:Measurable (submitted R d (N:=N) file road A.names A.turn sites s):=by
    change Measurable (fun U=>∏i∈s.val,uncut R (d i) N per K (z i) (v i) U)
    exact Finset.measurable_prod _ (fun i _=>(charge i).1)
  have h (U):‖submitted R d (N:=N) file road A.names A.turn sites s U‖≤
      ∏i∈s.val,loss R (d i) K*(B*(R.family.path.levels.clock.hatBeta K)^power):=by
    change ‖∏i∈s.val,uncut R (d i) N per K (z i) (v i) U‖≤_
    rw [norm_prod]
    apply prod_le_prod (fun _ _=>norm_nonneg _)
    intro i _
    exact ((charge i).2 U).trans (mul_le_mul_of_nonneg_left
      (WilsonOriginalObservedRoseFittedPurse.column R d A file station axes i)
      (WilsonOriginalMicroscopicGuardedWallet.nonneg R (d i) K))
  exact ⟨Integrable.of_bound m.aestronglyMeasurable _ (Filter.Eventually.of_forall h),
    by simpa [value] using norm_integral_le_of_norm_le_const (μ:=scene R.family.path N per K) (Filter.Eventually.of_forall h)⟩
end YM.Integration.WilsonOriginalFiniteRosterTrialRead
