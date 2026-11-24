import YM.Integration.WilsonIndependentRegisteredUnaryFactory
import YM.Integration.WilsonPhysicalStationPrincipalGrade
import YM.Integration.WilsonPhysicalStationFineCorrection
import YM.Integration.WilsonPhysicalStationHorizontalWallet

/-! The signed, registered factory on an engineering-homogeneous input on one
original step. Its full output has one thermal diagonal and one dated fee. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationRegisteredDiagonal
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus MergeProof Matric Gram
open PhysicalNext.Repeat.Legato Bandage Campaign
open Next.Foundations OPE
open WilsonPhysicalStationFactoryGerm (incoming)
open scoped BigOperators Classical Topology
variable {G:Gauge} {d:ℕ} (F:Frame G d)

def ceiling (t:ℝ):ℝ := ∑a:F.Index,|t|^(F.grades a).2

theorem ceiling_nonneg (t:ℝ) : 0≤ceiling F t :=
  Finset.sum_nonneg (fun _ _=>pow_nonneg (abs_nonneg _) _)

theorem charged (t:ℝ) (x:F.Coeff) :
    F.coeffSize (F.scaled t x) ≤ ceiling F t*F.coeffSize x := by
  unfold Frame.coeffSize
  rw [Finset.mul_sum];apply Finset.sum_le_sum;intro a _
  have atA:|t|^(F.grades a).2≤ceiling F t:=
    Finset.single_le_sum (f:=fun i:F.Index=>|t|^(F.grades i).2)
      (fun _ _=>pow_nonneg (abs_nonneg _) _) (Finset.mem_univ a)
  simpa [Frame.scaled_apply,norm_mul,Real.norm_eq_abs] using mul_le_mul_of_nonneg_right atA (norm_nonneg (x a))

theorem exact (T:Heading F) {fine coarse:ℝ} (signed:WilsonIndependentUnaryPrincipal.Signed T fine coarse)
    (L:Side) (v:F.Coeff) (e:ℕ) (horizon:d=e+1) (horizontal:Columns.low F e v=0) :
    T.leads L v=F.scaled (coarse/fine) v := by
  have active:=WilsonPhysicalStationHorizontalWallet.fromLower F e v horizontal horizon
  ext i
  rw [WilsonPhysicalStationPrincipalGrade.one T signed.through L active i (F.bound i)]
  by_cases hi:(F.grades i).1=d
  · rw [hi,Nat.sub_self,pow_zero,mul_one]
    simp [Frame.scaled_apply]
  · rw [Frame.scaled_apply,active i (lt_of_le_of_ne (F.bound i) hi),mul_zero,mul_zero]

variable (R:Run G) {T:Campaign R} (L:Pillars R T) {N p m:ℕ}
local notation "F₀" => R.family.labels.level d
local notation "μ" => (F₀).coeffSize
def ratio (m:ℕ):ℝ:=(R.family.path.levels.budget m).threshold/(R.family.path.levels.budget (m+1)).threshold

include L in
theorem original (hg:G.Simple) (early:R.t d ≤ m) (live:m<N) (e:ℕ) (horizon:d=e+1) :
    ∃ U:Heading (F₀),
      WilsonIndependentUnaryPrincipal.Signed U (R.family.path.levels.budget (m+1)).threshold
        (R.family.path.levels.budget m).threshold ∧
      ∀ y:R.family.label d,
        let v:=(incoming R d N p y (m+1)).x
        let x:=(incoming R d N p y m).x
        Columns.low (F₀) e v=0 →
          U.leads (R.family.S.block m) v=(F₀).scaled (ratio R m) v ∧
          μ (x-(F₀).scaled (ratio R m) v) ≤ barunit (R.family.S.block m)*μ v := by
  obtain ⟨U,signed,paid⟩:=WilsonIndependentRegisteredUnaryFactory.original R L (p:=p) hg early live
  refine ⟨U,signed,?_⟩
  intro y v x horizontal
  have diag:=exact (F₀) U signed (R.family.S.block m) v e horizon horizontal
  refine ⟨diag,?_⟩
  have earn:=paid ((R.family.factory d N p).terminal.symm y)
  change μ (x-U.leads (R.family.S.block m) v) ≤ barunit (R.family.S.block m)*μ ((F₀).core v) at earn
  change U.leads (R.family.S.block m) v=(F₀).scaled (ratio R m) v at diag
  rw [← diag]
  exact earn.trans (mul_le_mul_of_nonneg_left (by apply WilsonStartup.Mixture.core_le)
    (by unfold barunit puffs; positivity))

end YM.Integration.WilsonPhysicalStationRegisteredDiagonal
end
