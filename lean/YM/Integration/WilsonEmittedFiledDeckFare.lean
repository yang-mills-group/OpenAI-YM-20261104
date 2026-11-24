import YM.Integration.WilsonEmittedFiledMixedWindow

/-! On the actual filed angular polynomials the positive-rank entries
are unchanged by flat centering. Comparing the centered deck readings
leaves the original occupied scalar as a separate finite payment. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000
noncomputable section
namespace YM.Integration.WilsonEmittedFiledDeckFare
open Function Filter Finset Lattice RG Marker RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Pipeline RegulatorIR.FVAAlt2.Sound RegulatorIR.Diagram
open Comparison.RG02 Comparison.RG02.Adjacent ActualRunAdmissionScales Pert.Asymptotics
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical TwoReset PhysicalNext.Repeat.Legato
open WilsonOriginalOccupiedAngularPage WilsonOriginalPolarizedAngularPage WilsonOriginalLinkedAngularPage
open WilsonIndependentCapturedAngularWinding WilsonIndependentCapturedFiledDirections
open private plane plane_smooth plane_coeff polynomial symmetric from YM.Integration.WilsonIndependentCapturedFiledDirections
open scoped BigOperators Classical ContDiff
variable {G:Gauge} {n:Side} {L:Type} [DecidableEq L] {M:Census L}
local notation "I" => SiteSlot G n
local notation "E" => Stationary.Link G n

def row (clock:UnitCost) (V:Bulk.Colors M G n) (u:L) (e:ℕ) (a:E) : ℂ :=
  See.noseC M u clock V e (Stationary.arm G n 1 a)

private theorem shape (clock:UnitCost) (V:Bulk.Colors M G n) (u:L)
    (A:Orders (I)) {p e toll:ℕ} (he:e≤p) (issued:Booth.Arm.Single clock V A u p toll) :
    row clock V u e=plane (fun r=>form (A e r)) (e+toll) := by
  rw [←polynomial]
  funext a
  change See.noseC M u clock V e _=_
  have read : See.noseC M u clock V e (Stationary.arm G n 1 a)=
      Booth.Uniforms.cuff A toll e (Stationary.arm G n 1 a) := issued.earned e he _
  rw [read,Booth.Uniforms.cuff,Binding.flavor_lo]
  rfl

theorem analytic (clock:UnitCost) (V:Bulk.Colors M G n) (u:L)
    (A:Orders (I)) {p e toll:ℕ} (he:e≤p) (issued:Booth.Arm.Single clock V A u p toll)
    (r:ℕ) : ContDiff ℝ r (row clock V u e) := by
  rw [shape clock V u A he issued]
  apply plane_smooth

/-- The complex derivative of the actual filed polynomial has the same
real coefficient as its stored bank, also in rank zero. -/
theorem entry (clock:UnitCost) (V:Bulk.Colors M G n) (u:L)
    (A:Orders (I)) {p e toll r:ℕ} (he:e≤p) (issued:Booth.Arm.Single clock V A u p toll)
    (hr:r≤e+toll) (x:Tuple (I) r) :
    coefficient r (row clock V u e) x=(r.factorial:ℝ) • (A e r x:ℂ) := by
  have jet : Tensor.coeff (row clock V u e) r 0=form (A e r) := by
    rw [shape clock V u A he issued]
    exact plane_coeff _ _ hr (symmetric (issued.symmetricW e r))
  have atx := congrArg (fun h:Tensor.T (E) ℂ r=>h (fun j=>ray G (x j))) jet
  have scaled : (r.factorial:ℝ)⁻¹ • coefficient r (row clock V u e) x=(A e r x:ℂ) :=
    atx.trans (measured _ _)
  rw [←scaled,smul_smul,mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero r),one_smul]

def centered (F:E→ℂ) : E→ℂ := F-fun _=>F 0

theorem positive {F:E→ℂ} {r:ℕ} (sm:ContDiff ℝ r F) (hr:r≠0) (x:Tuple (I) r) :
    coefficient r (centered F) x=coefficient r F x := by
  unfold coefficient entries centered
  rw [iteratedFDeriv_sub_apply sm.contDiffAt contDiffAt_const,iteratedFDeriv_const_of_ne hr]
  simp

/-- The angular wage is submitted on the original filed coefficients.
Both rows retain their own dated coupling and their full mark power. -/
theorem original (R:Run G) (simple:G.Simple) (fund:RG05Preconstruction.ReadoutPurchase R.b)
    (a b c q r:ℕ) (j:Fin r) : ∀ᶠ m:ℕ in atTop,∀ N per:ℕ,m<N →
    let n₀:=R.family.side m per
    let g:=regulatorRun R.family N per (m+1)
    let H:=R.family.path.levels.clock.hatBeta m
    ∀ (X:Side) (h:n₀.val∣X.val) (root o z:Site X) (V Z:Bulk.Colors M G X)
      (left right:UnitCost) (u:L) (A B:Orders (SiteSlot G X)) (p e toll:ℕ),
    e≤p → r≤e+toll → Booth.Arm.Single left V A u p toll → Booth.Arm.Single right Z B u p toll →
    (∀ y,board h o (move G) (centered (row left V u e)) y=
         board h z (move G) (centered (row right Z u e)) y) →
    ∀ (span:Positions X (Stationary.Loc G 1) r→ℝ) (ρ D spent fare:ℝ),
    0 < ρ → ρ⁻¹ ≤ H^b → D ≤ (n₀.val:ℝ)/8 → (∀x,0 ≤ span x ∧ (separation root (x j).1:ℝ) ≤ span x+D) →
    (∑x,Real.exp (ρ*span x)*((r.factorial:ℝ)*|A e r x|)) ≤ spent →
    (∑x,Real.exp (ρ*span x)*((r.factorial:ℝ)*|B e r x|)) ≤ fare →
    2*(spent+fare)≤H^a*g^(-(c:ℝ)) →
    (∑x,|A e r x-B e r x|) ≤ g^q := by
  filter_upwards [WilsonOriginalCappedDeckHearing.original R simple fund a b c q r j] with m ready
  intro N per late n₀ g H X h root o z V Z left right u A B p e toll he hr issued scheduled
    binding span ρ D spent fare strip width short reach stipend payment total
  have fine := analytic left V u A he issued r
  have lower := analytic right Z u B he scheduled r
  have nz : r≠0 := by have := j.isLt; omega
  have eh (x:Tuple (SiteSlot G X) r) := entry left V u A he issued hr x
  have ez (x:Tuple (SiteSlot G X) r) := entry right Z u B he scheduled hr x
  have heard:=ready N per late X h root o z (centered (row left V u e)) (centered (row right Z u e))
    (fine.sub contDiff_const) (lower.sub contDiff_const) binding span ρ D spent fare strip width short
    (fun x=>(reach x).2)
  simp_rw [positive fine nz,positive lower nz,eh,ez,norm_smul,Real.norm_natCast,Complex.norm_real,
    Real.norm_eq_abs] at heard
  have result:=heard stipend payment total
  apply le_trans _ result
  apply sum_le_sum
  intro x _
  rw [←smul_sub,←Complex.ofReal_sub,norm_smul,Real.norm_natCast,Complex.norm_real,Real.norm_eq_abs]
  have wage : (1:ℝ)≤r.factorial := by exact_mod_cast Nat.factorial_pos r
  have weight : 1≤Real.exp (ρ*span x/2) := Real.one_le_exp (by nlinarith only [mul_nonneg strip.le (reach x).1])
  calc
    _ ≤ (r.factorial:ℝ)*|A e r x-B e r x| := (one_mul _).symm.le.trans (mul_le_mul_of_nonneg_right wage (abs_nonneg _))
    _ ≤ _ := (one_mul _).symm.le.trans (mul_le_mul_of_nonneg_right weight (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)))

end YM.Integration.WilsonEmittedFiledDeckFare

