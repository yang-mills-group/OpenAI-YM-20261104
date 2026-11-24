import YM.Integration.WilsonMeasuredForcedIntake
import YM.Integration.WilsonPhysicalMarkedDefectSource

/-! The actual quiet of the received course admits a fresh, one-name
compulsory insertion at the capture center.  Every old partner remains on
the eligible inventory where the original post issued it. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMeasuredSingleOwner
open Function Finset MeasureTheory Lattice Wilson RG Labels Source Marker Overlay QuadraticLocal QuadraticLocal.Earn Ac
open Push.Corrected Push.AbsoluteSums QuadraticLocal.Fusion.Attached MergeProof.Accent Affinity
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonPhysicalMarkedDefect WilsonOriginalDepositedHard
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {d : ℕ} {F : Frame G d} {A : Hol G}
  {P W : Rep G n} {V : Type} [DecidableEq V] {J : Census V} {o : V → Site n}
  {Y : V → Type} [∀i, AddCommGroup (Y i)] [∀i, Module ℝ (Y i)]
  {C : ∀i,Set (Y i)} {K : ∀i,Submodule ℝ (Y i)} {k : ℝ}
  (rent : Hard.Rent W.activities.forced W.activities.K W.p W.p.supportExponent k)
  (j : V) (q : Coefficient F n) (law : q.Format (o j) A W) (t : Wallet C → ℂ)
local notation "base" => modelInput (Passport.point o) W J (Wallet C) rent

def intake : Tint.Incoming (Passport.point o) W (Wallet C) Empty J :=
  ⟨(base).old,joined (base).hard j q law t⟩

local notation "Z" => intake (J:=J) rent j q law t

theorem admitted (a : Attn K C {j} t) :
    Taut (Passport.point o).support C K (Z).old ∧ Crown (Passport.point o).support C K (Z).hard :=by
  obtain ⟨reg,hard⟩:=model_input_addresses (A:=Passport.point o) (Γ:=J) C K rent
  exact ⟨reg,WilsonOriginalDepositedHardTable.crown j q law C K (base).hard t hard a⟩

omit [∀i, AddCommGroup (Y i)] [∀i, Module ℝ (Y i)] in
theorem received [Fintype V] (w : V → ℝ) (hw : ∀i,0<w i) (bounded : ∀x,‖t x‖≤1)
    {κ M : ℝ} (actual : q.remBound (o j) W κ M)
    (same : P.p=W.p) (quiet : W.eval=P.eval) (owners : P.activities.forced=W.activities.forced)
    (S : SectionData F) :
    (Z).old.Paid w W.p.B (W.p.supportExponent+1+1) 0 ∧
    (Z).hard.Paid w W.p.B W.p.supportExponent (k+w j*(κ*M)) ∧
    ∀ x U,t x*q.density (o j) S W U=t x*(soft q).density (o j) S P U+
      (Real.exp (W.exponent U):ℂ)*
        (∑' b, packet W.activities W.p ((Z).hard.hard x) U b).part (J.fire j) :=by
  have paid := (model_input_prices (A:=Passport.point o) (Γ:=J) (X:=Wallet C) rent w).2
  obtain ⟨fund,-,field⟩:=WilsonMeasuredForcedIntake.original (base).hard j q law t w hw paid bounded
    actual same quiet owners S
  refine ⟨Spill.Foundry.empty_lit W _ _ _,fund,?_⟩
  intro x U
  have sameField:=field x U
  rw [model_input_gas (A:=Passport.point o) (Γ:=J) rent hw x U] at sameField
  change t x*q.density (o j) S W U=t x*(soft q).density (o j) S P U+
    _*((∑' b,packet W.activities W.p ((Z).hard.hard x) U b).part (J.fire j)-
    (Poly.send J.quiet _).part (J.fire j)) at sameField
  simpa only [Poly.part_send,if_neg (J.fire_hot j),sub_zero] using sameField

end YM.Integration.WilsonMeasuredSingleOwner
