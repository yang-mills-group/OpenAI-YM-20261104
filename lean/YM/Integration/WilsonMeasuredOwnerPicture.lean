import YM.Integration.WilsonMeasuredSingleOwner

/-! Full zero-painter physical gallery for one measured forced source. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMeasuredOwnerPicture
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

local notation "Z" => WilsonMeasuredSingleOwner.intake (J:=J) rent j q law t
local notation "ε₀" => (Empty.elim : Empty → Row (Passport.point o) J G (Wallet C))
local notation "panel" => Tint.Patrol.picture ε₀ (Z)

omit [∀i,AddCommGroup (Y i)] [∀i,Module ℝ (Y i)] in
theorem field [Fintype V] (w : V → ℝ) (hw : ∀i,0<w i) (bounded : ∀x,‖t x‖≤1)
    {κ M : ℝ} (actual : q.remBound (o j) W κ M)
    (same : P.p=W.p) (quiet : W.eval=P.eval) (owners : P.activities.forced=W.activities.forced)
    (S : SectionData F) (x : Wallet C) (U : Config G n) :
    ((panel).density x U).part J.quiet=W.eval U ∧
    ((panel).density x U).part (J.fire j)=t x*(q.density (o j) S W U-(soft q).density (o j) S P U) :=by
  obtain ⟨-,paid,equity⟩:=WilsonMeasuredSingleOwner.received (J:=J) rent j q law t w hw bounded actual
    same quiet owners S
  have joined:=Hard.packet_summing (Z).hard paid W.p.exponent_pos.le hw x U
  have scalar:=Hard.packet_of_quiet (Z).hard x U joined
  have empty : (panel).E.log x U=0 :=tsum_empty
  rw [Gallery.density,empty,Next.Rank.Exponential.pass_zero,one_mul]
  change ((Real.exp (W.exponent U):ℂ) • (∑' b,packet W.activities W.p ((Z).hard.hard x) U b)).part J.quiet=(W.eval U:ℂ) ∧
    ((Real.exp (W.exponent U):ℂ) • (∑' b,packet W.activities W.p ((Z).hard.hard x) U b)).part (J.fire j)=_
  rw [Poly.part_smul,Poly.part_smul,scalar,Rep.eval,Complex.ofReal_mul]
  exact ⟨rfl,by linear_combination -(equity x U)⟩

end YM.Integration.WilsonMeasuredOwnerPicture
