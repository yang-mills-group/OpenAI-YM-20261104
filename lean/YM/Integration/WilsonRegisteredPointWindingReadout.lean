import YM.Integration.OriginalIssuedMarkedRows
import YM.Integration.SignedRootedWindingReadout
import YM.Integration.WilsonLimitConstruction.FundedPointSourceClock

/-! The signed finite-minus-cover contraction for the original registered point
stencils on any admitted torus, through the same realm as their outgoing path
measure. The price is charged before the physical test or its placements. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredPointWindingReadout
open Function Filter Lattice RG Wilson Precision Next.Foundations
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider.Canvas
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Embroider WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Blue WilsonCoeffUV.Winding Work.F08
open FundedMarkedPathSelection WilsonLimitConstruction
open scoped Classical BigOperators

variable {G : Gauge} {R : Run G} {m e n N per i r d c q : ℕ}
    {J Z : Finset (Fin n)} {o : Fin n} {k D : Fin n → ℕ}

abbrev difference (Q : Realm G (e+1) Credit.leanC) {hm : Q.anchor ≤ m} {A : ℝ}
    (bank : Input Q hm Z k D A) (J : Finset (Fin n)) (o : Fin n) (N per i r : ℕ)
    (R : Run G) :=
  let n₀ := R.family.side m per
  let t := fun z => PeriodicMarkedWinding.roots n₀ z o
  let ideal := fun z => (output bank J N (t z)).2 i r
  let finite := fun z => coilH Q.draws Q.paid m N n₀ (bank.familyAt (t z)) k
    (ratioHigh Q.draws Q.paid N m) J i r
  RootedPeriodicMarkedWinding.row n₀ J o (fun z => Carp.plume (ideal z) n₀ - finite z)

def priced {α : Type} (J : Finset (Fin n)) (o : Fin n) (r : ℕ)
    (T : (Fin n → Cover) → Ten (Pen D J) (Cloth α) r) (g A : ℝ) (c q : ℕ) : Prop :=
  ∀ (x : Cover) (v : Fence α J o r → SignedRootedWindingReadout.Tests D) (U : ℝ),
    0 ≤ U → (∀ i, SignedRootedWindingReadout.amplitude J (v i) ≤ U) →
    ∀ ξ : Fence α J o r → ℂ, (∀ i, ‖ξ i‖ ≤ 1) →
      let f := fun i => ξ i * SignedRootedWindingReadout.read J (v i) (towerV J o r T x i)
      Summable f ∧ ‖∑' i, f i‖ * g ^ (-(c : ℝ)) ≤ U * (g ^ q * A ^ J.card)

theorem signed {s : Gear G → ℝ} (Q : Realm G (e+1) Credit.leanC) {hm : Q.anchor ≤ m}
    {A : ℝ} (bank : Input Q hm Z k D A) (hN : m < N) (ho : o ∈ J)
    (hs : 0 ≤ s (Q.mint m hm).gear)
    (award : OriginalIssuedMarkedRows.Award R Q hm J Z o s N per i r d c q bank) :
    priced J o r (difference Q bank J o N per i r R)
      (Pert.Asymptotics.regulatorRun R.family N per (m+1)) A c q := by
  obtain ⟨B, invoice, post⟩ := award.2.2
  obtain hg := ActualRunKernelPackets.regulator_pos R N per (m+1) hN
  intro x v U hU hv ξ hξ
  obtain ⟨conv, bound⟩ := SignedRootedWindingReadout.tested J ho (by positivity) post x v U hU hv ξ hξ
  exact ⟨conv, (mul_le_mul_of_nonneg_right bound (Real.rpow_nonneg hg.le _)).trans
    ((mul_assoc _ _ _).le.trans (mul_le_mul_of_nonneg_left invoice hU))⟩

/-- The reporter chooses one realm before the top cutoff, period, actual
fine point placements, derivative letters and independent testing functions. -/
theorem original {B : MS.Local.Physical.Deck G} (P : MS.Land.Prescription B)
    (grades weights : Fin n → ℕ) (labs : Fin n → MS.Rake.Label B) (μ : ℝ)
    (normal : Fin n → ℂ) (quad : Fin n → Bool) {w s : Gear G → ℝ}
    (hJ : J ⊆ Z) (ho : o ∈ J) (hi : i ≤ e) (hw : ∀ a, 0 < w a) (hs : ∀ a, 0 ≤ s a)
    (stage : FundedMarkedWindingWindow.Window R J Z o
      (FundedOriginalMarkedInput.OrbitD (FundedPointMarkedSeed.reference R grades weights))
      k e i r d c q w s m) :
    ∃ (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m),
      Q.draws = R.family.path.levels ∧ Q.paid = R.metals.O ∧
      ∀ N per, m < N → ∀ (b : ℕ) (sites : Fin n → Site (R.family.side b per))
        (orders : Fin n → ℕ) (cells : (Fin n → Cover) → Fin n → Site (loose Q.draws m).L),
        let a := FundedPointMarkedSeed.datum R grades weights per b sites
        let X := FundedOriginalMarkedInput.chosen P a labs (μ - R.family.S.scale b) orders normal quad
        let bank := OriginalIssuedMarkedRows.input X Q hm w hw Z cells
          (fun v _ => Nat.le_add_left _ (k v))
        OriginalIssuedMarkedRows.Award R Q hm J Z o s N per i r d c q bank ∧
          priced J o r (difference Q bank J o N per i r R)
            (Pert.Asymptotics.regulatorRun R.family N per (m+1))
            (OriginalIssuedMarkedRows.fee (k:=k) X Q hm w) c q := by
  obtain ⟨Q,hm,draws,paid,issue⟩ := OriginalIssuedMarkedRows.select hJ ho hi hw stage
  refine ⟨Q,hm,draws,paid,?_⟩
  intro N per hN b sites orders cells a X bank
  have awarded := issue N per hN (FundedOriginalMarkedInput.Count a labs) X
    (fun v _ => Nat.le_add_left _ (k v)) cells
  exact ⟨awarded,signed Q bank hN ho (hs _) awarded⟩

end YM.Integration.WilsonRegisteredPointWindingReadout
