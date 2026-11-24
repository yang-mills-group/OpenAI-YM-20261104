import YM.Integration.WilsonFiniteIncomingMarkedWinding
import YM.Integration.SignedRootedWindingReadout

/-! The complete signed winding current for the finite marked recursion with
its own incoming vacuum. The width is read on the outgoing row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFiniteIncomingWindingCurrent
open Function Filter Lattice RG WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Address
open WilsonCoeffUV.Soil WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Realm
open Laurent Precision Work.F08
open scoped Classical BigOperators

variable {G : Gauge} {ι : Type} [DecidableEq ι] {D k : ι → ℕ}
    {e i r m : ℕ} {E : Credit} {Z J : Finset ι} {o : ι}

abbrev row (R : Levels G) (β : ChartRatio G) (m N : ℕ) (n : Side) (K : (ι → Site n) → family G D)
    (k : ι → ℕ) (J : Finset ι) (o : ι) (i r : ℕ) :=
  RootedPeriodicMarkedWinding.row n J o (fun z =>
    let O := logO R β m N (K z) k J
    Carp.plume (O.2 i r) n - O.1 n i r)

def price (G : Gauge) (r a : ℕ) (J : Finset ι) (o : ι) (n : Side) (σ B : ℝ)
    (W : Credit) (u : ℝ) : ℝ :=
  ((priceM (Hooks G) r σ + tiePay (Hooks G) r (σ/4) + 1)*B + B) *
    Real.exp (-(σ/512)*(n.val : ℝ)) * (riding (Hooks G) r a J o W).buy u

theorem original (Q : Realm G (e+1) E) (hm : Q.anchor ≤ m) (hJ : J ⊆ Z) (ho : o ∈ J)
    (hi : i ≤ e) {s : ℝ} (hs : 0 < s) :
    ∃ (d : ℕ) (C σ : ℝ), 0 ≤ C ∧ 0 < σ ∧
      ∀ N, m < N → ∀ (n : Side) (K : (ι → Site n) → family G D)
        (cells : (ι → Site n) → ι → Site (loose Q.draws m).L),
      (∀ z, K z ∅ = 0) → (∀ z, Eu k (K z)) →
      ∀ V A : ℝ, 1 ≤ V → 0 ≤ A →
      (∀ a ≤ e, ∀ l, Sight
        ((story Q.draws Q.paid N (m+1)).1 (n*(loose Q.draws m).L) a l)
        (actionW Q.draws Q.paid N (m+1) a l) (holt Q m hm s hs).s V) →
      (∀ z, ∀ S ⊆ Z, ∀ a ≤ e, ∀ l,
        MarkU (chartIn (loose Q.draws m) (PeriodicMarkedWinding.roots n z o) (cells z)) S
          ((K z S).1 (n*(loose Q.draws m).L) a l) ((K z S).2 a l)
          (holt Q m hm s hs).s (A^S.card)) →
      ∀ (a : ℕ) (W : Credit) (u : ℝ), (σ/32/2/2)⁻¹ ≤ W.buy u → 1 ≤ u →
        let P := row Q.draws Q.paid m N n K k J o i r
        let B := C * V^d * A^J.card * rimJ (ratioHigh Q.draws Q.paid N m) i r
        let H := price G r a J o n σ B W u
        PostMark J o r P (σ/256) H a ∧
        ∀ (x : Cover) (v : Fence (Hooks G) J o r → SignedRootedWindingReadout.Tests D)
          (U : ℝ), 0 ≤ U → (∀ b, SignedRootedWindingReadout.amplitude J (v b) ≤ U) →
          ∀ ξ : Fence (Hooks G) J o r → ℂ, (∀ b, ‖ξ b‖ ≤ 1) →
          let f := fun b => ξ b * SignedRootedWindingReadout.read J (v b) (towerV J o r P x b)
          Summable f ∧ ‖∑' b, f b‖ ≤ U*H := by
  obtain ⟨d,C,σ,hC,hσ,step⟩ :=
    WilsonFiniteIncomingMarkedWinding.original (D:=D) (k:=k) (r:=r) Q hm hJ hi hs
  refine ⟨d,C,σ,hC,hσ,?_⟩
  intro N hN n K cells h₀ hK V A hV hA vacuum marks a W u hu hw P B H
  have receipt := RootedPeriodicMarkedWinding.measured (j:=r) ho hσ
    (fun z => (logO Q.draws Q.paid m N (K z) k J).2 i r)
    (fun z => (logO Q.draws Q.paid m N (K z) k J).1 n i r)
    (fun z => step N hN n (K z) (PeriodicMarkedWinding.roots n z o) (cells z)
      (h₀ z) (hK z) V A hV hA vacuum (marks z)) W hu hw a
  have paid : PostMark J o r P (σ/256) H a := by
    simpa only [P,H,B,row,price,catchW,show σ/32/2/2/2=σ/256 by ring,
      show σ/32/16=σ/512 by ring] using receipt
  exact ⟨paid, SignedRootedWindingReadout.tested J ho (by positivity) paid⟩

end YM.Integration.WilsonFiniteIncomingWindingCurrent
