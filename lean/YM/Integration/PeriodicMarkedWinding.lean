import YM.WilsonCoeffUV.Winding.Gazette
import YM.WilsonCoeffUV.Winding.Moment

/-! Periodic marked heat compared with the periodized cover in coordinates
centered at a specified mark. Every other prescribed mark moves independently. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PeriodicMarkedWinding
open Finset Function Lattice RG Laurent Bloch Metric Wilson Tree Exterior Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.PathCost
open scoped BigOperators Classical

variable {ι α V : Type} {J : Finset ι} {n : Side} {r : ℕ} {s A : ℝ}

/-- Use the centered lift of each mark's own periodic displacement from one
fixed named root. Distinct labels may still occupy the same torus site. -/
def roots (n : Side) (z : ι → Site n) (u : ι) (i : ι) : Cover :=
  lift (z u) + lift (z i - z u)

theorem roots_wrap (z : ι → Site n) (u : ι) : wrap n ∘ roots n z u = z := by
  funext i
  simp [Function.comp_apply, roots]

private theorem crest (z : ι → Site n) {u : ι} (hu : u ∈ J)
    (x : dock (Site n) α r) :
    crestCard (roots n z u) J ≤ 2 * Syn (tor n) z J x := by
  apply league_cash _ (a := lift (z u))
  intro i
  change size (lift (z u) + lift (z i.val - z u) - lift (z u)) ≤ _
  rw [add_sub_cancel_left]
  exact leg_le (tor n) (foyer z J x) (.inl ⟨u, hu⟩) (.inl i)

/-- A spatial error estimate at every period and every tuple of independent
positions. Half the surviving rate still weights the field and marked sites.
The exponential in the period has rate `s/512`. -/
theorem periodized [NormedAddCommGroup V] [CompleteSpace V] [Fintype α]
    {P : Ten V (Co n α) r} {F : Ten V (Cloth α) r} (z : ι → Site n)
    (u : ι) (hu : u ∈ J) (hs : 0 < s)
    (h : MarkU (roots n z u) J P F s A) :
    let t := s / 32
    let B := (priceM α r s + tiePay α r (s/4) + 1)*A + A
    Wig (tor n) z (t/2) (B*catchW (t/16) n) J (Bank.Carp.plume F n - P) := by
  intro t B
  have hJ : J.Nonempty := ⟨u, hu⟩
  by_cases small : 4*crestCard (roots n z u) J < n.val
  · simpa only [roots_wrap] using markOrbit h hJ small hs
  have hP := (h.mono (show t ≤ s by dsimp [t]; linarith)).bill
  have hF := (plumeW (n := n) h.access hJ hs).bill
  have hB := add_nonneg hF.1 hP.1
  rw [roots_wrap] at hP hF
  refine ⟨mul_nonneg hB (catch_hot ..), fun x => ?_⟩
  have far := crest z hu x
  have hn : n.val ≤ 8*Syn (tor n) z J x := by omega
  exact expired (hF.2 x) (hP.2 x) hn (by dsimp [t]; positivity) hB

/-- The original one-step operator supplies its own two-sided winding comparison
from the preblock input only. The price, width and credit precede the period,
the individual root placements, the independent source kernels and their tests. -/
theorem step [DecidableEq ι] (G : Gauge) {Z : Finset ι} (hJ : J ⊆ Z)
    (D k : ι → ℕ) (e i r : ℕ) (hi : i ≤ e) (H E : Credit)
    (w : Gear G → ℝ) (hw : ∀ I, 0 < w I) :
    ∃ (s c : Gear G → ℝ) (U : Credit), (∀ I, 0 < s I ∧ (s I)⁻¹ ≤ c I) ∧
      ∀ (Q : Realm G (e+1) E) m N (n : Side) (hm : Q.anchor ≤ m) (_ : m < N),
        let I := (Q.mint m hm).gear
        c I ≤ Q.cash H m → ∀ K : family G D, Eu k K → K ∅ = 0 →
        ∀ (z : ι → Site n) (u : ι), u ∈ J →
        ∀ (b : ι → Site (loose Q.draws m).L) (A : ℝ), 0 ≤ A →
          safeB (chartIn (loose Q.draws m) (roots n z u) b) K Z e (w I) A →
          let M := Q.cash U m * A ^ J.card
          let B := (priceM (Hooks G) r (s I) + tiePay (Hooks G) r (s I/4) + 1)*M+M
          Wig (tor n) z (s I/32/2) (B * catchW (s I/32/16) n) J
            (Bank.Carp.plume ((logO Q.draws Q.paid m N K k J).2 i r) n -
              coilH Q.draws Q.paid m N n K k (ratioHigh Q.draws Q.paid N m) J i r) := by
  obtain ⟨s, c, U, hs, issue⟩ := pledges G e i r hi H E w hw hJ D k
  refine ⟨s, c, U, hs, ?_⟩
  intro Q m N n hm hN I budget K hEu h0 z u hu b A hA input
  exact periodized z u hu (hs I).1
    (issue Q m N n hm hN budget K hEu h0 (roots n z u) b A hA input)

end YM.Integration.PeriodicMarkedWinding
end
