import YM.Integration.RootedPeriodicMarkedWinding
import YM.WilsonCoeffUV.Winding.Gazette

/-! A winding estimate for the two independently computed histories that enter
the *same* update. The finite observable uses its actual finite incoming
vacuum and every finite marked subword. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFiniteIncomingMarkedWinding
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer Function Filter Lattice RG WilsonCoeffUV.Embroider WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank Laurent Bloch Metric Gauge Power Matrix Precision Wilson Tree Exterior
open WilsonCoeffUV.Blue Work.F08 FreeResolvent AnalyticNext.QuarticMatch.Sheets PowerSeries
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.PathCost
open scoped Topology BigOperators Classical

variable {G : Gauge} {ι : Type} [DecidableEq ι] {D k : ι → ℕ}
    {e i r m N : ℕ} {E : Credit} {Z J : Finset ι}

private def paired (Q : Realm G (e+1) E) (hm : Q.anchor ≤ m) (hN : m < N)
    {s : ℝ} (hs : 0 < s) (n : Side)
    (K : family G D) (y : ι → Cover) (cells : ι → Site (loose Q.draws m).L)
    (h₀ : K ∅ = 0) (hK : Eu k K) {V A : ℝ} (hV : 1 ≤ V) (hA : 0 ≤ A)
    (vacuum : ∀ a ≤ e, ∀ l, Sight
      ((story Q.draws Q.paid N (m+1)).1 (n*(loose Q.draws m).L) a l)
      (actionW Q.draws Q.paid N (m+1) a l) (holt Q m hm s hs).s V)
    (marks : ∀ S ⊆ Z, ∀ a ≤ e, ∀ l, MarkU (chartIn (loose Q.draws m) y cells) S
      ((K S).1 (n*(loose Q.draws m).L) a l) ((K S).2 a l)
      (holt Q m hm s hs).s (A^S.card)) :
    PackOne Z D k e (holt Q m hm s hs) := by
  let previous := (old Q.draws Q.paid Q.hG Q.green N (m+1) hN).basis (n*(loose Q.draws m).L)
  let frame : ScrollV e (holt Q m hm s hs) :=
    { cloVent Q m N n hm hN s hs with
      W := (story Q.draws Q.paid N (m+1)).1
      coin := V
      paid := hV
      fare := vacuum }
  exact ⟨frame,y,cells,K,previous.lamp,previous.shape,h₀,hK,A,hA,marks⟩

/-- Constants and output width are chosen before the top, period, deposits and
tests. The input receipts price the actual finite and cover vacua together
and every marked subset of the submitted family. -/
theorem original (Q : Realm G (e+1) E) (hm : Q.anchor ≤ m) (hJ : J ⊆ Z)
    (hi : i ≤ e) {s : ℝ} (hs : 0 < s) :
    ∃ (d : ℕ) (C σ : ℝ), 0 ≤ C ∧ 0 < σ ∧
      ∀ N, m < N → ∀ (n : Side) (K : family G D) (y : ι → Cover)
        (cells : ι → Site (loose Q.draws m).L), K ∅ = 0 → Eu k K →
      ∀ V A : ℝ, 1 ≤ V → 0 ≤ A →
      (∀ a ≤ e, ∀ l, Sight
        ((story Q.draws Q.paid N (m+1)).1 (n*(loose Q.draws m).L) a l)
        (actionW Q.draws Q.paid N (m+1) a l) (holt Q m hm s hs).s V) →
      (∀ S ⊆ Z, ∀ a ≤ e, ∀ l, MarkU (chartIn (loose Q.draws m) y cells) S
        ((K S).1 (n*(loose Q.draws m).L) a l) ((K S).2 a l)
        (holt Q m hm s hs).s (A^S.card)) →
        let O := logO Q.draws Q.paid m N K k J
        MarkU y J (O.1 n i r) (O.2 i r) σ
          (C * V^d * A^J.card * rimJ (ratioHigh Q.draws Q.paid N m) i r) := by
  obtain ⟨d,gates⟩ := qLocal_mark (G:=G) (D:=D) (k:=k) e i r hi J Z hJ
  obtain ⟨C,σ,hC,hσ,step⟩ := gates (holt Q m hm s hs)
  refine ⟨d,C,σ,hC,hσ,?_⟩
  intro N hN n K y cells h₀ hK V A hV hA vacuum marks O
  let p := paired Q hm hN hs n K y cells h₀ hK hV hA vacuum marks
  have result := step p (ratioHigh Q.draws Q.paid N m)
  rw [show O.1 n = _ from feeleg Q.draws Q.paid m N K k hN Q.hG Q.green hK n J,
      show O.2 = _ from onSide Q.draws Q.paid m N K k h₀ hK Q.hG Q.green hN J]
  exact result

end YM.Integration.WilsonFiniteIncomingMarkedWinding
