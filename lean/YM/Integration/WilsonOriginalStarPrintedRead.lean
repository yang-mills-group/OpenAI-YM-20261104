import YM.Integration.WilsonOriginalStarPrimaryCatalog
import YM.Integration.WilsonOriginalStarSourceIntake

/-! A complete measured nonbare singleton on the printed original group-field catalogue. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace YM.Integration.WilsonOriginalStarPrintedRead
open Function Finset Filter Lattice Wilson RG Source Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Tint QuadraticLocal.Affinity
open PhysicalNext.Repeat.Legato WilsonOriginalStarIncoming WilsonOriginalStarIncomingRead
open WilsonOriginalDepositedRegularHearing WilsonOriginalStarPrimaryCatalog
open scoped BigOperators Classical Topology
variable {G : Gauge} (R : Run G) (N p k d : ℕ) (upper : k≤N) (ref : R.family.ref d≤k)
   {V T I S : Type} [DecidableEq V] [Fintype V] {J : Census V}
   (o : V → Site (R.family.side k p)) (j : V)
   (q : Coefficient (R.family.labels.level d) (R.family.side k p))
variable (law : q.Format (o j) R.family.params (R.family.path.rep N p k)) (t : T → ℂ) (D : ℕ)
    (old : Incoming (Passport.point o) (R.family.path.rep N p k) T I J) (M : Lamps T S G (R.family.path.rep N p k).p o J)

theorem received (w : V→ℝ) (hw : ∀v, 0<w v) (test : ∀x, ‖t x‖≤1) {κ B b e h : ℝ}
    (budget : q.remBound (o j) (R.family.path.rep N p k) κ B) (wide : 1≤(R.family.path.rep N p k).p.supportExponent)
    (model : M.Paid w (R.family.path.rep N p k).p.B ((R.family.path.rep N p k).p.supportExponent+1+1) b) (reg : old.old.Paid w (R.family.path.rep N p k).p.B ((R.family.path.rep N p k).p.supportExponent+1+1) e)
    (hard : old.hard.Paid w (R.family.path.rep N p k).p.B (R.family.path.rep N p k).p.supportExponent h) (x : T) (U : Config G (R.family.side k p)) :
    ((exhibit (enter old j q law t D) (M.join (catalogue (J:=J) R N p k d upper ref o j q.x t))).density x U).part (J.fire j) -
      ((exhibit old M).density x U).part (J.fire j) =
      t x*(q.density (o j) (R.family.localSection d) (R.family.path.rep N p k) U-((R.family.path.rep N p k).eval U:ℂ)*tail (R.family.path.rep N p k) q D U) := by
  have priced := WilsonOriginalStarPrimaryCatalog.funded (J:=J) R N p k d upper ref o j q.x t w hw ((R.family.path.rep N p k).p.supportExponent+1+1) test
  have posted := WilsonOriginalStarIncomingRead.original old j q law t D M (M.join (catalogue (J:=J) R N p k d upper ref o j q.x t)) (R.family.localSection d)
    w hw test budget wide model (Lamps.joinPaid model priced) reg hard x U
  have positive : 0≤((R.family.path.rep N p k).p.supportExponent+1+1) := by linarith
  rw [Lamps.joinLog x U (model.sums positive hw x U) (priced.sums positive hw x U),Poly.part_plus,
    WilsonOriginalStarPrimaryCatalog.filed (J:=J) R N p k d upper ref o j q.x t x U] at posted
  have same : WilsonOriginalStarPrimaryCatalog.primary R N p k d o j q.x U =
      WilsonOriginalStarIncomingRead.primary (P:=R.family.path.rep N p k) (o:=o) j q (R.family.localSection d) U := rfl
  rw [same] at posted
  linear_combination posted

open Table Spec Labels Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.Spindle
open MergeProof.Accent MergeProof.East Extra.Histories WilsonPositionThermometerDepositedRow
variable {f : Extraction.Order} {H : (Bel R.family.book).Hierarchy}

theorem star (simple : G.Simple) (grade : ℕ) :
    ∀ᶠ k in atTop, ∀ {h : ℕ} (W : Vane R.family h) (l : Fin (h+1)), l.val=grade → W.k=k →
      W.checked f H h → ∀ (licensed : R.family.ref l ≤ k) (a : (Bel R.family.book).Field l)
      (N p : ℕ) (above : k<N),
      let v := W.wheel.atCut (N,p) l a
      let q := row R.family l k N p v
      let P := R.family.path.rep N p k
      ∀ {V T I S : Type} [DecidableEq V] [Fintype V] {J : Census V}
        (o : V → Site (R.family.side k p)) (j : V), o j=0 →
      ∀ (t : T → ℂ) (D : ℕ) (old : Incoming (Passport.point o) P T I J)
        (M : Lamps T S G P.p o J) (w : V→ℝ), (∀v, 0<w v) → (∀x, ‖t x‖≤1) →
      1≤P.p.supportExponent → ∀ {b e z : ℝ},
      M.Paid w P.p.B (P.p.supportExponent+1+1) b →
      old.old.Paid w P.p.B (P.p.supportExponent+1+1) e →
      old.hard.Paid w P.p.B P.p.supportExponent z →
      ∃ (law : q.Format (o j) R.family.params P),
        q.x = Price.awake R.family l k N p v ∧
        ∀ (x : T) (U : Config G (R.family.side k p)),
          ((exhibit (enter old j q law t D) (M.join (catalogue (J:=J) R N p k l above.le
            licensed o j q.x t))).density x U).part (J.fire j) - ((exhibit old M).density x U).part (J.fire j) =
            t x * ((P.eval U:ℂ) * (actualTransport R.family (N:=N) (R.family.O N p v 0) above.le U -
              tail P q D U)) := by
  filter_upwards [WilsonPositionThermometerDepositedRow.paid (f:=f) (H:=H) R.makes simple grade 1 one_pos]
    with k issued h W l correct atStar tested licensed a N p above v q P V T I S instD instF J o j home
      t D old M w hw ht wide b e z model reg hard
  obtain ⟨law,coordinates,pay,trueRead⟩ := issued W l correct atStar tested licensed a N p above
  have situated : q.Format (o j) R.family.params P := home ▸ law
  refine ⟨situated,coordinates,?_⟩
  intro x U
  have seen := received R N p k l above.le licensed o j q situated t D old M w hw ht (home ▸ pay)
    wide model reg hard x U
  have transported : q.density (o j) (R.family.localSection l) P U =
      P.eval U • actualTransport R.family (N:=N) (R.family.O N p v 0) above.le U := by
    rw [home]
    exact trueRead U
  rw [transported] at seen
  simpa only [Complex.real_smul,mul_sub] using seen

end YM.Integration.WilsonOriginalStarPrintedRead
