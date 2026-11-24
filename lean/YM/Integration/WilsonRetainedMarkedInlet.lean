import YM.Overlay.Pays
import YM.QuadraticLocal.Lamps

/-! The original regular and forced marked rows as a local-comparison input on the very same field. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000

noncomputable section
namespace YM.Integration.WilsonRetainedMarkedInlet

open Function Finset MeasureTheory Lattice Wilson RG Marker Overlay QuadraticLocal Push.Corrected
open scoped Classical Topology BigOperators

variable {G : Gauge} {n : Side} {V : Type*} [Fintype V] [DecidableEq V]
  {R : Census V} {P : Rep G n} (a : Bands R P) (h : a.Active)
  {w : V → ℝ} {u c d b δ κ : ℝ} (t : a.Radial w u c d b) (H : P.activities.Valid P.p δ κ)

omit [Fintype V] in
private theorem live (s : R.Mode) (hs : s.val.Nonempty) : s ≠ R.quiet :=
  fun e => hs.ne_empty (congrArg Subtype.val e)

def lamps : Lamps Unit ℕ G P.p a.origins R where
  mode := a.rays
  live i := live _ (h.proper i)
  address i := ⟨a.origins (h.proper i).choose, a.support i, h.pins i _ (h.proper i).choose_spec⟩
  roots i := h.pins i
  nominal _ := a.H
  legal _ := h.regular
  clear _ := False
  pure _ _ _ no := no.elim

theorem regular (hz : a.units = 0) (U : Config G n) :
    (lamps a h).log () U = a.extra U := by
  classical
  simp [Lamps.log, Lamps.frame, Lamps.light, Lamps.ground, lamps, Bands.extra, Bands.ray, hz]

include h t H in
private theorem quiet (i : ℕ) (U : Config G n) :
    (a.each i U).part R.quiet = (P.activities.K i U : ℂ) := by
  have zero (j : ℕ) : (a.tagged i j U).part R.quiet = 0 := by
    rw [Bands.tagged,Poly.part_send,if_neg (live _ (h.occurs i j)).symm]
  rw [Bands.each,Poly.part_plus,Poly.share ((a.baseBound h t H U).1 i)]
  simp [zero]

include h t H in
private theorem charge (i : ℕ) :
    Width.LocalCharge P.p a.origins (P.activities.forced i).support (a.each i) where
  gauge θ U := by simp only [Bands.each,Bands.tagged,H.forced.sym i θ U,h.invi i _ θ U]
  borel := by
    unfold Bands.each
    refine Measurable.add ((Bands.sends _).measurable.comp
      (Complex.continuous_ofReal.measurable.comp (H.forced.meas i))) (Measurable.tsum fun j => ?_)
    exact (Bands.sends _).measurable.comp (h.meas i j)
  reads U W hf ht := by
    simp only [Bands.each,Bands.tagged,H.forced.reads i U W hf ht,h.inspects i _ U W hf ht]
  carry U s nz v hv := by
    classical
    by_contra out
    have non : s ≠ R.quiet := live _ ⟨v,hv⟩
    have zero (j : ℕ) : (a.tagged i j U).part s = 0 := by
      rw [Bands.tagged,Poly.part_send]
      split
      next e =>
        by_contra ne
        have active : a.entries i j ≠ 0 := fun hzero => ne (by simp [hzero])
        exact out (h.retained i j active v (e ▸ hv))
      next => rfl
    apply nz
    rw [Bands.each,Poly.part_plus,Poly.part_send,if_neg non,Poly.share ((a.baseBound h t H U).1 i)]
    simp [zero]

def hard : Hard Unit P.p P.activities.forced P.activities.K a.origins R where
  hard _ := a.each
  locality _ i := charge a h t H i
  charged _ i U nz := by
    by_contra no
    have old : P.activities.K i U = 0 := not_not.mp (fun e => no (H.forced.permit i U e))
    have marks (j : ℕ) : a.entries i j U = 0 := not_not.mp (fun e => no (h.keeps i j U e))
    apply nz
    simp [Bands.each,Bands.tagged,old,marks]
  quiet _ i U := quiet a h t H i U

def incoming : Gallery Unit ℕ a.origins P R := ⟨lamps a h,hard a h t H⟩

theorem forced (U : Config G n) : (incoming a h t H).gas () U = a.cluster U := rfl

theorem original (hz : a.units = 0) (U : Config G n) :
    (incoming a h t H).density () U = a.density U := by
  change (Real.exp (P.exponent U):ℂ) • (Poly.pass ((lamps a h).log () U) * _) = _
  rw [regular a h hz]
  rfl

end YM.Integration.WilsonRetainedMarkedInlet


