import YM.Integration.WilsonCenteredNestedOrbit

/-! The same physical rotation and real branch can be carried through all
vertices, including the lower terms of the raw through-degree field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedRealOrbit
open Function Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader
open OPE.Prescription OPE.Log WilsonCenteredNestedLoggedRow WilsonCenteredNestedGross
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable {I : Type} [Fintype I] {d : I→ℕ}

def restored (P : Prescription F.sector.derivatives) (h : ℕ) (x : I→E4) (v : Labels S d)
    (o : E4) (k : Ortho) (real : Bool) : S.Field h :=
  if real then S.conj F.room.kernel.spin h (spinning P F.sector.turns h x o k (bar F.room.kernel.spin v))
  else spinning P F.sector.turns h x o k v

lemma conjugate (h : ℕ) (x : I→E4) (v : Labels S d) (o : E4) :
    Q.packet h x (bar F.room.kernel.spin v) o = S.conj F.room.kernel.spin h (Q.packet h x v o) := by
  unfold Reader.packet
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _=>?_
  rw [Q.real_fresh,Q.stands.realInc]

theorem original {P : Prescription F.sector.derivatives} (hp : P.Coherent)
    (fac : Facilities C f S) (foundation : Foundation F Q) {u : Filter (ℕ×ℕ)} [u.NeBot]
    (lo : u ≤ f.fuse) (ticket : MatrixTicket (C:=C) S F.sector.derivatives u)
    (h : ℕ) (v : Labels S d) {M η : ℝ} (Mn : 0 ≤ M) (ηp : 0 < η) :
    ∃(j : ℕ)(A : ℝ),0 ≤ A ∧ ∀ᶠ r:ℝ in 𝓝[>]0,∀(x:I→E4)(o:E4),WithinRoom r M η x o →
      ∀(k:Ortho)(b:Bool),‖restored F P h x v o k b - Q.packet h x v o‖ ≤
        wage j A r * r^((h:ℝ)+1-weight d) := by
  obtain ⟨j,A,An,trueRow⟩ := WilsonCenteredNestedOrbit.original F Q hp fac foundation lo ticket h v Mn ηp
  obtain ⟨l,B,Bn,barRow⟩ := WilsonCenteredNestedOrbit.original F Q hp fac foundation lo ticket h (bar F.room.kernel.spin v) Mn ηp
  let star := (conjugateR F.room.kernel.spin h).toContinuousLinearMap
  let E := max A (‖star‖*B)
  refine ⟨max j l,E,An.trans (le_max_left ..),?_⟩
  filter_upwards [trueRow,barRow,(show ∀ᶠr:ℝ in 𝓝[>]0,0<r from self_mem_nhdsWithin)] with r direct conjugateRow rp x o fit k b
  have rn := Real.rpow_nonneg rp.le ((h:ℝ)+1-weight d)
  cases b
  · exact (direct x o fit k).trans (mul_le_mul_of_nonneg_right (wage_le (le_max_left ..) An (le_max_left ..)) rn)
  · have back : S.conj F.room.kernel.spin h (Q.packet h x (bar F.room.kernel.spin v) o) = Q.packet h x v o := by
      rw [conjugate F Q,Table.reflect_star]
    change ‖S.conj F.room.kernel.spin h _ - Q.packet h x v o‖ ≤ _
    rw [←back,←map_sub]
    calc
      _ ≤ ‖star‖ * ‖spinning P F.sector.turns h x o k (bar F.room.kernel.spin v) - Q.packet h x (bar F.room.kernel.spin v) o‖ :=
        star.le_opNorm _
      _ ≤ ‖star‖ * (wage l B r * r^((h:ℝ)+1-weight d)) :=
        mul_le_mul_of_nonneg_left (conjugateRow x o fit k) star.opNorm_nonneg
      _ = wage l (‖star‖*B) r * r^((h:ℝ)+1-weight d) := by unfold wage;ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (wage_le (le_max_right ..) (mul_nonneg star.opNorm_nonneg Bn) (le_max_right ..)) rn

end YM.Integration.WilsonCenteredNestedRealOrbit
