import YM.Integration.WilsonPositionThermometerStationFunding

/-! The reporter's original inverse-calibrated field has a before-regulator
coefficient budget at the extraction date and at the common funding date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerStationWallet
open Function Set Filter RG Labels Source Lattice Wilson Next.Rank Next.Rank.East Next.Rank.Price
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open scoped BigOperators Classical Topology
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {H : (Bel C.book).Hierarchy}
    {D : ℕ} (V : Vane C D) (j : Fin (D+1)) (w : (Bel C.book).Field j)

def allowance : ℝ :=
  let F := C.labels.level j
  let t := 2*C.path.levels.clock.monitor V.k
  let b := Next.Rank.Station.mag C.path.levels V.b V.k
  2*F.coeffSize (F.scaled t (weightTag C j b (Further.CorrectedLift.ladder C j w)))

theorem original (hC : C.Makes) (checked : V.checked f H D) {N p : ℕ} (top : V.k < N) :
    (C.labels.level j).coeffSize (awake C j V.k N p (V.wheel.atCut (N,p) j w)) ≤ allowance V j w := by
  let F := C.labels.level j
  let T := V.R N p j
  let b := Next.Rank.Station.mag C.path.levels V.b V.k
  let v := weightTag C j b (Further.CorrectedLift.ladder C j w)
  let u := V.wheel.atCut (N,p) j w
  let a := shrink C V.k N p
  let t := 2*C.path.levels.clock.monitor V.k
  have hT : Tested C j V.k N p T := ((checked.rate N p top).1 j).1
  have ha : 0 < a := shrink_pos C hC top.le p
  have hz : a⁻¹ ≤ t := shrink_min C hC top.le p
  have hQ : F.scaled a (T u) = v := poured hC (checked.early j) top.le b T hT _
  have copy : T u = F.scaled a⁻¹ v := by
    have h := F.scaled_inv (inv_ne_zero ha.ne') (T u)
    rw [inv_inv,hQ] at h
    exact h.symm
  have hpos : 0 < t := (inv_pos.mpr ha).trans_le hz
  have budget : F.coeffSize (T u) ≤ F.coeffSize (F.scaled t v) := by
    rw [copy]
    unfold Frame.coeffSize
    apply Finset.sum_le_sum
    intro i _
    rw [Frame.scaled_apply, Frame.scaled_apply, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
    gcongr
  exact (hT.cost C T u).trans (mul_le_mul_of_nonneg_left budget zero_le_two)

theorem at_report (hC : C.Makes) (checked : V.checked f H D) {m N p : ℕ}
    (ref : C.ref j ≤ m) (order : m ≤ V.k) (top : V.k < N) (ε : ℝ)
    (columns : ∀ i, m ≤ i → i < V.k → (C.path.levels.params (i+1)).columns ≤ ((C.S.block i).val:ℝ)^ε) :
    (C.labels.level j).coeffSize (awake C j m N p (V.wheel.atCut (N,p) j w)) ≤
    (C.S.a m/C.S.a V.k)^ε * allowance V j w := by
  exact (WilsonPositionThermometerStationTransport.filed C V j w hC ref order top.le ε columns).trans
    (mul_le_mul_of_nonneg_left (original V j w hC checked top) (Real.rpow_nonneg
      (div_nonneg (C.S.a_pos m).le (C.S.a_pos V.k).le) _))

end YM.Integration.WilsonPositionThermometerStationWallet
end
