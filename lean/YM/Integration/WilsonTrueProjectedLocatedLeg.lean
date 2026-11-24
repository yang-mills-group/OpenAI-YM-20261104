import YM.Integration.WilsonTrueProjectedLocatedBalance
import YM.Integration.WilsonOriginalNullPlacedFullMatrix

/-! An individually paid transferred primary, including a previous stable feed,
is a genuine full stored field at the landing site. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedLocatedLeg
open Filter MeasureTheory Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open QuadraticLocal QuadraticLocal.Advent AllOrder AllOrder.Floe AllOrder.Transit WheelP WilsonOriginalNullCorridor
open scoped Classical Topology BigOperators

open FormalBulk08 City Pose RemainderComparison ConnectedActivityE6
open WilsonTrueProjectedPointProgram WilsonTrueProjectedPointInverse
open WilsonTrueProjectedLocatedBasis WilsonTrueProjectedLocatedHistory
open WilsonPinnedWidthTransport WilsonTrueProjectedNaturalFee WilsonTrueProjectedCourse
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G)
local notation "C₀" => R.family


open WilsonTrueProjectedLocatedFunded WilsonTrueProjectedLocatedMerge Push.Local
theorem charge {d : ℕ} {F : Frame G d} {A : Hol G} {p : Side} (W : Rep G p) (o : Site p)
    (q : Coefficient F p) {κ B price : ℝ} (hf : q.Format o A W) (hr : q.remBound o W κ B)
    (dw : d≤W.p.order) (pw : d≤W.p.power) (head : F.coeffSize (projection F A W.p.threshold o q)≤price) :
    F.coeffSize q.x≤price+tPrice F A W*B := by
  let v:=projection F A W.p.threshold o q
  have orig := (germ_close F A).choose_spec.2 W q hf hr dw pw
  have h : ‖q.x-v‖≤(germ_close F A).choose*Germ.wraps W.p p*B := (norm_sub_rev q.x v).le.trans orig
  have r : F.coeffSize (q.x-v) ≤ tPrice F A W*B := (size_le_norm F _).trans
    ((mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by dsimp [tPrice]; ring))
  have eq : v+(q.x-v)=q.x := by abel
  rw [←eq]
  exact (Size.add F v _).trans (add_le_add head r)

theorem original {d N p b n : ℕ} {η : ℝ} {live : b+n≤N} {home : Opened C₀ d b p}
    {o : ∀ j,Site ((C₀).side j p)} {A : (C₀).label d →ₗ[ℂ] (C₀).label d}
    (H : WilsonOriginalNullPlacedFullMatrix.Heard R d η N p b n live home o A) (x : (C₀).label d) :
    let P := (C₀).path.rep N p b
    let L := (C₀).labels.level d
    let bill := WilsonOriginalNullPlacedCollar.cost R d η b (b+n)*(2*stock C₀ (b+n)*mCost C₀ d N p (b+n) x)
    ∃ z : store C₀ d p b, Paid R P (o b) z ((2+|tPrice L (C₀).params P|)*bill) ∧
      flow C₀ d N p b n (placed R d N p b o n x)=z.density (o b) ((C₀).localSection d) P := by
  intro P L bill
  obtain ⟨_,z,fz,bz,_,_,_,head,field,-⟩:=H.deposited x
  have dims:=dimensions d N p b R.makes home.post (show b≤N by omega)
  have ray := H.intrinsic x z ⟨fz,⟨_,bz⟩,field.symm⟩
  have cap : L.coeffSize (projection L R.family.params P.p.threshold (o b) z) ≤ 2*bill := by
    rw [ray];exact head
  have pay:=charge P (o b) z fz bz dims.1 dims.2 cap
  have b0:0≤bill:=(rem_nonneg bz)
  have r0:0≤|tPrice L R.family.params P|:=abs_nonneg _
  have safe:bill≤(2+|tPrice L R.family.params P|)*bill := (one_mul bill).symm.le.trans
    (mul_le_mul_of_nonneg_right (by linarith) b0)
  refine ⟨z,⟨fz,rem_mono bz safe,?_⟩,field⟩
  calc
    _ ≤ 2*bill+tPrice L R.family.params P*bill := pay
    _ ≤ 2*bill+|tPrice L R.family.params P| * bill := add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (le_abs_self _) b0)
    _ = _ := by ring

end YM.Integration.WilsonTrueProjectedLocatedLeg
