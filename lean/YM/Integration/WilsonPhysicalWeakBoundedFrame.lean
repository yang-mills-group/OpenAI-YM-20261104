import YM.Integration.WilsonPhysicalWeakElectedCoordinates
import YM.Integration.WilsonPhysicalAllGradeWeakElection

/-! Cost-uniform signed coordinates of the actual original station vector at changing homes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalWeakBoundedFrame
open Function Filter Spec Table Climb PhysMS PhysMS.Frame Trace.Pilot Trace.Target
open PhysicalNext.Repeat.Legato
open WilsonPhysicalAllGradeWeakElection WilsonPhysicalWeakRisingStaff WilsonPhysicalWeakSundial
open WilsonPhysicalWeakWallStaff WilsonPhysicalWeakWallBounded WilsonPhysicalWeakSameStation
open WilsonPhysicalWeakWallBooks
open WilsonOriginalTwoFlatPublicBooks (Book)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
variable (F:Final R.family f S)(J:ℝ→tower S){H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}
  (simple:G.Simple)(a:Assignment F J H l simple){D T:ℕ}{δ:ℝ}
  (books:(r:{r:ℝ//0<r ∧ r<δ})→ Book F (l:=l) H arch D T r.val)
  (shared:∀r,∃cap:D≤(a.day r.val).1,Shared F (books r) (trim cap (a.day r.val).2))

theorem literal (r:{r:ℝ//0<r ∧ r<δ})(j:Fin (D+1))(v:(Bel R.family.book).Field j)(z:ℕ×ℕ):
    (((books r).rows j).arm true (J r.val j v)).source z=
      (books r).W.wheel.atCut z ⟨j.val,Nat.lt_succ_of_le ((Nat.le_of_lt_succ j.isLt).trans (books r).fits)⟩
        (((books r).V j).symm (J r.val j v)) :=
  ((books r).rows j).weak _ _

include shared in
theorem original {ι:Type*}(u:Filter ι)(age:ι→{r:ℝ//0<r ∧ r<δ})(near:Tendsto (fun i=>(age i).val) u trail)
    (M ε:ℝ)(hm:0≤M)(ep:0<ε):
    ∀ᶠi in u,∀j:Fin (D+1),∀v:(Bel R.family.book).Field j,
      cost R.family v≤M → ‖((books (age i)).V j).symm (J (age i).val j v)-v‖≤ε:=by
  let q:=ε/(M+1)
  have hp:0<M+1:=by linarith
  have qp:0<q:=div_pos ep hp
  have b(k:slot R.family D):∀ᶠi in u,
      ‖((books (age i)).V k.1).symm (J (age i).val k.1 (head R.family k))-head R.family k‖≤q:=by
    have lim:=WilsonPhysicalWeakElectedCoordinates.oriented F simple a.day a.rises a.sale
      books shared u age near J a.change k.1 (head R.family k)
    exact (Metric.tendsto_nhds.mp lim q qp).mono fun _ h=>by rw [dist_eq_norm] at h; exact h.le
  filter_upwards [Filter.eventually_all.mpr b] with i basis j v cap
  let U:=(J (age i).val j).trans ((books (age i)).V j).symm
  have entry:(∀k,‖U (Module.finBasis ℂ _ k)-Module.finBasis ℂ _ k‖≤q):=fun k=>basis ⟨j,k⟩
  have fare:=atBasis (Module.finBasis ℂ _) U q entry v
  change ‖U v-v‖≤ε
  apply fare.trans
  change cost R.family v*q≤ε
  calc
    _≤(M+1)*q:=mul_le_mul_of_nonneg_right (cap.trans (le_add_of_nonneg_right zero_le_one)) qp.le
    _=ε:=by dsimp [q];field_simp

end YM.Integration.WilsonPhysicalWeakBoundedFrame
