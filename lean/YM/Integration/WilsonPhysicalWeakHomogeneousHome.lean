import YM.Integration.WilsonPhysicalWeakBoundedFrame
import YM.Integration.WilsonPositionHomogeneousLeading

/-! The actual positioned original arm and the signed natural weak basis at every real home. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalWeakHomogeneousHome
open Function Filter Spec Table Climb PhysMS PhysMS.Frame Trace.Pilot Trace.Target
open PhysicalNext.Repeat.Legato
open OPE Next.Extract RG.Supply MS MS.Land FVA2 FVA2.Register
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

variable (Z:WilsonPrescription G)(lead:PhysMS.Leading F J)(obeys:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)
variable {ι:Type*}(u:Filter ι)(age:ι→{r:ℝ//0<r ∧ r<δ})(near:Tendsto (fun i=>(age i).val) u trail)

include shared near lead obeys in
theorem direction (j:Fin (D+1))(v:(Bel R.family.book).Field j):
    Tendsto (fun i=>((books (age i)).V j).symm (WilsonPositionHomogeneousFrame.homogeneous F J Z (age i).val j v))
      u (𝓝 v):=by
  let home (i:ι):=WilsonPositionPrescribedLift.field F J Z.store j (age i).val
    (WilsonPositionHomogeneousFrame.change F J Z j (age i).val v)
  have limit:Tendsto home u (𝓝 v):=(WilsonPositionHomogeneousLeading.field F J Z lead obeys simple j v).comp near
  have wallet:Tendsto (fun i=>cost R.family (home i)) u (𝓝 (cost R.family v)):=
    (WilsonPhysicalWeakElectedCoordinates.continuousCost (R:=R) j).continuousAt.tendsto.comp limit
  let M:=max 0 (cost R.family v+1)
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  have bound:=WilsonPhysicalWeakBoundedFrame.original F J simple a books shared u age near M (ε/2)
    (le_max_left ..) (half_pos ep)
  filter_upwards [bound,wallet.eventually_lt_const (lt_add_one _),Metric.tendsto_nhds.mp limit _ (half_pos ep)] with i sold paid small
  have first:=sold j (home i) (paid.le.trans (le_max_right ..))
  have card:dist (((books (age i)).V j).symm (J (age i).val j (home i))) (home i)≤ε/2:=by
    rwa [dist_eq_norm]
  change dist (((books (age i)).V j).symm (J (age i).val j (home i))) v<ε
  exact (dist_triangle _ (home i) _).trans_lt ((add_lt_add_of_le_of_lt card small).trans_eq (add_halves ε))

include shared near lead obeys in
theorem original (M ε:ℝ)(hm:0≤M)(ep:0<ε):
    ∀ᶠi in u,∀j:Fin (D+1),∀v:(Bel R.family.book).Field j,
      cost R.family v≤M →
        ‖((books (age i)).V j).symm (WilsonPositionHomogeneousFrame.homogeneous F J Z (age i).val j v)-v‖≤ε:=by
  let q:=ε/(M+1)
  have hp:0<M+1:=by linarith
  have qp:0<q:=div_pos ep hp
  have b(k:slot R.family D):∀ᶠi in u,
      ‖((books (age i)).V k.1).symm (WilsonPositionHomogeneousFrame.homogeneous F J Z
        (age i).val k.1 (head R.family k))-head R.family k‖≤q:=by
    have lim:=direction F J simple a books shared Z lead obeys u age near k.1 (head R.family k)
    exact (Metric.tendsto_nhds.mp lim q qp).mono fun _ h=>by rw [dist_eq_norm] at h; exact h.le
  filter_upwards [Filter.eventually_all.mpr b] with i basis j v cap
  let U:=(WilsonPositionHomogeneousFrame.homogeneous F J Z (age i).val j).trans ((books (age i)).V j).symm
  have entry:(∀k,‖U (Module.finBasis ℂ _ k)-Module.finBasis ℂ _ k‖≤q):=fun k=>basis ⟨j,k⟩
  have fare:=atBasis (Module.finBasis ℂ _) U q entry v
  change ‖U v-v‖≤ε
  apply fare.trans
  change cost R.family v*q≤ε
  calc
    _≤(M+1)*q:=mul_le_mul_of_nonneg_right (cap.trans (le_add_of_nonneg_right zero_le_one)) qp.le
    _=ε:=by dsimp [q];field_simp

end YM.Integration.WilsonPhysicalWeakHomogeneousHome
