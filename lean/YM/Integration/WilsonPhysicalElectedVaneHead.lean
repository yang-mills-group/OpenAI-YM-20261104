import YM.Integration.WilsonPhysicalWeakHomogeneousHome
import YM.Integration.WilsonPhysicalStationSignedBlock

/-! The weak field used at a physical home, evaluated in the real fitted source record
on its very same cap book before both original limits. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalElectedVaneHead
open Function Filter Spec Table Climb PhysMS PhysMS.Frame Trace.Pilot Trace.Target
open PhysicalNext.Repeat.Legato MergeProof.East Next.Rank Next.Rank.East
open WilsonPhysicalAllGradeWeakElection WilsonPhysicalWeakRisingStaff WilsonPhysicalWeakSundial
open WilsonPhysicalWeakWallStaff WilsonPhysicalWeakWallBounded WilsonPhysicalWeakSameStation
open WilsonPhysicalWeakWallBooks WilsonPhysicalStationFiledHead
open WilsonOriginalTwoFlatPublicBooks (Book)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
variable (F:Final R.family f S)(J:ℝ→tower S){H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}
  (simple:G.Simple)(a:Assignment F J H l simple){D T:ℕ}{δ:ℝ}
  (books:(r:{r:ℝ//0<r ∧ r<δ})→ Book F (l:=l) H arch D T r.val)
  (shared:∀r,∃cap:D≤(a.day r.val).1,Shared F (books r) (trim cap (a.day r.val).2))
  {ι:Type*}(u:Filter ι)(age:ι→{r:ℝ//0<r ∧ r<δ})(near:Tendsto (fun i=>(age i).val) u trail)

private theorem age_of_eq {C:Family G}{d e:ℕ}{A:Vane C d}{B:Vane C e}(h:d=e)(v:HEq A B):A.k=B.k:=by
  subst e
  rw [eq_of_heq v]

include shared near in
theorem late:Tendsto (fun i=>(books (age i)).W.k) u atTop:=by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [(a.rises.comp near).eventually_ge_atTop k,near.eventually a.sale] with i grow actual
  obtain ⟨cap,same⟩:=shared (age i)
  have he: (books (age i)).W.k=((a.day (age i).val).2.room.station.k):=
    age_of_eq same.2.1 same.2.2.1
  exact (grow.trans actual.1.live).trans_eq he.symm

abbrev level {r:ℝ}(B:Book F (l:=l) H arch D T r)(d:Fin (D+1)):Fin (B.k+1):=
  ⟨d.val,Nat.lt_succ_of_le ((Nat.le_of_lt_succ d.isLt).trans B.fits)⟩

def recorded {r:ℝ}(B:Book F (l:=l) H arch D T r)(d:Fin (D+1))(v:S.Field d)(N p:ℕ):R.family.label d:=
  (((R.family.S.a B.W.k:ℂ)^d.val)⁻¹) •
    WilsonMeasuredPublicEntranceGridDebit.fitted R d B.W.k N p (((B.rows d).arm true v).source (N,p))

theorem filed {r:ℝ}(B:Book F (l:=l) H arch D T r)(d:Fin (D+1))(v:S.Field d)(N p:ℕ):
    recorded F B d v N p=vote R B.W (level F B d) ((B.V d).symm v) N p:=by
  unfold recorded vote
  rw [((B.rows d).weak v (N,p))]

include shared near in
theorem bills (ε:ℝ)(ep:0<ε):
    ∀ᶠi in u,∀d:Fin (D+1),∀p,fee R d (books (age i)).W.k p≤ε:=by
  have rates:∀d:Fin (D+1),∀ᶠk:ℕ in atTop,∀p,fee R d k p≤ε:=
    fun d=>WilsonPhysicalStationSignedBlock.uniform R d simple ε ep
  exact (late F J simple a books shared u age near).eventually (Filter.eventually_all.mpr rates)

include shared near in
theorem original (ε:ℝ)(ep:0<ε):
    ∀ᶠi in u,∀d:Fin (D+1),∀v:S.Field d,∀N p,let B:=books (age i);B.W.k<N →
      let L:=tagged R B.W (level F B d) ((B.V d).symm v) N p
      (R.family.labels.level d).coeffSize (recorded F B d v N p-L)≤ε*(2*(R.family.labels.level d).coeffSize L):=by
  filter_upwards [bills F J simple a books shared u age near ε ep] with i earned
  dsimp only
  intro d v N p high
  let B:=books (age i)
  let w:=(B.V d).symm v
  let j:=level F B d
  have debt:=WilsonPhysicalStationFiledHead.original R B.W j w (p:=p) B.checked high
  rw [filed F B d v N p]
  exact debt.trans (mul_le_mul_of_nonneg_right (earned d p) (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _=>norm_nonneg _)))

include shared near in
theorem homogeneous (ε:ℝ)(ep:0<ε):
    ∀ᶠi in u,∀d:Fin (D+1),∀v:S.Field d,∀N p,let B:=books (age i); B.W.k<N →
      let w:=(B.V d).symm v
      let y:=Further.CorrectedLift.ladder R.family d w
      ∀h b:ℕ,(∀k,y k≠0 → (R.family.labels.level d).grades k=(h,b)) →
      (R.family.labels.level d).coeffSize ((WilsonPhysicalStationSignedBlock.scale R B.W N p h b)⁻¹ • recorded F B d v N p-y) ≤
      ε*(2*(R.family.labels.level d).coeffSize y):=by
  filter_upwards [bills F J simple a books shared u age near ε ep] with i earned
  dsimp only
  intro d v N p high h b mono
  let B:=books (age i)
  let w:=(B.V d).symm v
  let j:=level F B d
  have debt:=WilsonPhysicalStationSignedBlock.pure R B.W j w (p:=p) B.checked high mono
  rw [filed F B d v N p]
  exact debt.trans (mul_le_mul_of_nonneg_right (earned d p) (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _=>norm_nonneg _)))

end YM.Integration.WilsonPhysicalElectedVaneHead
