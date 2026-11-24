import YM.Integration.WilsonPhysicalElectedVaneHead
import YM.Integration.WilsonPhysicalVaneBasis

/-! A finite signed determining family for the original weak ingress. Every column has
its own authentic engineering and angular units and is read in the very same booked Vane. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalAbsoluteVaneDirections
open Function Filter Spec Table Climb PhysMS PhysMS.Frame Trace.Pilot Trace.Target
open PhysicalNext.Repeat.Legato Next.Rank Next.Rank.East Further.CorrectedLift
open WilsonPhysicalAllGradeWeakElection WilsonPhysicalWeakWallStaff WilsonPhysicalWeakSameStation WilsonPhysicalWeakWallBooks
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonPhysicalElectedVaneHead (recorded level)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
variable (F:Final R.family f S)(J:ℝ→tower S){H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}
  (simple:G.Simple)(a:Assignment F J H l simple){D T:ℕ}{δ:ℝ}
  (books:(r:{r:ℝ//0<r ∧ r<δ})→ Book F (l:=l) H arch D T r.val)
  (shared:∀r,∃cap:D≤(a.day r.val).1,Shared F (books r) (trim cap (a.day r.val).2))
  {ι:Type*}(u:Filter ι)(age:ι→{r:ℝ//0<r ∧ r<δ})(near:Tendsto (fun i=>(age i).val) u trail)

def column {r:ℝ}(B:Book F (l:=l) H arch D T r)(d:Fin (D+1))(N p:ℕ)(e:(R.family.labels.level d).Index):R.family.label d:=
  (WilsonPhysicalStationSignedBlock.scale R B.W N p ((R.family.labels.level d).grades e).1 ((R.family.labels.level d).grades e).2)⁻¹ •
  recorded F B d ((B.V d) (WilsonPhysicalVaneBasis.field R.family d e)) N p

def native {r:ℝ}(B:Book F (l:=l) H arch D T r)(d:Fin (D+1))(N p:ℕ)(x:(Bel R.family.book).Field d):R.family.label d:=
  ∑e,(ladder R.family d x) e • column F B d N p e

def variation (d:Fin (D+1))(x:(Bel R.family.book).Field d):ℝ:=
  ∑e,‖(ladder R.family d x) e‖*(R.family.labels.level d).coeffSize (ladder R.family d (WilsonPhysicalVaneBasis.field R.family d e))

private theorem page {d:ℕ}{V:Type*}[Fintype V](β:V→ℂ)(c:V→R.family.label d)(w:V→ℝ)
    (bounds:∀e,(R.family.labels.level d).coeffSize (c e)≤w e):
    (R.family.labels.level d).coeffSize (∑e,β e • c e)≤∑e,‖β e‖*w e:=by
  let K:=R.family.labels.level d
  calc
    _=∑k,‖∑e,β e*(c e k)‖:=by simp [Labels.Frame.coeffSize]
    _≤∑k,∑e,‖β e*(c e k)‖:=Finset.sum_le_sum fun _ _=>norm_sum_le _ _
    _=∑e,‖β e‖*K.coeffSize (c e):=by rw [Finset.sum_comm];simp [K,Labels.Frame.coeffSize,Finset.mul_sum]
    _≤_:=Finset.sum_le_sum fun e _=>mul_le_mul_of_nonneg_left (bounds e) (norm_nonneg _)

include shared near in
theorem original (ε:ℝ)(ep:0<ε):
    ∀ᶠi in u,∀d:Fin (D+1),∀N p,(books (age i)).W.k<N → ∀x:(Bel R.family.book).Field d,
      (R.family.labels.level d).coeffSize (native F (books (age i)) d N p x-ladder R.family d x)≤2*ε*variation (R:=R) d x:=by
  filter_upwards [WilsonPhysicalElectedVaneHead.homogeneous F J simple a books shared u age near ε ep] with i served d N p high x
  let B:=books (age i)
  let seed:=(WilsonPhysicalVaneBasis.field R.family d)
  let y:=ladder R.family d x
  let L:=ladder R.family d
  have each (e:(R.family.labels.level d).Index):
      (R.family.labels.level d).coeffSize (column F B d N p e-L (seed e))≤ε*(2*(R.family.labels.level d).coeffSize (L (seed e))):=by
    have sent:=served d ((B.V d) (seed e)) N p high
    dsimp only at sent
    have same:((books (age i)).V d).symm ((B.V d) (seed e))=seed e:=(B.V d).symm_apply_apply _
    rw [same] at sent
    exact sent _ _ (WilsonPhysicalVaneBasis.pure R.family d e)
  have complete:∑e,y e • L (seed e)=L x:=by
    simpa only [map_sum,map_smul] using congrArg L (WilsonPhysicalVaneBasis.resolve R.family d x)
  change (R.family.labels.level d).coeffSize ((∑e,y e • column F B d N p e)-L x)≤_
  rw [←complete,←Finset.sum_sub_distrib]
  simp only [←smul_sub]
  calc
    _≤∑e,‖y e‖*(ε*(2*(R.family.labels.level d).coeffSize (L (seed e)))):=
      page y _ _ each
    _=_:=by unfold variation;rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro e _;change ‖y e‖*(ε*(2*_))=(2*ε)*(‖y e‖*_);ring

end YM.Integration.WilsonPhysicalAbsoluteVaneDirections
