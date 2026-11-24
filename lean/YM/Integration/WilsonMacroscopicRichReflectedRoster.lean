import YM.PhysMS.Frame.Measured
import YM.Euclid.Pairing
import YM.Integration.WilsonMacroscopicRichTwoLengthSlates

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichReflectedRoster
open YM YM.Spec YM.PhysMS YM.Trace.Pilot YM.Word YM.Table.Pairing YM.OPE YM.OPE.Orbits YM.Climb YM.Spin YM.Next.UVStress
open scoped Topology Classical
open Filter Set
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Spec.Final C f S)
variable (J:ℝ→tower S)(H:Leading F J)

/-- Every issued vector carries its own engineering grade. -/
def labels {n:ℕ} (v:Fin n→(Bel C.book).Tag) (r:ℝ) : Fin n→C.book.Token := fun i=>
  ⟨(v i).1,S.representative _ (J r _ (v i).2)⟩

def physical (r:ℝ)(v:(Bel C.book).Tag):S.Tag:=⟨v.1,J r _ v.2⟩
def reflected (a:Axis)(v:(Bel C.book).Tag):(Bel C.book).Tag:=
  ⟨v.1,(Bel C.book).adj (Maxwell.Free.spin_free C.labels) _ a v.2⟩

@[simp] theorem twice (a:Axis)(v:(Bel C.book).Tag):reflected a (reflected a v)=v:=by
  rcases v with ⟨d,u⟩
  exact congrArg (@Sigma.mk ℕ (Bel C.book).Field d) ((Bel C.book).reflect_twice (Maxwell.Free.spin_free C.labels) d a u)

/-- Reflection transports the actual reported classes at their own radius. -/
theorem joined {n m:ℕ}(a:Axis)(v:Fin n→(Bel C.book).Tag)(w:Fin m→(Bel C.book).Tag)(r τ:ℝ)
    (co:∀i:Fin n,realH F.room.kernel.spin (Maxwell.Free.spin_free C.labels) (J r (v i).1)):
    S.classTokens ∘ tied (labels J v r) (labels J w τ) a=
      Fin.append (fun i=>physical J r (reflected a (v i))) (fun j=>physical J τ (w j)):=by
  funext i;refine Fin.addCases ?_ ?_ i
  · intro j
    change S.classTokens (tied (labels J v r) (labels J w τ) a (Fin.castAdd m j))=_
    rw [show tied (labels J v r) (labels J w τ) a (Fin.castAdd m j)=C.book.reflectedToken a (labels J v r j) from Fin.append_left ..,Fin.append_left]
    change @Sigma.mk ℕ S.Field (v j).1 (S.project _ (C.book.adj _ a (S.representative _ (J r _ (v j).2))))=_
    rw [←S.adj_project F.room.kernel.spin,S.rep]
    have eq := (co j).1 (Signed.mirror a) ((Bel C.book).conj (Maxwell.Free.spin_free C.labels) _ (v j).2)
    rw [(co j).2] at eq
    exact congrArg (@Sigma.mk ℕ S.Field (v j).1) eq.symm
  · intro j
    change S.classTokens (tied (labels J v r) (labels J w τ) a (Fin.natAdd n j))=_
    rw [show tied (labels J v r) (labels J w τ) a (Fin.natAdd n j)=labels J w τ j from Fin.append_right ..,Fin.append_right]
    exact congrArg (@Sigma.mk ℕ S.Field _) (S.rep _ _)

def doubled {n:ℕ} (a:Axis)(v:Fin n→(Bel C.book).Tag) : Fin (n+n)→(Bel C.book).Tag :=
  Fin.append (reflected a ∘ v) v

include H in
private theorem bounded {n:ℕ}(d:Caps n)(v:MaxwellSlots C d)(K:Set (Points n))
    (compact:IsCompact K)(safe:K⊆conf n):
    ∃M:ℝ,0≤M ∧ ∀ᶠ r in trail,∀x∈K,‖measured F none (J r) v r x‖≤M := by
  obtain ⟨C₀,hC⟩:=compact.exists_bound_of_continuousOn (fun x hx=>(WickGoal_tied v (safe hx)).continuousAt.continuousWithinAt)
  refine ⟨max 0 C₀+1,by positivity,?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (H.lead n d v 0 K compact safe) 1 zero_lt_one] with r h
  intro x hx
  specialize h x hx
  rw [dist_comm,dist_eq_norm] at h
  rw [show iteratedFDeriv ℝ 0 (measured F none (J r) v r) x-iteratedFDeriv ℝ 0 (WickGoal v) x=
    iteratedFDeriv ℝ 0 (measured F none (J r) v r-WickGoal v) x from by ext z;simp,norm_iteratedFDeriv_zero] at h
  calc
    _ ≤ ‖measured F none (J r) v r x-WickGoal v x‖+‖WickGoal v x‖ := norm_le_norm_sub_add _ _
    _ ≤ 1+max 0 C₀ := add_le_add h.le ((hC x hx).trans (le_max_right _ _))
    _ = _ := add_comm ..

private theorem scaled {n:ℕ}{x:Points n}{a:Axis}(h:single x a){r:ℝ}(hr:0<r):single (r•x) a := by
  refine ⟨?_,fun i=>?_⟩
  · intro i j hi
    apply h.1
    exact (smul_right_injective _ hr.ne') hi
  · exact mul_pos hr (h.2 i)

include H in
/-- The reflected Schwinger diagonal of these physical fields is bounded on each compact in the positive half space. -/
theorem original {n:ℕ}(a:Axis)(v:Fin n→(Bel C.book).Tag)(K:Set (Points n))
    (compact:IsCompact K)(safe:∀x∈K,single x a):
    ∃M:ℝ,0≤M ∧ ∀ᶠr in trail,∀x∈K,
      ‖S.gram a (realize (labels J v r) (r•x)) (realize (labels J v r) (r•x))‖≤M := by
  let t:=doubled a v
  let A := (fun x:Points n=>closedUp a x x) '' K
  have hA:IsCompact A:=compact.image ((pairIso a).symm.continuous.comp (continuous_id.prodMk continuous_id))
  have cA:A⊆conf (n+n):=by rintro _ ⟨x,hx,rfl⟩;exact spans (safe x hx) (safe x hx)
  obtain ⟨M,hM,bill⟩:=bounded F J H (fun i=>(t i).1) (fun i=>(t i).2) A hA cA
  have co:∀ᶠr in trail,∀i:Fin n,realH F.room.kernel.spin (Maxwell.Free.spin_free C.labels) (J r (v i).1):=
    Filter.eventually_all.2 (fun i=>H.equivariant (v i).1)
  refine ⟨M,hM,?_⟩
  filter_upwards [bill,co,self_mem_nhdsWithin] with r fee co hr
  intro x hx
  have xp:=scaled (safe x hx) (show 0<r from hr)
  have fold:closedUp a (r•x) (r•x)=r•closedUp a x x := (pairIso a).symm.map_smul r (x,x)
  have booked:S.classTokens ∘ tied (labels J v r) (labels J v r) a=fun i=>physical J r (t i) := by
    rw [joined F J a v v r r co]
    funext i;refine Fin.addCases ?_ ?_ i
    · intro j;rw [Fin.append_left,show t (Fin.castAdd n j)=reflected a (v j) from Fin.append_left ..]
    · intro j;rw [Fin.append_right,show t (Fin.natAdd n j)=v j from Fin.append_right ..]
  rw [displacement S F.room.kernel.laws.toSymmetric _ _ xp xp,
    ←S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) (spans xp xp),booked,fold]
  exact fee _ (mem_image_of_mem _ hx)

end YM.Integration.WilsonMacroscopicRichReflectedRoster
