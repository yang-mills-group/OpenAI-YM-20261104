import YM.Integration.WilsonPhysicalPositionUniformBranches
import YM.PertExtension.ReflectFrame

/-! One real physical quotient field and a fixed reflected free measurement
separate all nontrivial branches of the elected bounded-radius transitions.
The field is selected before the radius, ratio or regulators. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionRealBranchPanel
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonPhysicalPositionBornCandidates (operator)
open WilsonPhysicalPositionUniformBranches (change)
open scoped Topology Classical BigOperators
variable {G:Gauge}(C:Family G)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field
local notation "I" => (C.labels.level d).Index
local instance realNorm (d:ℕ):NormedSpace ℝ (D d):=NormedSpace.restrictScalars ℝ ℂ _

def words (d:ℕ):((C.labels.level d).Index→ℝ)→ₗ[ℝ]D d where
  toFun x:=(Bel C.book).project d (fun j=>(x j:ℂ))
  map_add' x y:=by
    rw [←map_add]
    apply congrArg _
    ext j
    exact Complex.ofReal_add _ _
  map_smul' t x:=by
    change (Bel C.book).project d (fun j=>((t*x j:ℝ):ℂ))=t • _
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),←map_smul]
    apply congrArg _
    ext j
    exact Complex.ofReal_mul _ _

theorem real (d:ℕ)(x:(C.labels.level d).Index→ℝ):
    WilsonPhysicalPositionAdmissible.real C d (words C d x)=words C d x:=by
  change (Bel C.book).conj (spin_free C.labels) d ((Bel C.book).project d _)=(Bel C.book).project d _
  rw [Table.conj_project]
  apply congrArg _
  ext j
  exact Complex.conj_ofReal _

theorem detected {d:ℕ}(T:D d→L[ℂ]D d)(h:∀x,T (words C d x)=words C d x):
    T=ContinuousLinearMap.id ℂ (D d):=by
  ext1 v
  obtain ⟨z,rfl⟩:=(Bel C.book).onto d v
  have split:(Bel C.book).project d z=words C d (fun j=>(z j).re)+Complex.I • words C d (fun j=>(z j).im):=by
    unfold words
    change _=(Bel C.book).project d _+Complex.I • (Bel C.book).project d _
    rw [←map_smul,←map_add]
    apply congrArg _
    ext j
    change z j=(z j).re+Complex.I*(z j).im
    rw [mul_comm Complex.I]
    exact (Complex.re_add_im _).symm
  rw [ContinuousLinearMap.id_apply,split,T.map_add,T.map_smul,h,h]

private theorem margin {K:Type*}[Fintype K](w:K→ℝ)(hw:∀k,0<w k):
    ∃γ:ℝ,0<γ ∧ ∀k,4*γ≤w k:=by
  let vals:=insert (1:ℝ) (Finset.univ.image w)
  have live:vals.Nonempty:=Finset.insert_nonempty ..
  have allpos:0<vals.min' live:=by
    obtain b|b:=Finset.mem_insert.mp (vals.min'_mem live)
    · rw [b];exact zero_lt_one
    obtain ⟨a,_,e⟩:=Finset.mem_image.mp b
    exact e ▸ hw a
  refine ⟨vals.min' live/4,by positivity,fun k=>?_⟩
  rw [show 4*(vals.min' live/4)=vals.min' live by ring]
  exact Finset.min'_le vals (w k) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem w (Finset.mem_univ k)))

def fee {d:ℕ}(v:D d)(a:MoveSpace G d):ℝ:=
  PertExtension.Rigidity.Positive.positive C.labels (d:=d) (hierarchy C.labels)
    (v-operator C a v) (v-operator C a v)

theorem original {d:ℕ}(menu:Finset (MoveSpace G d)):
    ∃v:D d,WilsonPhysicalPositionAdmissible.real C d v=v ∧ ∃γ:ℝ,0<γ ∧
      ∀a∈menu,operator C a≠ContinuousLinearMap.id ℂ (D d)→
      4*γ≤fee C v a:=by
  classical
  let active:=menu.filter fun a=>operator C a≠ContinuousLinearMap.id ℂ (D d)
  let K(a:active):=(((operator C a).toLinearMap-LinearMap.id).restrictScalars ℝ ∘ₗ words C d).ker
  have strict(a:active):K a≠⊤:=by
    intro full
    apply (Finset.mem_filter.mp a.2).2
    apply detected C
    intro x
    have hx:=LinearMap.congr_fun (LinearMap.ker_eq_top.mp full) x
    exact sub_eq_zero.mp hx
  obtain ⟨x,out⟩:=(Set.ne_univ_iff_exists_notMem _).mp (fun cover=>
    (Subspace.exists_eq_top_of_iUnion_eq_univ cover).elim fun a h=>strict a h :
    (⋃a:active,(K a:Set ((C.labels.level d).Index→ℝ)))≠Set.univ)
  let v:=words C d x
  let wage(a:active):ℝ:=fee C v a.val
  have pos(a:active):0<wage a:=by
    apply PertExtension.Rigidity.Positive.positive_def
    intro z
    apply out
    apply Set.mem_iUnion.mpr
    exact ⟨a,sub_eq_zero.mpr (sub_eq_zero.mp z).symm⟩
  obtain ⟨γ,hγ,all⟩:=margin wage pos
  refine ⟨v,real C d x,γ,hγ,?_⟩
  intro a ha ne
  let slot:active:=⟨a,Finset.mem_filter.mpr ⟨ha,ne⟩⟩
  exact all slot

end YM.Integration.WilsonPhysicalPositionRealBranchPanel
end
