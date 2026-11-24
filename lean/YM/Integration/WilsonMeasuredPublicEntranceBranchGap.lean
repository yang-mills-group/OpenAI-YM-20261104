import YM.Integration.WilsonMeasuredPublicEntranceBranchFlag
import YM.Integration.WilsonMeasuredPublicEntranceRecordedQuotient
import YM.Integration.WilsonPhysicalPositionDirectedTest

/-! A fixed positive branch separation on the actual elected real field and the finite directed rows. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 12000
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceBranchGap
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free XSpace XSpace.Normalize
open PertExtension.Rigidity.Positive
open WilsonPhysicalPositionBornCandidates (operator)
open WilsonPhysicalPositionAdmissible (Native)
open WilsonMeasuredPublicEntranceBranchFlag (inspected)
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field
abbrev Axis (C:Family G)(d:ℕ):=Fin ((Extra.FD.recorded C.labels d).m+1)

def row (C:Family G){d:ℕ}(T:Module.End ℂ ((Bel C.book).Field d))(out src:Axis C d):ℂ:=
  let B:=Extra.FD.recorded C.labels d
  B.b.coord out ((T-1) (B.b src))

def watches (C:Family G){d:ℕ}(out src:Axis C d):Prop:=
  src≠0 ∧ inspected (Extra.FD.recorded C.labels d).w out src

theorem identity {d:ℕ}(T:Module.End ℂ (D d))(native:Native C T)
    (iso:∀x,positive C.labels (hierarchy C.labels) (T x) (T x)=positive C.labels (hierarchy C.labels) x x)
    (checked:∀i j,watches C i j→ row C T i j=0):T=1:=by
  let B:=Extra.FD.recorded C.labels d
  refine WilsonMeasuredPublicEntranceBranchFlag.measured T ?_ (fun x=>positive C.labels (hierarchy C.labels) x x)
    (fun _ hx=>positive_def C.labels (hierarchy C.labels) hx) ?_ iso
  · apply WilsonMeasuredPublicEntranceBranchFlag.nilpotent B.b B.w (T-1)
    · exact WilsonMeasuredPublicEntranceRecordedQuotient.native B T native
    · intro i j h
      by_cases neutral:j=0
      · subst j
        change B.b.coord i (T (B.b 0)-B.b 0)=0
        rw [B.unit_,show T ((Bel C.book).unit d)=(Bel C.book).unit d from native.neutral,sub_self,map_zero]
      · exact checked i j ⟨neutral,h⟩
  · intro x y
    simp only [map_add,map_sub,LinearMap.add_apply,LinearMap.sub_apply]
    ring

private theorem readings {K:Type*}[Fintype K](amount:K→ℝ):
    ∃δ:ℝ,0<δ ∧ ∀k,0<amount k→2*δ≤amount k:=by
  let s:=insert (1:ℝ) ((Finset.univ.filter fun k=>0<amount k).image amount)
  have live:s.Nonempty:=Finset.insert_nonempty .. 
  have good:0 < s.min' live:=by
    obtain eq|hp:=Finset.mem_insert.mp (s.min'_mem live)
    · rw [eq];exact zero_lt_one
    obtain ⟨k,hk,eq⟩:=Finset.mem_image.mp hp
    exact eq ▸ (Finset.mem_filter.mp hk).2
  refine ⟨s.min' live/2,by positivity,fun k hk=>?_⟩
  rw [show 2*(s.min' live/2)=s.min' live by ring]
  exact Finset.min'_le s _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩)))

theorem income (F:Final C f S)(J:ℝ→tower S)(lead:Leading F J)
    {I:Type*}{l:Filter I}[NeBot l]{r t:I→ℝ}
    (hr:Tendsto r l trail){u:ℝ}(hu:0<u)(ht:Tendsto t l (𝓝 u))(pos:∀i,0<t i)
    {d:ℕ}(Z:Module.End ℂ (D d))
    (conv:∀v,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (pos i) v) l (𝓝 (Z v))):
    Native C Z ∧ ∀x,positive C.labels (hierarchy C.labels) (Z x) (Z x)=positive C.labels (hierarchy C.labels) x x:=by
  have hrt:Tendsto (fun i=>t i*r i) l trail:=by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa only [mul_zero] using ht.mul (hr.mono_right nhdsWithin_le_nhds)
    filter_upwards [hr.eventually self_mem_nhdsWithin] with i hi using mul_pos (pos i) hi
  refine ⟨WilsonPhysicalPositionBranchLimits.closed (Y:=fun i=>(Frame.cocycle d J (r i) (t i) (pos i)).toLinearMap) ?_ conv,
    fun x=>(WilsonPhysicalPositionDirectedReturn.original F J lead hr hu ht pos Z conv x).2⟩
  filter_upwards [hr.eventually (WilsonPhysicalPositionCocycleNative.purchased F J lead d),
    hrt.eventually (WilsonPhysicalPositionCocycleNative.purchased F J lead d)] with i a b
  exact WilsonPhysicalPositionCocycleNative.original F J (pos i) a b

/-- Both tolerances and the one real witness are chosen before the two reporter radii. -/
theorem original (F:Final C f S)(J:ℝ→tower S)(lead:Leading F J)(V:Store G)(d:ℕ):
    ∃v:D d,WilsonPhysicalPositionAdmissible.real C d v=v ∧ ∃γ δ:ℝ,0<γ ∧ 0<δ ∧
      ∀{I:Type*}{l:Filter I}[NeBot l]{r t:I→ℝ}{c u:ℝ},0<c→0<u→Tendsto r l trail→Tendsto t l (𝓝 u)→
      (∀ᶠ i in l,t i∈Icc c 1)→∀(pos:∀i,0<t i)(Z:Module.End ℂ (D d)),
      (∀y,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (pos i) y) l (𝓝 (Z y)))→
      Z=1 ∨ ((∃out src,watches C out src ∧ 2*δ≤‖row C Z out src‖) ∧
        4*γ≤positive C.labels (hierarchy C.labels) (v-Z v) (v-Z v)):=by
  obtain ⟨menu,ear⟩:=WilsonPhysicalPositionBranchLimits.original F J lead V d
  obtain ⟨v,real,γ,hγ,gap⟩:=WilsonPhysicalPositionRealBranchPanel.original C menu
  let K:=menu × Axis C d × Axis C d
  let amount(k:K):ℝ:=‖row C (operator C k.1.val).toLinearMap k.2.1 k.2.2‖
  obtain ⟨δ,hδ,margin⟩:=readings amount
  refine ⟨v,real,γ,δ,hγ,hδ,?_⟩
  intro I l hl r t c u hc hu hr ht span pos Z conv
  by_cases eq:Z=1
  · exact Or.inl eq
  obtain ⟨a,ha,hZ⟩:=ear hc hu hr ht span pos Z conv
  have entered:(operator C a).toLinearMap=Z:=hZ
  have ne:operator C a≠ContinuousLinearMap.id ℂ (D d):=fun h=>eq (entered.symm.trans (congrArg ContinuousLinearMap.toLinearMap h))
  obtain ⟨native,born⟩:=income F J lead hr hu ht pos Z conv
  have signal:∃i j,watches C i j ∧ row C Z i j≠0:=by
    by_contra! no
    exact eq (identity Z native born no)
  obtain ⟨i,j,hij,det⟩:=signal
  refine Or.inr ⟨⟨i,j,hij,?_⟩,?_⟩
  · let key:K:=(⟨a,ha⟩,i,j)
    have price:amount key=‖row C Z i j‖:=by dsimp [amount,key];rw [entered]
    rw [←price]
    exact margin key (price.symm ▸ norm_pos_iff.mpr det)
  · have bound:=gap a ha ne
    change 4*γ≤positive C.labels (hierarchy C.labels) (v-(operator C a).toLinearMap v) (v-(operator C a).toLinearMap v) at bound
    rwa [entered] at bound

end YM.Integration.WilsonMeasuredPublicEntranceBranchGap
