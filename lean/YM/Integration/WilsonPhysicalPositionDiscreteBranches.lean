import YM.Integration.WilsonPhysicalPositionChangeCancellation

/-! Discreteness of the true Born stabilizer on each finite horizon. An
invertible limit which preserves the full free physical prediction is
isolated by the native prescribed position screen. Thus a compact family
of such possible branches is finite, with no extra Lie group assumption. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionDiscreteBranches
open Function Filter Set Maxwell XSpace XSpace.Normalize
open scoped Topology Classical
variable {G:Gauge}{d:ℕ}
local notation "M" => MoveSpace G d

def field (x:M):FieldEnd G d:=stand ((guide G d).symm x)
def preserves (x:M):Prop:=recruit (field x) (reference G d)=reference G d
def shift (a:M):M→ₗ[ℝ] M:=LinearMap.id+WilsonPhysicalPositionChangeCancellation.cost G d a

theorem action (a x:M):field (a+shift a x)=field a ∘ₗ field x:=by
  let A:=(guide G d).symm a
  let B:=(guide G d).symm x
  change stand ((guide G d).symm (a+(x+guide G d (WilsonPhysicalPositionChangeCancellation.cross A B))))=_
  rw [map_add,map_add,LinearEquiv.symm_apply_apply]
  change stand (A+(B+WilsonPhysicalPositionChangeCancellation.cross A B))=_
  rw [←add_assoc]
  exact WilsonPhysicalPositionChangeCancellation.action A B

theorem cancellation {a:M}(h:Injective (field a)):Injective (shift a):=by
  intro x y eq
  have same:field (a+shift a x)=field (a+shift a y):=congrArg (fun z=>field (a+z)) eq
  rw [action,action] at same
  apply (guide G d).symm.injective
  apply Subtype.ext
  apply LinearMap.ext
  intro p
  have pt:field a (field x p)=field a (field y p):=congrArg (fun t:FieldEnd G d=>t p) same
  have e:=h pt
  exact add_left_cancel (show p+((guide G d).symm x).val p=p+((guide G d).symm y).val p from e)

theorem identity (V:Store G):
    ∀ᶠ x:M in 𝓝 0,preserves x→x=0:=by
  let D:=V.survey d
  have tends:Tendsto (fun x:M=>(D.opening.1,x)) (𝓝 0) (𝓝 D.opening):=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  filter_upwards [tends.eventually (D.pathway (V.prepared d))] with x test
  intro hx
  have fit:Fray.SetEq (V.measure d) ((guide G d).symm x) (reference G d):=congrArg (V.measure d).D hx
  have eq: D.itinerary (D.opening.1,x)=D.itinerary D.opening:=by
    simpa only [Fray.opening,Fray.box,LinearEquiv.apply_symm_apply] using (D.means _ _).mp fit
  have chosen:=test.mp eq
  exact chosen.symm.trans (D.ground0 _)

theorem isolated (V:Store G){a:M}(ha:preserves a)(inject:Injective (field a)):
    ∀ᶠ z in 𝓝 a,preserves z→z=a:=by
  let iso:=LinearEquiv.ofBijective (shift a) ⟨cancellation inject,LinearMap.injective_iff_surjective.mp (cancellation inject)⟩
  let back:=fun z:M=>iso.symm (z-a)
  have at0:back a=0:=by simp [back]
  have near:Tendsto back (𝓝 a) (𝓝 0):=by
    rw [←at0]
    exact ((iso.symm.toLinearMap.continuous_of_finiteDimensional).comp (continuous_id.sub continuous_const)).tendsto a
  have atz (z:M):a+shift a (back z)=z:=by
    change a+iso (iso.symm (z-a))=z
    rw [LinearEquiv.apply_symm_apply]
    abel
  filter_upwards [near.eventually (identity (d:=d) V)] with z test
  intro hz
  have actionAt:field z=field a ∘ₗ field (back z):=(congrArg field (atz z).symm).trans (action a (back z))
  have backStays:preserves (back z):=by
    unfold preserves at *
    rw [actionAt,←recruits_comp,ha] at hz
    exact hz
  have equals:=atz z
  rw [test backStays,map_zero,add_zero] at equals
  exact equals.symm

theorem finite (V:Store G)(K:Set M)(compact:IsCompact K)
    (keeps:∀a∈K,preserves a)(inject:∀a∈K,Injective (field a)):K.Finite:=by
  have chosen (a:K):∃U:Set M,IsOpen U ∧ (a:M)∈U ∧ ∀ z∈U,z∈K→z=a:=by
    obtain ⟨U,incl,op,mem⟩:=mem_nhds_iff.mp (isolated V (keeps _ a.property) (inject _ a.property))
    exact ⟨U,op,mem,fun z hz hK=>incl hz (keeps z hK)⟩
  choose U op center single using chosen
  have cover:K⊆⋃a:K,U a:=fun z hz=>mem_iUnion.mpr ⟨⟨z,hz⟩,center ⟨z,hz⟩⟩
  obtain ⟨s,sub⟩:=compact.elim_finite_subcover U op cover
  apply (s.finite_toSet.image (Subtype.val:K→M)).subset
  intro z hz
  obtain ⟨a,mem,belongs⟩:=mem_iUnion₂.mp (sub hz)
  exact ⟨a,mem,(single a z belongs hz).symm⟩

end YM.Integration.WilsonPhysicalPositionDiscreteBranches
end
