import YM.Frontier6.Bouquet.Geometry.Stars

/-! Full Jacobi normal metric. Center of mass is unweighted per slot and tracked
 separately from directions in this L² metric. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble
open scoped Topology BigOperators Classical InnerProductSpace lp
variable (P: Ensemble)
def mass (U:Finset Slot): Room→L[ℝ] E4:= ∑ i∈U,house i
def centroid (p:Pod): Room→L[ℝ] E4:= (p.card:ℝ)⁻¹ • mass p.val
def dark : Room→ₗ[ℝ] (P→E4):= LinearMap.pi fun p:P=> (mass p.val.val).toLinearMap
def fiber : Place:= entire P.Along ⊓ (dark P).ker
def normal (p:Pod): Place:= fiber (only p)
-- tie typeclass
lemma fiber_entire : fiber P ≤ entire P.Along:= inf_le_left
instance fiber_fin : FiniteDimensional ℝ (fiber P) := FiniteDimensional.of_injective (Submodule.inclusion (fiber_entire P)) (Submodule.inclusion_injective _)
instance (p:Pod) : FiniteDimensional ℝ (normal p):= by unfold normal;infer_instance
instance (p:Pod) : CompleteSpace (normal p):=FiniteDimensional.complete ℝ _
instance : CompleteSpace (fiber P):=FiniteDimensional.complete ℝ _
instance (p:Pod): ProperSpace (normal p):=FiniteDimensional.proper ℝ _
instance : ProperSpace (fiber P):=FiniteDimensional.proper ℝ _
lemma dark_at (x:Room)(p:P): dark P x p= mass p.val.val x:=rfl
lemma fiber_iff (x:Room): x∈ fiber P ↔ x∈ entire P.Along∧ ∀ p∈P.choose, mass p.val x=0:=by
    constructor; intro h; exact ⟨h.1,fun p hp=> congr_fun h.2 (⟨p,hp⟩:P)⟩
    intro h; exact ⟨h.1,(show dark P x=0 from funext fun p=> h.2 p p.property)⟩
lemma normal_iff (p:Pod)(x:Room): x∈ normal p ↔ x∈ entire p.val ∧ mass p.val x=0:=by rw [normal,fiber_iff,along_only]; simp only [only_mem,forall_eq]
lemma mass_eq (U:Finset Slot)(x:Room): mass U x=∑ i∈U,x i:= ContinuousLinearMap.sum_apply ..
lemma centroid_times (p:Pod)(x:Room): (p.card:ℝ) • centroid p x= mass p.val x:=by
    have hs:(p.card:ℝ) ≠0:= by exact_mod_cast p.card_pos.ne'
    unfold centroid; rw [ContinuousLinearMap.smul_apply,smul_smul,mul_inv_cancel₀ hs,one_smul]
lemma mass_away {U:Finset Slot}{i:Slot}(hi:i ∉ U)(x:E4): mass U (occupant i x)=0:=by rw [mass_eq]; exact sum_eq_zero fun j hj=>absentee _ _ _ (by rintro rfl; contradiction)
lemma mass_in {U:Finset Slot}{i:Slot}(hi:i∈ U)(x:E4): mass U (occupant i x)=x:=by
    rw [mass_eq, Finset.sum_eq_single_of_mem i hi]; exact occupancy ..; intro j hj hn; exact absentee _ _ _ hn.symm

def shrink : entire P.Along→ₗ[ℝ] (P→ E4):= dark P ∘ₗ (entire P.Along).subtype
lemma shrink_surj : Surjective (shrink P):=by
    intro y; let z(p:P):= occupant p.val.here (y p); let x:=∑ p:P,z p
    have hx(p:P): z p∈ entire P.Along:= entire_solo ((mem_along ..).mpr ⟨_,p.property,p.val.here_mem⟩) _
    refine ⟨⟨x,Submodule.sum_mem _ (fun p _=> hx p)⟩,funext fun i=>?_⟩
    change mass i.val.val x=y i; unfold x; rw [map_sum,sum_eq_single_of_mem i (mem_univ _), mass_in i.val.here_mem]; -- z unfold
    intro j hj he; exact mass_away (fun hz=> he (serial P j.val.here_mem hz)) _
lemma fiber_dim : 4*P.choose.card + dim (fiber P)= 4*P.Along.card:=by
    let L:=(shrink P); have h:= L.finrank_range_add_finrank_ker; rw [LinearMap.range_eq_top.mpr (shrink_surj P), finrank_top, Module.finrank_pi_fintype] at h;
    let F:= Submodule.inclusion (fiber_entire P); let e:= LinearMap.codRestrict L.ker F (fun i=> show _ ∈ L.ker from i.property.2);
    have he:Bijective e:=by -- inspect naming
        constructor; intro i j hi; exact Submodule.inclusion_injective _ (congr_arg (fun x:L.ker=> (x.val:entire P.Along)) hi)
        intro j; exact ⟨⟨j.val.val,j.val.property,j.property⟩,rfl⟩
    have hv:= (LinearEquiv.ofBijective e he).finrank_eq; unfold dim; rw [hv]; rw [show Module.finrank ℝ (entire P.Along)=_ from entire_dim P.Along] at h; simpa [mul_comm 4] using h -- simplify pi
end YM.Frontier6.Bouquet
