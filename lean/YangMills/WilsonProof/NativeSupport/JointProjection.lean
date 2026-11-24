import YangMills.WilsonProof.NativeSupport.JointNonlinearTariff
import YangMills.WilsonProof.NativeSupport.JointShadow

/-! Erase auxiliary ownership after each measured Wilson step. Colliding
copies of one original marker vanish. Distinct copies retain exactly
their old source weight. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Painted
open Finset Marker Extra.Trajectories Packet MarkerSubstitution
open scoped BigOperators Classical
variable {V : Type} [Fintype V] [DecidableEq V]

def plain (p : Ink V) : Poly (YM.Stock.census V) := Poly.send (tag {p.1}) 1

private theorem square (p : Ink V) : plain p * plain p = 0 := by
  by_contra h
  obtain ⟨_,disj,_⟩:=merges_of_tagged_mul h
  exact disjoint_left.mp disj (mem_singleton_self p.1) (mem_singleton_self p.1)

def project : Poly (YM.Stock.census (Ink V)) →+* Poly (YM.Stock.census V) := hom plain square

def faithful (S : Finset (Ink V)) := Set.InjOn Prod.fst (S : Set (Ink V))

private theorem plain_prod (S : Finset (Ink V)) :
    ∏ i∈S,plain i = if faithful S then Poly.send (tag (S.image Prod.fst)) 1 else 0 := by
  let s (i:Ink V) := tag {i.1}
  change (∏ i∈S,Poly.send (s i) (1:ℂ))=_
  split
  next keep =>
    have fit : Fits s S := by
      refine ⟨?_,mem_univ _⟩
      intro i hi j hj ne
      change Disjoint {i.1} {j.1}
      exact Finset.disjoint_singleton.mpr fun e=>ne (keep hi hj e)
    have id : unionTag s S fit = tag (S.image Prod.fst) := by
      apply Subtype.ext
      change S.biUnion (fun i=>{i.1})=_
      ext v
      simp [eq_comm]
    rw [tagged_prod s S fit,id,prod_const_one]
  next refuse =>
    by_contra h
    have fit:=fits_of_tagged_prod s h
    apply refuse
    intro i hi j hj e
    by_contra ne
    exact disjoint_left.mp (fit.1 hi hj ne) (mem_singleton_self _) (mem_singleton.mpr e)

theorem project_send (S : Finset (Ink V)) (h : faithful S) (c : ℂ) :
    project (Poly.send (tag S) c)=Poly.send (tag (S.image Prod.fst)) c := by
  change applyTo plain (Poly.send (tag S) c)=_
  rw [on_send,plain_prod,if_pos h]
  ext p
  simp only [Poly.part_smul,Poly.part_send]
  split <;> simp

theorem projected_part (P : Poly (YM.Stock.census (Ink V))) (T : Finset V) :
    (project P).part (tag T) =
      ∑ S : Finset (Ink V) with faithful S ∧ S.image Prod.fst=T, P.part (tag S) := by
  change (applyTo plain P).part _=_
  simp only [applyTo,Poly.part_sum,Poly.part_smul,plain_prod,sum_filter]
  apply sum_congr rfl
  intro S _
  by_cases keep : faithful S
  · rw [if_pos keep,Poly.part_send]
    by_cases e : S.image Prod.fst=T
    · rw [if_pos (congrArg tag e.symm),if_pos ⟨keep,e⟩,mul_one]
    · rw [if_neg (fun he=>e (congrArg Subtype.val he).symm),if_neg (not_and.mpr fun _=>e),mul_zero]
  · rw [if_neg keep,if_neg (fun h=>keep h.1)]
    change _*0=0
    exact mul_zero _

theorem projected_toll (w : V → ℝ) (S : Finset (Ink V)) (h : faithful S) :
    Poly.toll w (tag (S.image Prod.fst))=Poly.toll (fun i:Ink V=>w i.1) (tag S) := by
  change (∏ v∈S.image Prod.fst,w v)=_
  exact Finset.prod_image h

theorem project_painted (T : Finset V) (y : V) (old : Bool) (c : ℂ) :
    project (Poly.send (tag (T.map (paint y old false))) c)=Poly.send (tag T) c := by
  let q := paint y old false
  have fit : faithful (T.map q) := by
    intro a ha b hb same
    obtain ⟨a,_,rfl⟩:=mem_map.mp ha
    obtain ⟨b,_,rfl⟩:=mem_map.mp hb
    exact congrArg q (show a=b from same)
  have id : (T.map q).image Prod.fst = T := by
    ext x
    constructor
    · rintro h
      obtain ⟨u,hu,rfl⟩:=mem_image.mp h
      obtain ⟨v,hv,rfl⟩:=mem_map.mp hu
      exact hv
    · intro h
      exact mem_image.mpr ⟨q x,mem_map_of_mem q h,rfl⟩
  change applyTo plain (Poly.send (tag (T.map q)) c)=_
  rw [on_send,plain_prod,if_pos fit,id]
  ext p
  simp only [Poly.part_smul,Poly.part_send]
  split <;> simp

/-- The root bill is conserved on the surviving color modes. This
identity permits repeated repainting with a fixed primitive alphabet. -/
theorem projected_mass (w : V → ℝ) (x : V) (c : Finset (Ink V) → ℝ) :
    ∑ T : Finset V with x∈T,Poly.toll w (tag T)*
      (∑ S : Finset (Ink V) with faithful S ∧ S.image Prod.fst=T,c S) =
    ∑ S : Finset (Ink V) with faithful S ∧ x∈S.image Prod.fst,
      Poly.toll (fun i:Ink V=>w i.1) (tag S)*c S := by
  let D := univ.filter (fun T:Finset V=>x∈T)
  change (∑ T∈D,_)=_
  simp only [sum_filter,mul_sum,mul_ite,mul_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro S _
  by_cases h : faithful S
  · simp only [h,true_and]
    rw [sum_ite_eq]
    simp only [D,mem_filter,mem_univ,true_and]
    rw [projected_toll w S h]
  · simp [h]

end YM.Integration.InletSusceptibility.Painted
