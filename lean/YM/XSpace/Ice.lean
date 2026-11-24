import YM.XSpace.Shuttle

/-!
# Wires, finish deleting auxiliary-only contractions
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Legs
open Function Set Filter MvPolynomial Maxwell Maxwell.Free Next.Rank.Normal
open scoped BigOperators Classical
variable {G : Gauge} {K : Symmetric (World G)} {L : Finset (World G)} {S: Finset E4} {P : Pol G}

lemma op_both (x y : Ph) (hx : covers L x) (hy : covers L y) (hp : P∈ Lap.scope L): Lap.op L K (bilocal G x y*P)=
    let V:= ∑ a:G.ColorIndex,K.cov (cellL x a) (cellL y a)
    bilocal G x y*Lap.op L K P + (2:ℂ) • (shuttle K x y P + shuttle K y x P + V • P):=by
  dsimp only; rw [bilocal]; simp_rw [Finset.sum_mul,map_sum]; rw [Finset.sum_smul,rides, rides, ← Finset.sum_add_distrib,← Finset.sum_add_distrib,Finset.smul_sum,← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _=>?_ ; set X':=cellL x a; set Y':=cellL y a
  let f:= X (R:=ℂ) X'; let g:=X (R:=ℂ) Y'; let D:=Lap.op L K
  change D (f*g*P)=_
  rw [mul_assoc,show D (f*(g*P))=_ from Lap.op_comm L _ (hx a) (Subalgebra.mul_mem _ (X_mem_supported.mpr (hy a)) hp), Lap.op_comm L _ (hy a) hp]; unfold g; rw [slit_prod]; simp_rw [← C_mul']; ring
lemma spots_more (x y : Ph): S⊆ Spots S x y:= (Finset.subset_insert y.1 S).trans (Finset.subset_insert ..)
lemma Friends.shaves (h : ColorLaw K) (he : Friends L S P): Friends L S (Lap.op L K P) :=by
  induction he with
  | baby=> rw [Lap.op_at]; simp only [Derivation.map_one_eq_zero,map_zero, Finset.sum_const_zero]; exact friends_zero
  | @joined S P x y hx hy ht ha hb hp ih=>
    have he : Friends L S _ := hp.shuttles x y K h (spots_more x y) (by simp [Spots]) hx ha
    have hh : Friends L S _ := hp.shuttles y x K h (spots_more x y) (by simp [Spots]) hy hb
    rw [op_both _ _ ha hb hp.fit]; exact (Friends.joined _ _ hx hy ht ha hb ih).add (((he.add hh).add ((hp.more (spots_more x y)).smul _)).smul _)
  | add _ _ ih1 ih2=> rw [map_add]; exact ih1.add ih2
  | smul c _ ih=> rw [map_smul]; exact ih.smul _
lemma Friends.warms (h : ColorLaw K) (he : Friends L S P): Friends L S (milk K P):=by
  let V : Submodule ℂ (Pol G) :=
    { carrier:=setOf (Friends L S), zero_mem':=friends_zero, add_mem':=fun h k=> Friends.add h k
      smul_mem':=fun a _ h=> Friends.smul a h }
  exact Lap.stable _ K V (fun _ hp=> Friends.shaves h hp) he.fit he

section cold
variable (S)
def Outside (G : Gauge) : Symmetric (World G) where
  cov x y:= if x.1∈S ∨ y.1 ∈ S then 0 else (Kf G).cov x y
  symm x y:= by simp only [or_comm,(Kf G).symm]

def Cold (G : Gauge) : Symmetric (World G) := Kf G + -(Outside S G) -- covariance cut.
lemma Out_color (e : G.ColorIndex): ColorLaw (-(Outside S G)):=by
  intro x y; by_cases h : x.1∈S ∨ y.1∈S
  · refine ⟨0,fun i j=>?_⟩; rw [ite_self]; change -(if x.1∈S ∨ y.1∈S then (0:ℂ) else _)=_; rw [if_pos h,neg_zero]
  have he i j: (-(Outside S G)).cov (cellL x i) (cellL y j)= -((Kf G).cov (cellL x i) (cellL y j)):=by
    change -(if x.1∈S ∨ y.1∈S then (0:ℂ) else _)=_; rw [if_neg h]
  simp_rw [he]
  by_cases H:x.1=y.1
  · use 0; intro i j; rw [ite_self]; unfold cellL lit; rw [H,empty_self,neg_zero]
  use -(fare e x.2 y.2 (x.1-y.1):ℂ); intro a b; rw [show (Kf G).cov (cellL x a) (cellL y b)= _ from colors e H ⟨0,x.2⟩ ⟨0,y.2⟩ a b]; split_ifs with h <;> simp_all

variable {S} (h : P∈Room G S)
include h 
lemma theory (R : Pol G): milk (-(Outside S G)) (P*R)=P*milk (-(Outside S G)) R:=by
  rw [Room,supported_eq_range_rename] at h; rw [AlgHom.mem_range] at h; obtain ⟨q,rfl⟩:= h
  let M:= -(Outside S G); let Z:=(Prod.fst (α:=E4) (β:=Paint G) ⁻¹' (S:Set E4)); let f:= rename (R:=ℂ) (Subtype.val (p:=fun z:World G=> z∈Z))
  change milk M (f q*R)= f q*milk M R
  induction q using MvPolynomial.induction_on with
  | C c=> rw [show f (C c)=C c from rename_C .., drink]
  | add p q hp hq=> rw [map_add, add_mul,add_mul,map_add,hp,hq]
  | mul_X p i hp=>
    have he : M.cov i.val=0:=by
      funext x; change -(if i.val.1∈S ∨ x.1∈S then (0:ℂ) else _)=0; rw [if_pos (Or.inl (show i.val.1∈S from i.property)),neg_zero]
    rw [mul_comm p,show f (X i*p) = f (X i)*f p from map_mul f _ _,show f (X i)=X _ from rename_X .., mul_assoc, feeds, he, slit_zero, add_zero,hp,mul_assoc]
end cold

lemma Frozen {R : Pol G} (e : G.ColorIndex) (h : Friends L S R) (hp : P∈Room G S) (hs : Silent S P):
    Next.Rank.Normal.blend (Cold S G) 0 (R * P)=0:=by
  have he:= (h.warms (Out_color S e)).acts e P hp hs
  unfold receive at he; rw [mul_comm _ P,← theory hp, blend_components, Next.Rank.Normal.warms,mul_comm P _] at he; exact he
end YM.XSpace.Legs
