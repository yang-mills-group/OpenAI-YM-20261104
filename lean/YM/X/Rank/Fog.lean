import YM.X.Heat.BCH
/-! Pairing any color-factorized covariance against the same polynomial. The argument extends
 through zero/degenerate covariance and all finite and infinite-leg lists. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Rank
open Function Set Filter Finsupp Maxwell Wick Next Rank.Normal -- possible ambiguous Rank.Normal
open YM.Next YM.Next.Rank.Normal MvPolynomial Heat
open scoped Topology BigOperators Classical
variable {G : Gauge} {S : Finset E4} {s : Finset Stroke} (c : G.ColorIndex)
local notation "K" => YM.Next.Rank.Normal.Symmetric
variable (q : K (Fiber G))
def splitCost {A B : Type*}(q : K (A×B)) : Prop := ∃ v:A→A→ℂ,∀ i, q.cov i=fun k=> if k.2=i.2 then v i.1 k.1 else 0
variable (hq : splitCost q)

lemma split_cost (k : G.ColorIndex) : splitCost (weft k) := ⟨fun x y=>(scov k x y:ℂ),fun i=>funext fun j=> by unfold weft; simp only; split_ifs with h he h he <;> first|rfl|simp_all⟩
lemma split_sum {p q : K (Fiber G)} (hp:splitCost p)(hq:splitCost q): splitCost (p+-q):= by
   obtain ⟨v,h⟩:=hp; obtain ⟨w,h'⟩:=hq; refine ⟨v-w,fun u=>funext fun i=>?_⟩; change p.cov _ _+-q.cov _ _=_; rw [h,h']; by_cases hT:i.2=u.2 <;> simp [hT,sub_eq_add_neg]
def reserve (S:Finset E4)(c : G.ColorIndex): Submodule ℂ (Canvas G) where
  carrier:={p| Fits S p ∧ Silent c p S}
  add_mem' {x y} := by rintro ⟨hx,h⟩ ⟨hy,k⟩; exact ⟨Subalgebra.add_mem _ hx hy, fun W hW=> by rw [mul_add,_root_.map_add,h W hW,k W hW,zero_add]⟩
  smul_mem' {t x} := by rintro ⟨hx,h⟩; exact ⟨(supported ℂ {i:Fiber G| i.1.1∈S}).toSubmodule.smul_mem t hx,fun W hW=> by rw [mul_smul_comm,map_smul,h W hW,smul_zero]⟩ -- term includes forall {x}?
  zero_mem' := ⟨Subalgebra.zero_mem _,fun W _=> by rw [mul_zero,_root_.map_zero]⟩
private lemma T_calc {V:Type*} [DecidableEq V] (s:Finset V)(R:K V)(P:poly V): therm s R P=(1/2:ℂ) • (∑ i∈s,Heat.D (R.cov i)*Heat.D (Pi.single i 1)) P:= by
   unfold therm; rw [LinearMap.smul_apply]; congr!
include hq
lemma therm_at (s:Finset Stroke){p:Canvas G}(hp:p∈ reserve S c) : therm (s.product (Finset.univ)) q p ∈ reserve S c := by
   obtain ⟨v,h⟩:=hq; obtain ⟨h',hP⟩:=hp
   have he : (∑ i∈ (s ×ˢ Finset.univ), Heat.D (q.cov i)*Heat.D (Pi.single i 1)) p = ∑ i∈s, Lap (v i) (Pi.single i 1) p := by
     rw [LinearMap.sum_apply, Finset.sum_product]; refine Finset.sum_congr rfl ?_; intro i hi; rw [lap_at]; refine Finset.sum_congr rfl ?_; intro k _; simp only [Module.End.mul_apply, h,Heat.Da]; have hw : Pi.single (i,k) (1:ℂ)=dip (Pi.single i 1) k := by funext j; rcases j with ⟨z,j⟩; by_cases hx : z=i<;>by_cases hK : j=k<;>simp [dip,hx,hK,Pi.single_apply]
     rw [hw]; congr!
   have hw:(∑ i∈ s, Lap (v i) (Pi.single i 1) p) ∈ reserve S c := Submodule.sum_mem _ (fun i hi=> ⟨Fits.Lap h' _ _, Silent.Lap c hP h' _ _⟩)
   rw [←he] at hw; rw [T_calc]; exact (reserve S c).smul_mem _ hw
lemma milking {p:Canvas G}(hp:p∈ reserve S c) : milk q p∈ reserve S c := by
   let L:= reserve S c; let s:Finset Stroke:= p.vars.image Prod.fst; let u:=s.product (Finset.univ (α:=G.ColorIndex)); let T:= therm u q
   obtain ⟨n,h,hT⟩:= (Heat.flowing u q p (mem_supported.mpr (fun i hi=> (Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hi, Finset.mem_univ i.2⟩)))).exists
   have ht n : (T^n) p∈ L:= by
     induction n with
     | zero=> rw [pow_zero,Module.End.one_apply]; exact hp
     | succ i hi=> rw [pow_succ',Module.End.mul_apply]; exact therm_at c q hq s hi
   rw [← hT, plume,LinearMap.sum_apply]; apply Submodule.sum_mem; intro i _; rw [LinearMap.smul_apply]; exact Submodule.smul_mem _ _ (ht i)
lemma converted {p:Canvas G} (hp:Fits S p)(hv:Silent c p S) : blend q 0 p=0:= by
   have he : milk (q + -(weft c)) p∈ reserve S c:= milking c _ (split_sum hq (split_cost c)) ⟨hp,hv⟩
   have ht:= restrict_lap c _ (show Silent c _ S from (show _ ∧ _ from he).2)
   unfold E at ht; rw [blend_components,warms,show (weft c)+(q + -(weft c))=q from ?_] at ht; exact ht -- order check
   apply YM.Next.Rank.Normal.Symmetric.ext; change (_ + (_ + -_):Fiber G→Fiber G→ℂ)=_; abel
end YM.PositionX.Rank
