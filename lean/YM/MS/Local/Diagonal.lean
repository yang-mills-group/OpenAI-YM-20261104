import YangMills.WilsonProof.NativeSupport.YM.MS.Local.Occupation
/-!
# Tile spanned by elementary strings of occupancy N∈[0,r]

Proof by attaching one at a time, no even-vs-super flips hidden. `v'=0` strings
carry all nonnegative ghost numbers when nonzero.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Local.BV.Woven
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor Submodule MatrixLet
open Landau Detect
open Complex (I)
open scoped Topology ContDiff
variable {G: Gauge} {f : Grade G} {F : Law G} {h q H k x y a b z : ℤ} {V A : Mover G}
    {r d n : ℕ}

def SplitS (V : Mover G) (h q : ℤ) (r d : ℕ) (F : Law G) := ∃ (f : Fin r→Grade G) (a b: Fin r→ℤ) (v:Fin r→ℕ), (∀ i, (0≤ a i ∧ f i ∈ yields (a i) (b i) ∧ v i ≤ 1 ∧ joint (MatrixLet.one V) (f i) = (v i:ℂ) • f i)) ∧ (∑ i, a i) = h ∧ (∑ i,b i)=q ∧(∑ i,v i)=d ∧ line r f=F
-- Prop eliminates data
lemma cap_occu (hv:SplitS V h q r d F): d ≤ r:= by
   obtain ⟨f,a,b,v,H,x,y,rfl,L⟩:= hv; calc
      _ ≤ ∑ _i:Fin r, 1:= Finset.sum_le_sum fun i _=> (H i).2.2.1
      _ = _:= by simp
lemma atTile (hv:SplitS V h q r d F): F∈ Bed G h q r:= by obtain ⟨p,a,b,v,H,rfl,rfl,h,rfl⟩:=hv; exact tileCub.mpr (line_in mslug ghostNo (fun i=> seedStar.mp (H i).2.1)) -- H includes a!
lemma value_count (X:Calib (MatrixLet.one V) k) (ht:h≤k) (p : Fin r→Grade G) (f : Fin r→ℤ) (g : Fin r→ℤ) (v:Fin r→ℕ) (H0 : ∀ i,0≤f i ∧ p i ∈ yields (f i) (g i) ∧ Count V (p i) = (v i:ℂ) • p i) (hF : h=∑ i,f i) :
       Nop V (line r p) = (↑(∑ i,v i):ℂ) • (line r p):= by
   induction r generalizing h with
   | zero=> simp_rw [Nop,line_zero,LinearMap.add_apply,LinearMap.comp_apply,no,map_zero,Fin.sum_univ_zero,Nat.cast_zero,zero_smul,add_zero]
   | succ r ih=>
       subst h; rw [Fin.sum_univ_succ] at ht
       have he : (∑ i : Fin r, f i.succ)≤k := (le_add_of_nonneg_left (H0 0).1).trans ht
       have hz : f 0≤ k:= (le_add_of_nonneg_right (Finset.sum_nonneg (f:=fun i:Fin r=>f i.succ) fun i _=>(H0 i.succ).1)).trans ht
       rw [line_bud,anticom X (H0 0).2.1 hz,(H0 0).2.2,ih he (p∘Fin.succ) (f∘Fin.succ) (g∘Fin.succ) (v∘Fin.succ) (fun i=>H0 i.succ) rfl, Fin.sum_univ_succ]; simp only [← place_at,map_smul, LinearMap.smul_apply,Function.comp_apply,Nat.cast_add,add_smul]
lemma rate (X:Calib (MatrixLet.one V) k) (ht:h≤k) (hv:SplitS V h q r d F): Nop V F=(d:ℂ) • F:= by
    obtain ⟨p,a,b,v,h0,hx,hy,rfl,rfl⟩:=hv; exact value_count X ht p a b v (fun i=>⟨(h0 i).1,(h0 i).2.1,(h0 i).2.2.2⟩) hx.symm

lemma attach_split (hd : SplitS V h q r d F) (hx:0≤x) (hf:f∈yields x y) (he:n≤1) (hN : Count V f=(n:ℂ) • f): SplitS V (x+h) (y+q) (r+1) (n+d) (bud f F):= by
    obtain ⟨p,a,b,v,H,rfl,rfl,rfl,rfl⟩:=hd
    refine ⟨Fin.cons f p,Fin.cons x a,Fin.cons y b,Fin.cons n v, fun i=>?_,?_,?_,?_,line_cons ..⟩
    refine Fin.cases ?_ (fun i=>?_) i; · simpa [Count] using And.intro hx (And.intro hf (And.intro he (show joint (MatrixLet.one V) f =_ from hN)))
    exact (by simpa only [Fin.cons_succ] using H i)
    all_goals simp [Fin.sum_univ_succ]
variable (h q r V)
def frieze:= Submodule.span ℂ {F: Law G|∃ d, SplitS V h q r d F}
variable {h q r V}
lemma from_split (hd:SplitS V h q r d F): F∈frieze (V:=V) h q r:= subset_span (mem_setOf.mpr ⟨_,hd⟩)
lemma by_split {f:Grade G} (hx:0≤x) (hf:f∈ yields x y) (v: F∈ frieze (V:=V) h q r) (he:n≤1) (hN:Count V f=(n:ℂ) • f): bud f F∈frieze (V:=V) (x+h) (y+q) (r+1):= by
   suffices hp: frieze (V:=V) h q r ≤ Submodule.comap (place _ _ f) (frieze (V:=V) (x+h) (y+q) (r+1)) from hp v
   rw [frieze,span_le]; rintro F ⟨d,hd⟩; exact from_split (attach_split hd hx hf he hN)
lemma Canvas (V:Mover G) (L:Calib (MatrixLet.one V) k) (hx:h≤k): Bed G h q r = frieze (V:=V) h q r := by
   induction r generalizing h q with
   | zero=>
       apply le_antisymm
       · refine bed_le _ fun f x y hf hq hp h0=> from_split (d:=0) ?_
         exact ⟨f,x,y,Fin.elim0,(fun i=>i.elim0),hq,hp,by simp,rfl⟩ -- sum
       rw [frieze,span_le]; rintro F ⟨d,hd⟩; exact atTile hd
   | succ r IH=>
       apply le_antisymm
       · apply bed_le; intro f x y hf hx' hy h0
         subst h q; rw [Fin.sum_univ_succ, Fin.sum_univ_succ,line_bud]; rw [Fin.sum_univ_succ] at hx
         let g:=f 0; let F:=line r (f∘Fin.succ); let Y := frieze (V:=V)
         let X:=x 0; let x' := ∑ i:Fin r,x i.succ; let y':= ∑ i:Fin r,y i.succ; let z:=y 0
         have hx': x' ≤ k:= (le_add_of_nonneg_left (h0 0)).trans hx
         have hX': 0 ≤ x':= Finset.sum_nonneg fun i _=>h0 (Fin.succ i)
         have hq : x 0 ≤ k:= (le_add_of_nonneg_right hX').trans hx
         have hF : F∈frieze (V:=V) x' y' r:= by rw [← IH hx']; exact tileCub.mpr (line_in _ _ (p:=f ∘ Fin.succ) (x:=fun i=>x i.succ) (fun i=> seedStar.mp (hf i.succ)))
         have hc:= L.spectrum hq (hf 0); let t:= Count V g; have ht: Count V t=t:= L.lights (x 0) _ g hq (hf 0)
         have ht' : bud t F∈frieze (V:=V) (X+x') (z+y') (r+1):= by_split (h0 0) (f:=t) hc hF (le_refl 1) (by rw [ht]; simp)
         have hv : bud (g-t) F∈ frieze (V:=V) (X+x') (z+y') (r+1):= by_split (h0 0) (f:=g-t) ((yields (x 0) (y 0)).sub_mem (hf 0) hc) hF (Nat.zero_le 1) (by rw [map_sub,ht, show Count V g=t from rfl]; simp)
         have he : bud g F=bud (g-t) F+bud t F:= by rw [← place_at,← place_at, ←place_at,map_sub, LinearMap.sub_apply]; abel
         change bud g F∈_; rw [he]; exact add_mem hv ht'
       rw [frieze,span_le]; rintro F ⟨d,hd⟩; exact atTile hd
end YM.MS.Local.BV.Woven
