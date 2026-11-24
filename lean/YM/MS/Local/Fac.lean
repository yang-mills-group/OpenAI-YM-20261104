import YM.MS.KoszulSyms
import YM.MS.Local.String

/-!
# Ordered words projected to monomials

Choose label language after this. Only linear normalized products. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Local
open Function Filter Set Finset Koszul Real Momentum Book Plane Submodule
open scoped Topology ContDiff
variable {P A J: Type} {p:Sector A}{v w:ℤ}
def glow (p:Sector A) (n:ℕ) (F:Fin n→Raw A ℂ):Raw A ℂ := match n with
 | 0=>coin 1
 | _+1=> product p (F 0) (glow p _ (F ∘ Fin.succ))
lemma glow_zero (F: Fin 0→Raw A ℂ): glow p 0 F=coin 1:=rfl
lemma glow_add (n:ℕ) (F: Fin (n+1)→Raw A ℂ): glow p (n+1) F=product p (F 0) (glow p n (F∘Fin.succ)):=rfl
lemma glow_cons (n:ℕ) (F:Fin n→ Raw A ℂ) (v:Raw A ℂ): glow p (n+1) (Fin.cons v F)=product p v (glow p n F):=by rw [glow_add,Fin.cons_zero, show Fin.cons v F ∘ Fin.succ = F from by ext; simp]
lemma fac_line (n:ℕ) (F:Fin n → Twig A P): fac (field p) n (line n F) = glow (field p) n (fun i=> Koszul.mono (F i)):= by
    induction n with
    | zero=> ext l; rcases l with _|l <;> simp [line,hit,glow,coin,fac,mask] -- adjust
    | succ n ih=>
      rw [line_bud,glow_add]; ext l; rw [fac_s,scattered]; refine scatter_congr _ l _ _ fun a r _=> ?_; rcases a with _|⟨a,_|_⟩ <;> simp only [pencil, Koszul.mono]
      · exact (zero_mul _).symm
      swap; · exact (zero_mul _).symm
      rw [show D a (bud _ _)= F 0 a • Local.line n (F ∘ Fin.succ) from rfl,map_smul,ih]; rfl

def capped (P:Type) (t:ℤ→ℤ→Set (Twig A P)) (n:ℕ) (v w:ℤ) (p:Sector A): Submodule ℂ (Row A P ℂ):= Submodule.span ℂ {X| ∃ (a b:Fin n→ℤ) (f:Fin n→ Twig A P), (∀ i,f i∈t (a i) (b i))∧∑ i,a i=v ∧∑ i,b i=w ∧ X=glow (field p) n (fun i=>Koszul.mono (f i))} -- parentheses Fin notation
lemma zero_mono : Koszul.mono (0:A→ℂ)=0:= by ext l; rcases l with _|⟨_,_|_⟩ <;> rfl
lemma register_span (t:ℤ→ℤ→Set (Twig A P)) (n:ℕ) (a b:Fin n→ℤ) (F:Fin n→Twig A P) (h:∀ i,F i∈span ℂ (t (a i) (b i))): glow (field p) n (fun i=> Koszul.mono (F i))∈ capped P t n (∑ i,a i) (∑ i,b i) p := by
   induction n with
   | zero=> exact Submodule.subset_span (mem_setOf.mpr ⟨a,b,F,fun i=> i.elim0,rfl,rfl,rfl⟩)
   | succ n ih=>
      rw [glow_add]; let v:= a 0; let w:=b 0; let S:= capped P t (n+1) (∑ i,a i) (∑ i,b i) p
      have he (g:Row A P ℂ) (hg:g∈ capped P t n (∑ i:Fin n,a i.succ) (∑ i:Fin n,b i.succ) p) (f:Twig A P) (hf:f∈t v w) : product (field p) (Koszul.mono f) g∈S:= by
          refine span_induction (p:=fun g _=>product (field p) (Koszul.mono f) g∈S) ?_ (by simp) (fun i j h hh hi hj=>by rw [map_add]; exact add_mem hi hj) (fun i j h hh=> by rw [map_smul]; exact smul_mem _ _ hh) hg
          rintro z ⟨a',b',k',hk,hx,hy,rfl⟩
          refine subset_span (mem_setOf.mpr ⟨Fin.cons v a',Fin.cons w b',Fin.cons f k',?_,?_,?_,?_⟩)
          · intro i; cases i using Fin.cases; simpa using hf; rename_i i; simpa using hk i
          · simp only [Fin.sum_univ_succ,v,Fin.cons_zero,Fin.cons_succ,hx] -- lint
          · simp only [Fin.sum_univ_succ,w,Fin.cons_zero,Fin.cons_succ,hy]
          rw [show (fun i=>Koszul.mono ((Fin.cons f k' : Fin (n+1)→Twig A P) i))=Fin.cons (Koszul.mono f) (fun i=>Koszul.mono (k' i)) from by funext i; cases i using Fin.cases <;> rfl, glow_cons]
      let Z:=glow (field p) n (fun i=> Koszul.mono (F i.succ))
      exact span_induction (p:=fun u _=> product (field p) (Koszul.mono u) Z∈ S)
        (fun u hu=>he Z (ih _ _ _ (fun i=> h i.succ)) u hu) (by rw [zero_mono]; simp)
        (fun i j h hh hi hj=> by simp only [mlin,map_add,LinearMap.add_apply]; exact add_mem hi hj)
        (fun i j h hh=> by simp only [mcost,map_smul,LinearMap.smul_apply]; exact smul_mem _ _ hh) (h 0)

lemma reg_span (t:ℤ→ℤ→Set (Twig A P)) (n:ℕ) (v w:ℤ) (p:Sector A) :
    span ℂ {g: Row A P ℂ|∃ (a b:Fin n→ℤ) (f: Fin n→Twig A P), (∀ i,f i∈ Submodule.span ℂ (t (a i) (b i)))∧ (∑ i,a i)=v ∧ (∑ i,b i)=w ∧ line n f=g} ≤ Submodule.comap (fac (field p) n) (capped P t n v w p):= by rw [span_le]; rintro g ⟨a,b,f,h,rfl,rfl,rfl⟩; rw [SetLike.mem_coe, Submodule.mem_comap, fac_line]; exact register_span t n a b f h
lemma registred {F:Raw A ℂ}(T:Submodule ℂ (Raw A ℂ)) {n:ℕ}(H:Symm p F) (h:rank n F) (he:fac p n F∈ T): F∈ T:= by
    rw [sym_fac p F H,rank_hat _|>.mp h, ← Nat.cast_smul_eq_nsmul ℂ] at he
    rw [← inv_smul_smul₀ (show (n.factorial:ℂ)≠0 from Nat.cast_ne_zero.mpr n.factorial_ne_zero) F]; exact smul_mem _ _ he
end YM.MS.Local
