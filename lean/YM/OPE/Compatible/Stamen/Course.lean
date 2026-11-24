import YM.OPE.Compatible.Stamen.Story
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
open Cloud JetS
open scoped ContDiff
variable {v y:fieldX (Shade H)}
open Tensor WardBin
section Roller
variable [DecidableEq I]
local notation "B!"=> Root (Shade H)
abbrev spillQ (a:Finset I)(f:I→ℝ):ℝ:=∏ i∈a,f i
def spellI (a:Finset I)(f g:I→ℝ):ℝ:= ∑ i∈a, g i*spillQ (a.erase i) f
def scrollI (a:Finset I)(f g:I→ℝ):ℝ:= ∑ i∈a,g i*spellI (a.erase i) f g
theorem consign (f g:I→ℝ)(x:I)(a:Finset I)(h:x∉a): spellI (insert x a) f g= g x*spillQ a f+f x*spellI a f g:=by
     rw[spellI,spellI,sum_insert h, Finset.erase_insert h,Finset.mul_sum]; refine congr_arg (_ +·) (sum_congr rfl fun i hi=>?_); unfold spillQ; rw [erase_insert_of_ne (show i≠x from fun hz=>h (hz ▸ hi)).symm, prod_insert (show x∉ a.erase i from fun hx=>h (mem_of_mem_erase hx))]; ring
lemma archive (f g:I→ℝ) (x:I)(a:Finset I)(h:x∉a): scrollI (insert x a) f g=2*g x*spellI a f g+ f x*scrollI a f g:=by
     rw [scrollI, sum_insert h, Finset.erase_insert h]; let sL(i:I):=g x* (g i*spillQ (a.erase i) f)+f x*(g i*spellI (a.erase i) f g); rw [sum_congr rfl (f:=fun i:I=>g i*spellI ((insert x a).erase i) f g) (g:=sL) (fun i hi=>?_)]
     · unfold sL; rw [sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; change _+ (g x * spellI a f g+f x * scrollI a f g)=_;ring
     unfold sL; rw[erase_insert_of_ne (show i≠x from fun hz=>h (hz ▸ hi)).symm, consign _ _ _ _ (show x∉ a.erase i from fun hx=>h (mem_of_mem_erase hx))];ring
lemma robust (a:Finset I)(p:I→Token):let g:=JetS.s∘p; let l:=JetS.l ∘p; let K:=JetS.h∘p
                                               ∏ i∈a,p i=⟨spillQ a g,spellI a g l, spellI a g K+(2:ℝ)⁻¹ * scrollI a g l⟩:=by
     intro g l K; induction a using Finset.induction_on with
     | empty=> simp only[prod_empty,spellI,sum_empty, scrollI,mul_zero,add_zero]; rfl
     | insert i a h ih=> rw [prod_insert h, ih, consign _ _ _ _ h, consign _ _ _ _ h, archive _ _ _ _ h]; apply JetS.eta
                         · simp only [ml_s,spillQ, prod_insert h]; rfl
                         · change _*spellI a g l+_*spillQ a g=_; unfold g l; dsimp only [Function.comp_apply]; ring
                         change _* (spellI a g K+_ * scrollI a g l)+(p i).l* _+_*spillQ a g=_
                         unfold g K l; dsimp only [Function.comp_apply]; ring
end Roller
end YM.OPE.Silt.Phere
