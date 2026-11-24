import YM.OPE.Compatible.Turbine.Reconcile
/-! Centered atoms across projections. The weights are ultimately always in terms of *real* input choices. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset Extraction Word Spec
open Allot Pixel Arcade Cov Cov.Display
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {X I J' : Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X){U F: Finset X}
    {G:Gauge}{C:Family G}{Λ:Extraction.Order}{S:Table C.book}(T:Final C Λ S)(P:Prescription T.sector.derivatives)(u:X)
set_option quotPrecheck false
local notation "L"=> T.sector.derivatives
local notation "K!"=> Arboreal.trim U u
local notation "H"=>brim D (Arboreal.trim U u)
local notation "V"=>brim D U
local notation "Θ"=>glen D U u
variable (p:X→ S.Tag)(hu:u∈ rest U){b d:ℕ}{φ:Filter I}{s:I→X→ℝ}{r f:I→ℝ}
variable [Fintype J'] (z:I→J'→E4)(w:J'→ S.Tag)(t:I→Viewers T)
variable (Y:Burst D U φ r s){η M c:ℝ}(H':Services C Λ S)(hO:Lanes (F:=Λ) T.sector.derivatives) (A: Allot C)(h:P.Coherent)
variable (a:Mode T.sector.derivatives) (hη:0 < η)(hM:0 ≤ M)(hc:0<c) (hh:1 ≤ b)(hb:d ≤ b)
variable (ht:∀ᶠ i in φ, whenHigh U (schedule C b (η/2) (s i))=schedule C b (η/2) (s i) u∧ aperture D C b 2 (η/2) (r i) (s i) u ≤ schedule C b (η/2) (s i) u-1)
variable {x:I→X→E4} (hx:∀ᶠ i in φ,Ridge (s i) η M D U (away (x i) (x i ⊥)))
local notation "O!" => fun i=> x i ⊥
local notation "X!"=> fun i=>away (x i) (x i ⊥)
local notation "Z!"=>fun i=>away (z i) (x i ⊥)
local notation "p₀"=> fun i:V=>(p i.val).1
local notation "K₀"=> fun (n:ℕ) i=> leverage D U p₀ u (s i) d n
local notation "P₀"=> Ward.expose ∘ p
variable (hy:∀ᶠ i in φ, ClearOf (x i ⊥) (z i) c)
local notation "V₀"=> picked V
local notation "P!"=> P.ope
local notation "g"=>fun (b:Mode L) i=> P.ope b (picked Θ (x i)) (picked Θ (Ward.expose∘p)) (x i u)
local notation "q!"=> fun b: Mode L=> update p u (⟨d,P.loaded b d⟩: S.Tag)
-- crossing costs readable
omit [Fintype X] [PartialOrder X] [OrderBot X] in
lemma elaborate_name (b:Mode L) (d:ℕ): pallet (Ward.expose ∘ p) (wadded T P d b) u= Ward.expose ∘ (update p u (⟨d,P.loaded b d⟩: S.Tag)):=by
   ext1 i; by_cases h:i=u
   · subst i; rw [Function.comp_apply, pallet,update_self,update_self]; rfl
   simp [pallet,h]
include hη hu A H' hO h hM Y hx hh hb ht
lemma printed_west : PaidWeight φ r (K₀ a.fst) (fun i=> P.ope a (picked V (x i)) (picked V (Ward.expose ∘ p)) (O! i)-∑ b'∈bands L d, (g b' i)*P.ope a (picked H (x i)) (picked H (Ward.expose ∘ (q! b'))) (O! i)):=by
   obtain ⟨f,hf,he⟩:= west_stable D T P u (Ward.expose ∘ p) hu Y H' hO A h a hη hM hh hb ht
   have hp := atProfits D u P₀ (n:=a.fst) (d:=d) hu Y
   refine Score.pointwise hf ?_ (by filter_upwards [hp] with i hi; exact mul_nonneg hi.1.le (norm_nonneg _))
   filter_upwards [he,hx] with i hi hx
   refine le_trans (le_of_eq ?_) (hi _ hx)
   refine congr_arg₂ _ rfl (congr_arg norm ?_); unfold stableCoeff; refine congr_arg₂ _ ?_ ?_
   · exact ((sub_self (O! i)) ▸ ope_away P (picked V P₀) (picked V (x i)) (O! i) (O! i) _).symm
   apply Finset.sum_congr rfl; intro j hj; rw [elaborate_name T P]; apply congr_arg₂
   exact (ope_away P (picked Θ P₀) (picked Θ (x i)) (x i u) _ j).symm
   exact ((sub_self (O! i)) ▸ ope_away P _ (picked H (x i)) (O! i) (O! i) _).symm
end YM.OPE.Arboreal.Trace
