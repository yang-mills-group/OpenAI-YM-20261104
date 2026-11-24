import YM.OPE.Compatible.Turbine.Jolt
/-! Pass signed viewer test; uses unselected here. -/
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
local notation "tr'"=>fun (D':Finset X) (n:ℕ) i (p₁:X→S.Tag)=> shadow P n (picked (brim D D') (x i)) (picked (brim D D') (Ward.expose∘p₁)) (O! i)
local notation "Π'"=>fun n i=> Cov.insert S S (O! i) (z i) w n
local notation "ℜ" =>fun (D':Finset X) i (p:X→S.Tag)=> Cov.kernel S (beside (picked (brim D D') (x i)) (z i)) (beside (picked (brim D D') p) w)
include Y hx hη hc hy

lemma restamp (n:ℕ) (pQ:Crown F) (hp:F⊆U) : ∀ᶠ i in φ,stampDelta D T P F (away (x i) (O! i)) P₀ (Z! i) (Ward.expose∘w) none n= ℜ F i p-(Π' n i) (tr' F n i p):=by
   have he:= clear_awayU D (Burst.heal D Y hp pQ) (hx.mono fun i hi=>Ridge.heals D hp _ hi) hη z hy hc |>.2
   filter_upwards [he] with i hi; obtain ⟨he,hi⟩:=hi
   let b:= picked (brim D F) p; let b':= picked (brim D F) (Ward.expose ∘ p); let w':= Ward.expose ∘ w; let Y:= picked (brim D F) (x i); have hz:=spectate T none; simp only [unselected_view] at hz
   unfold stampDelta; rw [unselected_view]; apply congr_arg₂
   · rw [kernel_expose,beside_commutes]; change observe S (beside (away Y (O! i)) _) (beside b' w') = _; dsimp only; rw [beside_away]; exact observe_away S _ _ _ hz.translations he
   unfold Cov.insert
   refine Eq.trans (b:=P.truncated S n Y b' (x i ⊥) (z i) w') ?_ (compatible_shadows (x:=Y) (d:=n) (v:=b') P hz (fun _=>le_rfl) (spectate_ready T none) w' hi).symm
   change P.truncated S n (away Y (O! i)) b' _ _ _ = _; exact (sub_self (O! i)) ▸ trunc_away P _ _ _ _ _ _ _ _ hz hi
include A H' hO h hu hM hh hb ht
lemma printed_east : PaidWeight φ r (K₀ a.fst) (fun i=> ℜ U i p-(∑ b∈bands L d,g b i*ℜ K! i (q! b))-Π' a.fst i (tr' U a.fst i p-∑ b∈bands L d,g b i • tr' K! a.fst i (q! b))):=by
   have hx' := clear_awayU D Y hx hη z hy hc|>.1
   obtain ⟨f,hf,he⟩:= east_stable D T P u P₀ hu (Z!) (Ward.expose ∘ w) (fun _=> none) Y H' hO A h a hη hM hc hx' hh hb ht
   have hp:= atProfits D u P₀ (d:=d) (n:=a.fst) hu Y; have hC := Burst.crown D Y; have hF:= remains U hC ((rest_mem ..).1 hu|>.1)
   refine Score.pointwise hf ?_ (hp.mono fun i hi=> mul_nonneg hi.1.le (norm_nonneg _))
   filter_upwards [he,hx,restamp D T P p z w Y hη hc hx hy a.1 hC (Finset.Subset.refl U),(eventually_all_finset (bands L d)).2 (fun b _=>restamp D T P (q! b) z w Y hη hc hx hy a.1 hF (Finset.filter_subset ..))] with i hi hx hh hm
   refine le_trans (le_of_eq ?_) (hi _ hx)
   apply congr_arg₂ _ rfl; apply congr_arg; unfold stableView; rw [hh,map_sub,map_sum]; simp_rw [map_smul]
   let a' b:= ℜ K! i (q! b); let b' b:=Π' a.fst i (tr' K! a.fst i (q! b))
   have hr: ∑ b∈bands L d,P.ope b (picked Θ (X! i)) (picked Θ P₀) (away (x i) (O! i) u) * stampDelta D T P K! (X! i) (pallet (P₀) (wadded T P d b) u) (Z! i) (Ward.expose ∘ w) none a.fst=
       ∑ b∈bands L d,(g b i*a' b-g b i • b' b):=by
       refine Finset.sum_congr rfl fun b hb=>?_; rw [elaborate_name T P]; dsimp only at *; rw [hm b hb]; change P.ope b (away (picked Θ (x i)) (O! i)) _ _ * (a' b-b' b)=_; change P.ope b _ _ (x i u-O! i) * (a' b-b' b)=_; rw [ope_away]; exact mul_sub ..
   rw [hr, Finset.sum_sub_distrib]; unfold a' b'; abel
end YM.OPE.Arboreal.Trace
