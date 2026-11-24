import YM.OPE.Compatible.Turbine.Mites
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
include hx hη Y hu
lemma clear_castle : ∀ᶠ i in φ,Covered S (s i u) (picked Θ (x i)) (x i u):=by
   have hU:u∈ U := (rest_mem ..).mp hu|>.2
   have hg:= (Y.fresh η hη).fade u hU
   obtain ⟨-,hw⟩:= finish_view D Y hx hη (Finset.Subset.refl U) (Burst.crown D Y)
   filter_upwards [hx,hw,hg.eventually (valid_geometry (S:=S) (I:=↥Θ) M)] with i hi hm hV
   refine hV _ _ (hm.comp (show Injective (fun i:Θ=> (⟨i.val,(mem_filter.mp i.2).1⟩:V)) from fun _ _ h=> Subtype.ext (congr_arg (Subtype.val:V→X) h))) ?_
   intro j; obtain ⟨hh,hJ⟩:=Finset.mem_filter.mp j.2; have ht:=hi.near u j.val hU (Finset.mem_union_right _ hh) hJ; unfold away at ht; rw [sub_sub_sub_cancel_right,norm_sub_rev] at ht; exact ht
local notation "F'"=> partQ u U
local notation "X'"=> nestle D u
local notation "T₀"=> Tones T
local notation "β!"=> fun n i=>shortInk D U p₀ u (s i) n
omit hx hη Y in
lemma home_priced : let F:= home D u ((rest_mem ..).1 hu|>.2); ∀ (s:X→ℝ)(d:ℕ), costed X' F' d (Sigma.fst ∘ (picked Θ p ∘ F)) (s ∘ Subtype.val)= shortInk D U p₀ u s d :=by
    intro E s d; exact congr_arg (·/(s u)^d) (vale_area D u ((rest_mem ..).1 hu|>.2) p₀ s (Sigma.fst ∘ picked Θ p) (fun _=>rfl))
include A H' hO hM
lemma glen_bill (c:T₀): PaidWeight φ r (fun i=> shortInk D U p₀ u (s i) c.fst) (fun i=> shoot D T U u c (s i) (x i) p):=by
    have hu':u∈U:= (rest_mem ..).mp hu |>.2
    let E:=home D u hu'; have hh:=below D u hu' Y; have he:= hx.mono fun i hi=> notch D u hu' hi
    let v:= picked Θ p; have hp:=(solid_beam T X' A hO H' hh he hη hM (v ∘ E) c)
    refine Score.congr hp ?_; filter_upwards [clear_castle D (S:=S) u hu Y hη hx] with i hi
    change costed X' F' _ _ _* ‖beam T c (s i u) (picked Θ (x i) ∘ E) _ (x i u)‖= _; rw [beam_perm T v (x i u) _ hi E]
    apply congr_arg₂ _ (home_priced (p:=p) _ _ hu _ _) rfl
include h
lemma glen_prime (d:ℕ) : PaidWeight φ r (fun i=> shortInk D U p₀ u (s i) (d+1)) (fun i=> trunc T d (s i u) (picked Θ (x i)) (picked Θ p) (x i u)-shadow P d (picked Θ (x i)) (picked Θ P₀) (x i u)):=by
    have hu':u∈U:= (rest_mem ..).mp hu |>.2; let E:=home D u hu'; have hh:=below D u hu' Y; have he:= hx.mono fun i hi=> notch D u hu' hi; let v:= picked Θ p; have hp:= ray_tracks T X' A hO H' hh he hη hM (v ∘ E) h d; have hr:= (Y.fresh _ hη).fade u hu'
    refine Score.congr hp ?_; filter_upwards [clear_castle D (S:=S) u hu Y hη hx,hr.eventually self_mem_nhdsWithin,(hr.mono_right nhdsWithin_le_nhds).eventually (ge_mem_nhds (Signal.period_pos (supplies S) d))] with i hi hw hv -- ge_mem
    · let X:= picked Θ (x i); let z:=x i u
      change _ * ‖ray T d (X∘E) (v∘E) z - shadow P d (X∘E) _ z‖ =_
      rw [← trunc_ray T _ (show 0< s i u from hw) hv]; refine congr_arg₂ _ (home_priced (p:=p) _ _ hu _ _) (congr_arg norm (congr_arg₂ _ ?_ ?_))
      · unfold trunc; refine sum_congr rfl fun j _=> congr_arg (· • _) (beam_perm T v _ j hi E)
      unfold shadow; refine sum_congr rfl fun j _=>?_ ; have hE:= P.coefficient_perm (Ward.expose ∘ v) (x:=X) (z:=z) (T.room.kernel.laws.toSymmetric) E j; exact congr_arg (fun t:ℂ=> t • P.loaded j d) hE
end YM.OPE.Arboreal.Trace
