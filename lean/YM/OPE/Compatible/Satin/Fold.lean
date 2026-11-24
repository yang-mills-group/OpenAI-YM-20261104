import YM.OPE.Compatible.Satin.Marine
/-!
# Weighted comparison uniform over all geometry on continuum parent. Need purchasing as an eventual condition. OPE smooth comparator unchanged.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset Extraction Word Spec
open Allot Pixel Arcade
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {X I J' : Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X){U F: Finset X}
    {G:Gauge}{C:Family G}{Λ:Extraction.Order}{S:Table C.book}(T:Final C Λ S)(P:Prescription T.sector.derivatives)(u:X)
set_option quotPrecheck false
local notation "L"=> T.sector.derivatives
local notation "K!"=> Arboreal.trim U u
local notation "H"=>brim D (Arboreal.trim U u)
local notation "V"=>brim D U
local notation "Θ"=>glen D U u
variable (p:X→ C.book.Token)(hu:u∈ rest U){b d:ℕ}{φ:Filter I}{s:I→X→ℝ}{r f:I→ℝ}
variable [Fintype J'] (z:I→J'→E4)(w:J'→ C.book.Token)(t:I→Viewers T)
variable (Y:Burst D U φ r s){η M c:ℝ}(H':Services C Λ S)(hO:Lanes (F:=Λ) T.sector.derivatives) (A: Allot C)(h:P.Coherent)
local notation "p₀"=> fun i:V=>(p i.val).1
local notation "K₀"=> fun (n:ℕ) i=> leverage D U p₀ u (s i) d n
local notation "K₁" => fun i=> shortInk D U p₀ u (s i) d
local notation "at!"=> fun i=>schedule C b (η/2) (s i)
local notation "t!"=> fun i=> aperture D C b 2 (η/2) (r i) (s i)
local notation "P!"=> picked (brim D U) p
variable (a:Mode T.sector.derivatives) (hη:0 < η)(hM:0 ≤ M)(hc:0<c) (hy:∀ᶠ i in φ,ClearOf 0 (z i) c)(hh:1 ≤ b)(hb:d ≤ b)
-- range Atlas shifts. New syntax readable; attach z'=root and z=center dynamically; ages active plateau.
local notation "S!"=> Scannable T D U φ r s (η/2) (M+1) 2
include Y
omit Y in
lemma row_crest (F:Finset X)(he:F⊆U)(hp:Crown F) : Row D (Q:=U) (Subtype.val : brim D F→ X):= ⟨fun i=> brim_under D U F he i.2,fun i j h=>brim_apart D F hp i.2 j.2 (Subtype.val_injective.ne h)⟩ -- omit Y
lemma row_vale : Row D (Q:=U) (Subtype.val : glen D U u→ X):= ⟨fun i=> Finset.mem_union_right _ (mem_filter.mp i.2|>.1), fun i j h=> brim_apart D U (Burst.crown D Y) (mem_filter.mp i.2|>.1) (mem_filter.mp j.2|>.1) (Subtype.val_injective.ne h)⟩
def scheduled (i:X)(k:X→ℕ)(F:Finset X)(q:X→ℕ) := whenHigh F k=k i ∧ q i ≤ k i-1
variable (ht:∀ᶠ i in φ, whenHigh U (schedule C b (η/2) (s i))=schedule C b (η/2) (s i) u∧ aperture D C b 2 (η/2) (r i) (s i) u ≤ schedule C b (η/2) (s i) u-1)
include hη in
lemma stamp_cast (F:Finset X)(he:F⊆U)(hp:Crown F)(n:ℕ)(hC:0<c)(hF:∀ᶠ i in φ,ClearOf 0 (z i) c) : Scannable T D U φ r s (η/2) (M+1) 2 (fun i x=>stampDelta D T P F x p (z i) w (t i) n):=by
    let v' := picked (brim D F) p; have hR := row_crest D (U:=U) F he hp; have hw:0<η/2:=by positivity
    have hh:= Scannable.shift D (cast_item D t z v' w Y hR hC hF hw (M:=M+1) _ (Finset.mem_union_left _ (Burst.crown D Y).base)) (show ∀ᶠ i in φ,∀ x:X→E4,Ridge (s i) (η/2) (M+1) D U x→ observe (spectator T (t i)) (beside (picked (brim D F) x) (fun j=> x ⊥+z i j)) (beside v' w)= observe (spectator T (t i)) (beside (picked (brim D F) x) (z i)) (beside v' w) from Eventually.of_forall (fun i x h=> by simp_rw [h.belly,zero_add])); exact Scannable.sub D hh (truncated_cast D t z v' w Y hR P n hC hF hw)
include hη hu
lemma Scan_stable (d:ℕ): Scannable T D U φ r s (η/2) (M+1) 2 (fun _ x=> stableCoeff D T P u U x p a d):=by
    have he:0<η/2:=by positivity
    refine Scannable.sub D (root_cast D Y (picked V p) P a he) (Scannable.summons D _ (fun b _ x=> P.ope b (picked Θ x) (picked Θ p) (x u) * P.ope a (picked H x) (picked H (pallet p (wadded T P d b) u)) 0) ?_)
    intro i hi; have hp:= Burst.crown D Y; have hz:= row_crest D (U:=U) K! (Finset.filter_subset ..) (remains U hp ((rest_mem ..).mp hu|>.1)); let p':= picked H (pallet p (wadded T P d i) u)
    refine Scannable.mul D (to_spectra D (picked Θ p) Y (row_vale D u Y) P he u (mem_union_left _ ((rest_mem ..).mp hu|>.2)) i) (Scannable.shift D (to_spectra D p' Y hz P he ⊥ (Finset.mem_union_left _ hp.base) a) ?_)
    exact Eventually.of_forall fun _ _ hx=> congr_arg _ hx.belly
include A H' hO h hM hh hb ht
lemma west_stable : ∃ f:I→ℝ, Score φ r f∧ ∀ᶠ i in φ,∀ x:X→ E4, Ridge (s i) η M D U x→ K₀ a.fst i*‖stableCoeff D T P u U x p a d‖≤ f i:=by
    obtain ⟨g,hg,hF⟩:=printed_gearing D T P u p hu Y H' hO A h a (by positivity:0<η/2) (by positivity:0≤ M+1) hh hb; obtain ⟨F',hf⟩:=Scan_stable D T P u p hu Y a (M:=M) hη d; exact Auth.encode (B:=b) D A H'.simpleGate Y (earnsExp (n:=a.fst) D u p hu Y) hf (by norm_num) hη hg (by filter_upwards [hF,ht] with i hi hh using hi hh.1 hh.2)
include hc hy
lemma east_stable : ∃ f:I→ℝ, Score φ r f∧ ∀ᶠ i in φ,∀ x:X→E4,Ridge (s i) η M D U x → K₀ a.fst i * ‖stableView D T P u U x p (z i) w (t i) a.fst d‖≤f i:=by
    obtain ⟨g,hg,hF⟩:=printed_frame D T P u p hu z w t Y H' hO A h a (by positivity:0<η/2) (by positivity:0≤ M+1) hc hy hh hb
    have hS:S! (fun i x=> stableView D T P u U x p (z i) w (t i) a.fst d):=by
        have hp:= Burst.crown D Y; have he:0<η/2:=(by positivity); refine Scannable.sub D (stamp_cast D T P p z w t Y hη U (Finset.Subset.refl _) hp a.fst hc hy) (Scannable.summons D _ (fun b i x=>P.ope b (picked Θ x) (picked Θ p) (x u) * stampDelta D T P K! x (pallet p (wadded T P d b) u) (z i) w (t i) a.fst) (fun b _ => ?_))
        exact Scannable.mul D (to_spectra D (picked Θ p) Y (row_vale D u Y) P he u (mem_union_left _ ((rest_mem ..).mp hu |>.2)) b) (stamp_cast D T P _ z w t Y hη K! (Finset.filter_subset ..) (remains U hp ((rest_mem ..).mp hu|>.1)) a.fst hc hy)
    obtain ⟨F',hf⟩:=hS; exact Auth.encode (B:=b) D A H'.simpleGate Y (earnsExp (n:=a.fst) D u p hu Y) hf (by norm_num) hη hg (by filter_upwards [hF,ht] with i hi hh using hi hh.1 hh.2)
end YM.OPE.Arboreal.Trace
