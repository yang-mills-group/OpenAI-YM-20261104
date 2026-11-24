import YM.OPE.Compatible.Satin.Plate
/-!
# y is gone. stationary coeff fusion and balance of viewer in authentic grid.
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
variable (p:X→ C.book.Token)(hu:u∈ rest U){b d d':ℕ}{φ:Filter I}{s:I→X→ℝ}{r f:I→ℝ}
variable [Fintype J'] (z:I→J'→E4)(w:J'→ C.book.Token)(t:I→Viewers T)
variable (Y:Burst D U φ r s){η M c:ℝ}(H':Services C Λ S)(hO:Lanes (F:=Λ) T.sector.derivatives) (A: Allot C)(h:P.Coherent)
local notation "p₀"=> fun i:V=>(p i.val).1
local notation "j"=> fun i=>schedule C b η (s i)
local notation "t!"=> fun i=> aperture D C b 2 η (r i) (s i)
local notation "K₀"=> fun (n:ℕ) i=> leverage D U p₀ u (s i) d n
local notation "K₁" => fun i=> shortInk D U p₀ u (s i) d
local notation "K₂"=> fun (n:ℕ) i=> tallInk D U p₀ u (s i) d n
local notation "P!"=> picked (brim D U) p
variable (a:Mode T.sector.derivatives) (hη:0 < η)(hM:0 ≤ M)(hc:0<c) (hy:∀ᶠ i in φ,ClearOf 0 (z i) c)(hh:1 ≤ b)(hb:d ≤ b)
include A Y H' hO h hu hη hM hh hb
lemma printed_gearing : ∃ f:I→ℝ,Score φ r f∧ ∀ᶠ i in φ, whenHigh U (j i)=j i u → t! i u ≤ j i u-1 →∀ x:X→ E4, Ridge (s i) η M D U x → Screened D U C x (t! i) → K₀ a.fst i *‖stableCoeff D T P u U x p a d‖ ≤ f i:=by
   obtain ⟨f,g,hf,hg,hF⟩:= highestCoverage (c:=2) D T A P p u hu hO.toInward H' d (sole (C.book.one 0)) a (Y.fresh _ hη) hM hh hb zero_lt_one h hO.toOutward
   obtain ⟨l,hl,hK⟩:=crescent D T P u p hu Y H' hO A h a hη hM (d:=d) (show Round φ r (fun i=> f i*K₁ i) from hf)
   let K i:= K₀ a.fst i; have hL:Score φ r (fun i=>(g i*K i + g i*K i)+l i) := (hg.up.plus hg.up (Burst.life D Y)).plus hl (Burst.life D Y); refine ⟨_,hL,?_⟩
   filter_upwards [hF,hK,atProfits (n:=a.fst) (d:=d) D u p hu Y] with i hi hg he hp ht x hX hω; obtain ⟨y,t,hV,hK,hA,-⟩:= hi hp ht x hX hω; let z:=update p u (⟨d,y⟩:C.book.Token); let v:= P.ope a (picked H x) (picked H z) 0; let x':=P.ope a (picked V x) (picked V p) 0; let c:=P.test a a.fst (S.project a.fst t);
   have hT:‖x'-v‖ ≤ g i+g i := (le_of_eq (congr_arg norm (sub_add_cancel (x'-v) c|>.symm))).trans ((norm_add_le ..).trans (add_le_add (hA _ ((full_bands ..).2 le_rfl)) hK))
   let U':=stableCoeff D T P u U x p a d; have hp': K i * ‖U'-(x'-v)‖ ≤ l i:=by
       have hv:= hg _ hX y hV; let T':= ∑ b∈bands L d,P.ope b (picked Θ x) (picked Θ p) (x u)* P.ope a (picked H x) (picked H (pallet p (wadded T P d b) u)) 0; change K i *‖x'-T'-(x'-v)‖ ≤ _; rw [sub_sub_sub_cancel_left]; exact hv -- orientation
   have ht' : ‖U'‖ ≤ ‖x'-v‖+‖U'-(x'-v)‖ :=by rw [add_comm]; exact (Eq.trans_le (congr_arg norm (sub_add_cancel U' (x'-v)|>.symm)) (norm_add_le ..))
   change K i * ‖U'‖ ≤_; apply (mul_le_mul_of_nonneg_left ht' he.1.le).trans; rw [mul_add]; exact add_le_add ((mul_le_mul_of_nonneg_left hT he.1.le).trans_eq (by ring)) hp'
include hy hc
lemma printed_frame : ∃ f:I→ℝ,Score φ r f∧ ∀ᶠ i in φ, whenHigh U (j i)=j i u → t! i u ≤ j i u-1 →∀ x:X→ E4,Ridge (s i) η M D U x → Screened D U C x (t! i) → K₀ a.fst i*‖stableView D T P u U x p (z i) w (t i) a.fst d‖≤ f i:=by
   obtain ⟨f,g,hf,hg,hF⟩:= highestCoverage (c:=2) D T A P p u hu hO.toInward H' d w a (Y.fresh _ hη) hM hh hb hc h hO.toOutward
   let X' i:= K₀ a.fst i; let e:= a.fst; let e':ℝ:= (bands L e).card
   obtain ⟨c',hc',hC⟩:= page_total T P w e H'.schedule hc
   obtain ⟨l,hl,hK⟩:=cantle D T P u p hu z w t Y H' hO A h a hη hM hc hy (d:=d) (show Round φ r (fun i=> f i*K₁ i) from hf)
   let V':I→ℝ:=fun i=> g i*X' i
   have hU:Score φ r (fun i=>V' i*(1+e'*c')+l i):= ((show Score φ r V' from hg.up).product (Score.steady _ (Burst.life D Y))).plus hl (Burst.life D Y); refine ⟨_,hU,?_⟩
   filter_upwards [hF,hK,hy, atProfits (n:=a.fst) (d:=d) D u p hu Y] with i hi hh hy he hp hU x hX hR; obtain ⟨y,t',hp',hϕ,hT,hK'⟩:=hi hp hU x hX hR
   let Ξ:= stampDelta D T P K! x (pallet p (⟨d,y⟩: C.book.Token) u) (z i) w (t i) e; let μ:=stampDelta D T P U x p (z i) w (t i) e; let Q:= ∑ b∈ bands L d,P.ope b (picked Θ x) (picked Θ p) (x u) * stampDelta D T P K! x (pallet p (wadded T P d b) u) (z i) w (t i) e
   have hv: ‖μ-Ξ‖≤ g i+e'*(g i*c'):= boundSecond D T P u x p d e h y (z i) w (t i) (hy.inject_both hc) (hK' (z i) hy (t i)) hT ((norm_nonneg _).trans hϕ) (hC _ hy (t i)) -- args
   have hh' : X' i * ‖Ξ-Q‖ ≤ l i:= hh _ hX y hp'
   have hz: ‖μ-Q‖≤ ‖μ-Ξ‖+‖Ξ-Q‖:=by exact (Eq.trans_le (congr_arg norm (sub_add_sub_cancel μ Ξ Q|>.symm)) (norm_add_le ..))
   change X' i*‖μ-Q‖≤ _; apply (mul_le_mul_of_nonneg_left hz he.1.le).trans; rw [mul_add]; exact add_le_add ((mul_le_mul_of_nonneg_left hv he.1.le).trans_eq (by unfold V'; ring)) hh'
end YM.OPE.Arboreal.Trace
