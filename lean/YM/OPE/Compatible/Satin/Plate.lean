import YM.OPE.Compatible.Satin.Weigh
/-!
# Functional estimate on root slot differences

Triad estimate per root layout gives power-signed balance on the complete display. After harvesting physical y, discard it by proving estimates on the same prescription that have *no* y. Tested, filtered, and parent coefficient: budget uses EXACT height departure even if other limbs remain to be nested further.
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
variable (p:X→ C.book.Token)(hu:u∈ rest U){b d d' n:ℕ}{φ:Filter I}{s:I→X→ℝ}{r f:I→ℝ}
variable [Fintype J'] (z:I→J'→E4)(w:J'→ C.book.Token)(t:I→Viewers T)
variable (Y:Burst D U φ r s){η M c:ℝ}(H':Services C Λ S)(hO:Lanes (F:=Λ) T.sector.derivatives) (A: Allot C)(h:P.Coherent)
local notation "p₀"=> fun i:V=>(p i.val).1
local notation "j"=> fun i=>schedule C b η (s i)
local notation "t!"=> fun i=> aperture D C b 2 η (r i) (s i)
local notation "K₀"=> fun (n:ℕ) i=> leverage D U p₀ u (s i) d n
local notation "K₁" => fun i=> shortInk D U p₀ u (s i) d
local notation "K₂"=> fun (n:ℕ) i=> tallInk D U p₀ u (s i) d n
-- syntax. homogeneous horizon chosen implicit from context otherwise include d
-- also a formula for later reading via real ray
local notation "P!"=> picked (brim D U) p
local notation "Π!"=> fun (t:C.book.Token)=>picked H (pallet p t u)
local notation "M1"=> fun (x:X→E4)=>picked Θ x
local notation "M2"=> fun (x:X→E4)=>picked H x
local notation "M0"=> fun (x:X→E4)=>picked V x
local notation "V!"=> fun (x:X→E4) (a:Mode L)=> P.ope a (picked Θ x) (picked Θ p) (x u)
def wadded (d:ℕ)(b:Mode T.sector.derivatives) : C.book.Token:= ⟨d,fullInk T P d b⟩
local notation "F!"=> wadded T P d
def stableCoeff (U:Finset X)(x:X→ E4)(p:X→ C.book.Token) (a:Mode T.sector.derivatives)(d:ℕ):=
    P.ope a (picked (brim D U) x) (picked (brim D U) p) 0 - ∑ b∈ bands T.sector.derivatives d,P.ope b (picked (glen D U u) x) (picked (glen D U u) p) (x u)*P.ope a (picked (brim D (Arboreal.trim U u)) x) (picked (brim D (Arboreal.trim U u)) (pallet p (wadded T P d b) u)) 0
def stampDelta (D':Finset X)(x:X→ E4)(p:X→ C.book.Token)(Z:J'→E4)(w:J'→ C.book.Token)(t: Viewers T) (d:ℕ):= observe (spectator T t) (beside (picked (brim D D') x) Z) (beside (picked (brim D D') p) w)-P.truncated (spectator T t) d (picked (brim D D') x) (picked (brim D D') p) 0 Z w
def stableView (U:Finset X)(x:X→ E4)(p:X→ C.book.Token)(Z:J'→E4)(w:J'→ C.book.Token)(t: Viewers T)(n d:ℕ):= stampDelta D T P U x p Z w t n- ∑ b∈ bands T.sector.derivatives d,P.ope b (picked (glen D U u) x) (picked (glen D U u) p) (x u) * stampDelta D T P (Arboreal.trim U u) x (pallet p (wadded T P d b) u) Z w t n
variable (a:Mode T.sector.derivatives) (hη:0 < η)(hM:0 ≤ M)(hc:0<c) (hy:∀ᶠ i in φ,ClearOf 0 (z i) c)
include A Y H' hO h hu hη hM
lemma crescent {F:I→ℝ}(hf:Round φ r (fun i=>F i*K₁ i)) :
   ∃ g:I→ℝ, Score φ r g∧ ∀ᶠ i in φ,∀ x:X→ E4, Ridge (s i) η M D U x → ∀ v:C.label d,
   (∀ b'∈bands L d, ‖P.ope b' (picked Θ x) (picked Θ p) (x u)-P.test b' d (S.project d v)‖ ≤ F i) → K₀ a.fst i * ‖P.ope a (picked H x) (picked H (update p u (⟨d,v⟩:C.book.Token))) 0-∑ b∈bands L d,P.ope b (picked Θ x) (picked Θ p) (x u)*P.ope a (picked H x) (picked H (pallet p (F! b) u)) 0‖≤g i:=by
   have hC:= Burst.crown D Y; let X' := bands L d; choose f hf' hF using fun t:Mode L => note_gains D T p hC hu A hO H' Y h hη hM a (F! t) -- hF yes along all X; Score multiply sum
   have hx:= hf.up.product (Score.summar X' f (Burst.life D Y) (fun i _=> hf' i)); refine ⟨_,hx,?_⟩; filter_upwards [(eventually_all_finset X').2 (fun i _=>hF i),atProfits (d:=d) (n:=a.fst) D u p hu Y,hf.pos] with i hi he hp x' hz y h
   have has_f (x':X→E4) (v:C.label d) : P.ope a (picked H x') (picked H (pallet p (⟨d,v⟩: C.book.Token) u)) 0=tipMark D T P p d x' U u a (S.project d v):= printed D T P p d x' hC hu v a
   have hV:= compareLinear D T P u x' p d (by assumption) y (fun v=> P.ope a (picked H x') (picked H (pallet p (⟨d,v⟩:C.book.Token) u)) 0) (tipMark D T P p d x' U u a) (has_f x') (fun b=> f b i) he.2.1.le he.2.2.le ((pos_of_mul_pos_left hp he.2.1.le).le) h (fun b hb=> hi b hb x' hz)
   rw [reloaded D u p]; exact hV
include hy hc
lemma cantle {F:I→ℝ}(hf:Round φ r (fun i=>F i*K₁ i)) : ∃ g:I→ℝ, Score φ r g ∧ ∀ᶠ i in φ,∀ x:X→ E4,Ridge (s i) η M D U x → ∀ v:C.label d,
   (∀ b∈ bands L d,‖P.ope b (picked Θ x) (picked Θ p) (x u)-P.test b d (S.project d v)‖≤ F i)→ K₀ a.fst i*‖stampDelta D T P K! x (pallet p (⟨d,v⟩:C.book.Token) u) (z i) w (t i) a.fst-∑ b∈ bands L d,P.ope b (picked Θ x) (picked Θ p) (x u)*stampDelta D T P K! x (pallet p (F! b) u) (z i) w (t i) a.fst‖≤g i:=by
   have hC:= Burst.crown D Y; let q:= trim U u; have hg:= remains U hC ((rest_mem ..).1 hu|>.1); let X':=bands L d; choose f hf' hF using fun a':Mode L=> test_fee D T p hC hu A hO H' Y h hη hM z w t (F! a') a.fst hc hy
   have hx:= hf.up.product (Score.summar X' f (Burst.life D Y) (fun i _=> hf' i)); refine ⟨_,hx,?_⟩; filter_upwards [(eventually_all_finset X').2 (fun i _=>hF i),atProfits (d:=d) (n:=a.fst) D u p hu Y,hf.pos,clear_scene D (M:=M) Y z hg (filter_subset ..) hc hy hη] with i hi he ht hA x' hz v hw
   obtain ⟨Z,hZ⟩:= pole_balance D T P p a.fst d (t i) w hC hu (hA x' hz)
   have hV:= compareLinear D T P u x' p d h v (fun v=> stampDelta D T P K! x' (pallet p (⟨d,v⟩:C.book.Token) u) (z i) w (t i) a.fst) Z hZ (fun b=> f b i) he.2.1.le he.2.2.le ((pos_of_mul_pos_left ht he.2.1.le).le) hw (fun b hb=> hi b hb x' hz)
   rw [reloaded D u p]; exact hV
end YM.OPE.Arboreal.Trace
