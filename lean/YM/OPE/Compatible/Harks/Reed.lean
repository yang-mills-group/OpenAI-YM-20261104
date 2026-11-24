import YM.OPE.Compatible.Harks.Hue
/-!
# Filtered linear purchases. Economic records only.Assuring uniform relative control
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap Asymptotics
open scoped Topology BigOperators Classical
variable {E F M:Type}[NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F] {r x b c t q:ℝ}
local notation "A!"=> (E→L[ℝ] E)
variable {a f:ℕ→ E}{g:ℕ→ F}{p:ℕ→ E→L[ℝ] E}
-- flags & sections. layers Fin d disregards possible dim zero.
variable {d k:ℕ}{G:ℕ→Type}[∀ i,NormedAddCommGroup (G i)][∀ i,NormedSpace ℝ (G i)]
structure Cuts (d:ℕ)(μ:ℕ→ℝ)(t A:ℝ)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](G:ℕ→Type)[∀ i,NormedAddCommGroup (G i)][∀ i,NormedSpace ℝ (G i)] where
    flag (i:ℕ) : Submodule ℝ E
    Tap (i:ℕ) : E→L[ℝ] G i
    first (p:E) : p ∈ flag 0
    next (i:ℕ)(h:i<d)(p:E): p∈ flag (i+1) ↔ p∈flag i ∧ Tap i p=0
    closed : IsClosed ((flag d): Set E)
    lift (i:ℕ)(h:i<d) : G i →L[ℝ] E
    rises (i:ℕ)(h:i<d)(v:G i) : lift i h v ∈ flag i ∧ Tap i (lift i h v)=v
    tempo (i:ℕ)(h:i<d):0< μ i
    fast : 0≤ t
    finishes (i:ℕ)(h:i<d): t < μ i
    beats (i j:ℕ)(h:i<j)(hk:j<d): μ j < μ i
variable {μ:ℕ→ℝ}{T:Cuts d μ t x E G}
structure Grooved (T:Cuts d μ t x E G)(p:E→L[ℝ] E):Prop where
    leaves (i:ℕ)(h:i≤d)(v:E) : v∈ T.flag i→ p v∈ T.flag i
    tempo (i:ℕ)(h:i<d)(v:E)(hp:v∈ T.flag i): T.Tap i (p v)=μ i • T.Tap i v
    march (v:E)(hp:v∈ T.flag d): ‖p v‖ ≤ t*‖v‖
    cap : ‖p‖ ≤ x
variable (hp:∀ i, Grooved T (p i)) (i:ℕ)
namespace Cuts
lemma recall (T: Cuts d μ t x E G)(i:ℕ)(hh:i≤d)(j:ℕ)(hj:j≤ i): T.flag i≤ T.flag j:=by
   induction i with
   | zero=> simp [Nat.eq_zero_of_le_zero hj]
   | succ i ih => by_cases h:j=i+1; rw [h]; intro H ht; exact ih (by omega) (by omega) ((T.next _ (by omega) _).1 ht).1
lemma sealing (T:Cuts d μ t x E G)(i:ℕ)(hp:i≤ d): IsClosed ((T.flag i):Set E):=by
   induction i with
   | zero=> rw [Set.eq_univ_iff_forall.mpr T.first]; exact isClosed_univ
   | succ i ih=> rw [show ((T.flag (i+1)):Set E)=↑(T.flag i) ∩ {j|T.Tap i j=0} from Set.ext fun _=>T.next i (by omega) _]; exact (ih (by omega)).inter (isClosed_eq (T.Tap i).continuous continuous_const)
end Cuts
lemma Run.herd (h:Run p a f)(hp:∀ i,Grooved T (p i))(hk:k≤d)(hf:∀ i,f i∈T.flag k)(ha:a 0∈ T.flag k): ∀ i,a i∈T.flag k:=by
    intro i; induction i with | zero=>exact ha| succ i ih=> rw [h]; exact (T.flag _).add_mem ((hp i).leaves k hk _ ih) (hf _)
lemma Run.hero (h:Run p a 0)(hp:∀ i,Grooved T (p i))(hk:k≤d)(ha:a 0∈ T.flag k): ∀ i,a i∈T.flag k:= Run.herd h hp hk (fun _=>(T.flag _).zero_mem) ha
lemma Run.tap (h:Run p a 0)(hp:∀ i, Grooved T (p i))(hk:k<d)(hh:a 0∈ T.flag k):Run (flint (μ k)) (fun i=>T.Tap k (a i)) 0:=by
    intro i; change (T.Tap _) (a _)=(flint (μ k) i) (T.Tap k (a i))+0; rw [h,Pi.zero_apply,add_zero]; rw [(hp i).tempo k hk (a i) (Run.hero h hp hk.le hh i),add_zero]; rfl
end YM.OPE.Hark
