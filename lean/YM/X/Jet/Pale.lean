import YM.Pert.Position.Implicit
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
/-!
Standard smooth jet calculus for formal power series in the physics comparison. `Word a` unrestricted coefficient sequence; all composition at the formal level (ordinary Taylor normalized derivatives).
Models relation `Act n a f` applies on bidirectional germ at 0 (no t parameter convergence claim as n→∞).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PositionX.Jet
open Function Filter Set
open scoped Topology ContDiff BigOperators Classical
universe u v w
abbrev Word (α: Type*) := ℕ→α
def pair {α β : Type*}(a:Word α)(b:Word β):Word (α × β):= fun i=>(a i,b i)
def delay {E : Type*} [AddCommMonoid E][Module ℝ E] (a:Word E)(n:ℕ)(t:ℝ) : E:= ∑ i∈Finset.range (n+1), t^i • a i

def just {E : Type*} [Zero E](v:E):Word E:= fun i=> if i=0 then v else 0
def turn {E : Type*}[AddCommMonoid E][Module ℝ E](a:Word E):Word E:=fun i=> (-1:ℝ)^i • a i
@[simp] lemma turn_zero {E : Type*}[AddCommMonoid E][Module ℝ E](a:Word E):turn a 0=a 0:= by rw [turn,pow_zero,one_smul]
lemma delay_map {E X : Type*}[AddCommMonoid E][AddCommMonoid X][Module ℝ E][Module ℝ X](a:Word E)(L:E→ₗ[ℝ] X)(n:ℕ)(t:ℝ): L (delay a n t)=delay (L ∘ a) n t:= by unfold delay; rw [map_sum]; simp_rw [map_smul]; rfl
lemma delay_zero {E : Type*}[AddCommMonoid E][Module ℝ E](a:Word E)(n:ℕ) : delay a n 0=a 0:= by
   unfold delay; rw [Finset.sum_eq_single_of_mem 0 (by simp)]; simp; intro k hk he; simp [he]
lemma delay_turn {E : Type*}[AddCommGroup E][Module ℝ E](a:Word E)(n:ℕ)(t:ℝ): delay (turn a) n t=delay a n (-t) := by unfold delay turn; apply Finset.sum_congr rfl; intro i hi; rw [smul_smul,← mul_pow];simp

section
variable {E : Type u} {G : Type v} {F : Type w} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup G][NormedSpace ℝ G][NormedAddCommGroup F][NormedSpace ℝ F]
variable {a:Word E} {b:Word F} {c:Word G}{n k:ℕ} {f f' : ℝ→E}{g:ℝ→F}

def someJ (f:ℝ→E)(i:ℕ):E:= ((i.factorial:ℝ))⁻¹ • iteratedDeriv i f 0
@[simp] lemma someJ_zero (f:ℝ→E) : someJ f 0=f 0:= by simp [someJ]
def run (f:E→F)(a:Word E)(i:ℕ):F:= someJ (f ∘ delay a i) i
@[simp] lemma run_zero (f:E→F)(a:Word E): run f a 0 = f (a 0):= by rw [run,someJ_zero,Function.comp_apply,delay_zero]

def Fits (n:ℕ)(f:ℝ→E)(a:Word E) : Prop:= ∀ i≤n,someJ f i=a i
structure Act (n:ℕ)(f:ℝ→E)(a:Word E):Prop where
   nice : ContDiffAt ℝ ω f 0
   writes : Fits n f a
open ContDiffAt
namespace Act
variable (ha:Act n f a)(hb:Act n g b)
lemma swell (a:Word E){k:ℕ}(h:n≤k): Act n (delay a k) a := ⟨(Pert.Position.curve_diff a k).contDiffAt,fun i hi=>by
   rw [someJ,show delay a k=Pert.Position.curve a k from rfl,Pert.Position.curve_deriv a (hi.trans h)]; exact inv_smul_smul₀ (by positivity) _⟩
lemma shrink (ha:Act n f a)(h:k≤n): Act k f a:= ⟨ha.nice,fun i hi=>ha.writes i (hi.trans h)⟩
lemma realizes {f f':ℝ→E} (h:f =ᶠ[𝓝 0] f')(ha:Act n f a): Act n f' a := ⟨ha.nice.congr_of_eventuallyEq h.symm,fun i hi=> by rw [←ha.writes i hi, someJ,someJ,h.iteratedDeriv_eq]⟩ -- tactic direction?
include ha
lemma zero : f 0=a 0:= by rw [← someJ_zero f]; exact ha.writes _ (Nat.zero_le _)
lemma actual (i:ℕ)(hi:i≤n): iteratedDeriv i f 0=(i.factorial:ℝ) • a i:= by rw [←ha.writes _ hi,someJ,smul_inv_smul₀ (by positivity)]
lemma transit {m:E→F}(hm:ContDiffAt ℝ ω m (a 0)): Act n (m ∘ f) (run m a) := by
   constructor
   · exact ContDiffAt.comp _ (ha.zero.symm ▸ hm) ha.nice
   intro i hi; let g:=delay a i; have hg : Act i g a:= swell a le_rfl
   have he(w:ℝ→E)(h:Act i w a) : someJ (m ∘ w) i=((i.factorial:ℝ))⁻¹ • (∑ q:OrderedFinpartition i, iteratedFDeriv ℝ q.length m (a 0) fun j=> ((q.partSize j).factorial:ℝ) • a (q.partSize j)) := by
       rw [someJ, iteratedDeriv_vcomp_eq_sum_orderedFinpartition (by rw [h.zero]; exact hm) h.nice (show (↑i:WithTop ℕ∞)≤ω from le_top), h.zero]
       congr 1; apply Finset.sum_congr rfl; intro q hq; apply congr_arg (iteratedFDeriv ..); funext j; rw [h.actual _ (q.partSize_le j)]
   exact (he f (ha.shrink hi)).trans (he g hg).symm
lemma linear {L:E→L[ℝ] G} : Act n (L ∘ f) (L ∘ a):= ⟨L.contDiff.contDiffAt.comp _ ha.nice, fun i hi=> by
    rw [someJ, iteratedDeriv_eq_iteratedFDeriv,L.iteratedFDeriv_comp_left ha.nice (by simp)]; change _ • L _= _; rw [←map_smul]; exact congr_arg L (show _ = _ from Eq.trans (by rw [someJ,iteratedDeriv_eq_iteratedFDeriv]; rfl) (ha.writes i hi)) -- rewrite
    ⟩
include hb
lemma zipper : Act n (fun t=>(f t,g t)) (pair a b):= ⟨ha.nice.prodMk hb.nice,fun i hi=> by
   rw [someJ,iteratedDeriv_eq_iteratedFDeriv,iteratedFDeriv_prodMk ha.nice hb.nice (by simp)]; unfold pair; rw [← ha.writes i hi,← hb.writes i hi] -- pair left
   simp only [someJ,iteratedDeriv_eq_iteratedFDeriv]; rfl⟩
omit hb ha
lemma static (a:E):Act n (fun _=>a) (just a):= ⟨contDiffAt_const,fun i _=> by simp only [just,someJ];split_ifs with h; subst h; simp; simp [iteratedDeriv_const,h]⟩
include ha
lemma reflects : Act n (fun t=>f (-t)) (turn a):= by
   refine ⟨_root_.ContDiffAt.comp (f:=fun x:ℝ=>-x) _ (show ContDiffAt ℝ ω f (-(0:ℝ)) from (by simpa only [neg_zero] using ha.nice)) contDiffAt_id.neg,?_⟩; intro i hi
   rw [someJ,iteratedDeriv_comp_neg,neg_zero,smul_comm,turn,← ha.writes i hi]
   rfl
end Act
end
end YM.PositionX.Jet
