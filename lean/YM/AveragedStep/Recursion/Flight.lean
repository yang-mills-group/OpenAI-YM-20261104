import YM.AveragedStep.Recursion.Spray
/-!
# On rows of colors over Rim, all-orders score coefficients join the marked list
by prepending slots (keep coincidences); Step impulse zero tested after pin.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep.SD
open Filter Function Lattice RG Loops Tree Wilson Precision Metric Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
open Finsupp
variable {c f:Side}{G:Gauge}{S:StepData c f}(h:S.patch.Branches S.kernel G)

abbrev Lips (G:Gauge)(c f:Side):=List (Ink G c f)
def del (j: Ink G c f): Lips G c f → Spray (Lips G c f)
  | []=>0
  | i::w=> (if j=i then single w (1:ℝ) else 0)+ leftS (fun x=>i::x) (del j w)
/-- `leading` partner; positive is cross itself, sign set in united recursion. -/
def cross{A:ChartRatio G}(F:Forest S.ratio)(k:Key F G)(w:Lips G c f):Spray (Lips G c f):=∑ i, single (hatch i :: w) (bracken S A F k i)
def tether {n:ℕ} (b:(Fin n → Ink G c f)→ℝ)(w:Lips G c f):Spray (Lips G c f):=∑ i, single (List.ofFn i ++ w) (b i)
/-- Skeleton - elm is positive measure score, subtract it. -/
def leap {A:ChartRatio G}(S:StepData c f)(j:Ink G c f)(n:ℕ)(w:Lips G c f):Spray (Lips G c f):= tether (n:=n+1) (canopy S j) w - tether (n:=n-1) (elm A j) w

def sample (Y:Hand G c f): Lips G c f→ℝ:=fun w=>mon w Y
lemma sample_add (Y:Hand G c f)(w v:Lips G c f):sample Y (w++v) = sample Y w*sample Y v := by simp [sample,mon]
lemma sample_del (Y:Hand G c f)(j:Ink G c f)(w:Lips G c f):offer (sample Y) (del j w) = peel j w Y:=by
 induction w with
 | nil=> simp [del,peel]
 | cons i w ih=>
   rw [del,peel,map_add,offer_left]; congr 1
   · by_cases he:j=i; · subst i; rw [if_pos rfl,if_pos rfl,offer_single,one_smul];rfl
     rw [if_neg he,if_neg (Ne.symm he),map_zero]
   rw [show sample Y ∘ (fun x=>i::x) = dashMark (Y i.1) i.2 • sample Y from rfl,offer_smul,ih,smul_eq_mul]
lemma sample_tether {n:ℕ}(b:(Fin n→Ink G c f)→ℝ)(Y:Hand G c f)(w):offer (sample Y) (tether b w)=
  (∑ i,b i * sample Y (List.ofFn i))*sample Y w:=by
 rw [tether, map_sum, Finset.sum_mul]; exact Finset.sum_congr rfl (fun i _=>by simp [offer_single,smul_eq_mul,sample_add,mul_assoc])
lemma sample_leap {A:ChartRatio G}(S:StepData c f)(j:Ink G c f){n:ℕ}(hn:n≠0)(Y:Hand G c f)(w): offer (sample Y) (leap (A:=A) S j n w)=mon w Y * tier S A j.1 (fingers G j.2) n Y:=by
 rw [leap,map_sub,sample_tether,sample_tether,duplicate hn]; change _*mon _ _ - _*mon _ _ = _; rw [mul_sub]; unfold sample; ring

/-- Linear SD equations on moments. H retained, not thrown from a booked tail. -/
def weigh (F:Forest S.ratio)(A:ChartRatio G)(j:Key F G)(w:Lips G c f): Spray (Lips G c f):= ∑ i,single (fkey F i::w) (body A F j i)
include h in
lemma lead {A:ChartRatio G}(F:Forest S.ratio)(j:Key F G)(Y:Hand G c f)(he:pin F Y)(w):
    offer (sample Y) (weigh F A j w+cross (A:=A) F j w)=mon w Y * tier S A (Sum.inl j.1.val) (fingers G j.2) 0 Y:=by
 rw [linear_out h A F j Y he,mul_add,map_add,weigh,cross,map_sum,map_sum,Finset.mul_sum,Finset.mul_sum]
 congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> rw [offer_single] <;> simp only [sample,mon_cons,mon_nil,smul_eq_mul] <;> ring

def friends (F:Forest S.ratio)(A:ChartRatio G)(k:Key F G)(w:Lips G c f):Spray (Lips G c f):=del (fkey F k) w-cross (A:=A) F k w
/-- positive Icc tape (don't silently treat `k` as k+1 in shift later) -/
def active (n:ℕ) := Finset.Icc 1 n
lemma on_tape (n k:ℕ):k∈active n↔1≤k∧k≤n:=Finset.mem_Icc

def bunched (F:Forest S.ratio)(A:ChartRatio G)(k:Key F G)(w:Lips G c f)(d:ℕ)(t:ℝ):Spray (Lips G c f):=
    friends F A k w - ∑ n∈active d,t^n • leap (A:=A) S (fkey F k) n w
lemma tape_def (n:ℕ): insert 0 (active n) = Finset.range (n+1):=by ext i;simp [active];omega
lemma tape_zero (n:ℕ): 0 ∉ active n:=by simp [active]
include h in
lemma unite (F:Forest S.ratio)(A:ChartRatio G)(i:Key F G)(Y:Hand G c f)(he:pin F Y)(w)(t:ℝ)(d:ℕ):
  offer (sample Y) (bunched F A i w d t-weigh F A i w)=vice (S:=S) (A:=A) t (fkey F i) w d Y:=by
 rw [bunched,friends,map_sub,map_sub,map_sub,map_sum, sample_del,vice,chorus,← tape_def,Finset.sum_insert (tape_zero d)]
 simp only [pow_zero,one_mul,fkey,fieldKey,mul_add,Finset.mul_sum]
 rw [← lead h F i Y he,map_add]
 let D:=active d
 let L(n:ℕ):=t^n • leap (A:=A) S (fkey F i) n w
 have hc:(∑ n∈D,offer (sample Y) (L n))=∑ n∈D,mon w Y*(t^n*tier S A (Sum.inl i.1.val) (fingers G i.2) n Y):=by
   refine Finset.sum_congr rfl fun n hn=>?_ ; dsimp only [L]; rw [map_smul,sample_leap _ _ (fun e=>tape_zero d (e ▸ hn)),smul_eq_mul]; unfold fkey fieldKey; dsimp only; ring
 dsimp only [fkey,fieldKey,L,D] at hc; rw [hc]; ring
end YM.AveragedStep.SD
