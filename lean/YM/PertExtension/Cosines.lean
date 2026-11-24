import YM.PertExtension.SymbolMatch
import Mathlib.Analysis.Fourier.ZMod

/-! Exact projected modes for finite inversion loops. Normalization: full side inverse volume. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace YM.PertExtension.LatticePT.Band
open MeasureTheory Measure Filter Maxwell Next Next.Rank Next.Rank.Radian Topology Analysis Asymptotics Set Real Metric Lattice Beamer Atlas Normal Perch Wall CellsInt Prayer RG
open Function Finset ZMod
open scoped ContDiff Topology BigOperators Classical NNReal RealInnerProductSpace
local notation "ℑ" => Complex.I

variable {n : Side}
def tone (x k:Site n) : ℂ := stdAddChar (∑ i,x i*k i)
lemma tone_swap (x k:Site n): tone x k=tone k x:= by unfold tone; simp_rw [mul_comm]
theorem tone_add (x y k:Site n) : tone (x+y) k=tone x k*tone y k:= by simp [tone, add_mul,Finset.sum_add_distrib,AddChar.map_add_eq_mul]
theorem tone_add' (x k l:Site n) : tone x (k+l)=tone x k*tone x l:=by rw [tone_swap,tone_add,(tone_swap k x),(tone_swap l x)] -- tone_swap default may rw wrong
lemma tone_zero (k : Site n): tone 0 k=1:=by simp only [tone,Pi.zero_apply,zero_mul,Finset.sum_const_zero,AddChar.map_zero_eq_one]
lemma tone_wrap (x k:Cover):tone (n:=n) (wrap n x) (wrap n k)=Complex.exp ((∑ i,x i*k i:ℤ)*(2*π*ℑ) / n.val) := by
    unfold tone ; change stdAddChar (∑ i:Axis,(x i:ZMod n.val)*(k i:ZMod n.val))=_; simp_rw [← Int.cast_mul];rw [← (Int.cast_sum .. : ((∑ i:Axis,x i*k i:ℤ):ZMod n.val) = _)] -- adjust before map products
    rw [stdAddChar_coe];congr 1;ring
lemma tone_unit (i:Axis) (x:Site n): tone x (step i)= stdAddChar (x i):= by
    rw [tone];congr 1;rw [sum_eq_single_of_mem i (mem_univ i)]
    all_goals simp [step_apply] <;> tauto
lemma tone_test (x : Site n)(h:x≠0):∃ i,tone x (step i)≠1 :=by
    by_contra! ht
    apply h; ext i;change x i=(0:ZMod n.val)
    apply ZMod.injective_stdAddChar;simp_rw [← tone_unit];rw [ht,AddChar.map_zero_eq_one]

private lemma shift_cancels (f : Site n→ℂ) (x : Site n) (z : ℂ)(h : z≠1)(hf:∀ y:Site n,f (y+x)=f y*z) : (∑ y:Site n, f y)=0:=by
   have he := Equiv.sum_comp (Equiv.addRight x) f
   change (∑ q :Site n, f (q+x))=(∑ q:Site n,f q) at he
   simp_rw [hf, ← Finset.sum_mul] at he
   by_contra hs; apply h
   exact mul_left_cancel₀ hs (he.trans (mul_one _).symm)

lemma mode_sum (x : Site n): (∑ k: Site n,tone x k) = if x=0 then (Fintype.card (Site n):ℂ) else 0 :=by
   by_cases h:x=0
   · rw [if_pos h,h];simp_rw [tone_zero];simp
   obtain ⟨i,hi⟩:=tone_test x h
   change _=_
   exact (shift_cancels (tone x) (step i) (tone x (step i)) hi (fun y=>tone_add' x y (step i))).trans (if_neg h).symm


end YM.PertExtension.LatticePT.Band
namespace YM.PertExtension.LatticePT.Band
open MeasureTheory Measure Filter Maxwell Next Next.Rank Next.Rank.Radian Topology Analysis Asymptotics Set Real Metric Lattice Beamer Atlas Normal Perch Wall CellsInt Prayer RG
open Function Finset ZMod
open scoped ContDiff Topology BigOperators Classical NNReal RealInnerProductSpace
variable {n:Side}
abbrev frequency (k : Site n) : E4:=addr n (lift k)
lemma phase_matches (x t:Cover) (n:Side) : tone (wrap n x) (wrap n t)=wave (mapZ x) (addr n t):= by
   rw [tone_wrap,terrel,chimes]
   congr 1
   rw [PiLp.inner_apply] -- adjust
   change ↑(∑ i,x i*t i:ℤ)*(2*(Real.pi:ℂ)*Complex.I)/n.val=2*(π:ℂ)*Complex.I * (((∑ i:Axis,(x i:ℝ)*((n.val:ℝ)⁻¹*(t i:ℝ))):ℝ):ℂ)
   push_cast;rw [Finset.sum_mul,Finset.mul_sum, Finset.sum_div];apply Finset.sum_congr rfl;intro i _;ring
-- no pole away from k=0
lemma tone_step_wrap i (t:Cover) (n:Side) : increment i (addr n t)=tone (step i) (wrap n t)-1:= by
  rw [← wrap_step n i,phase_matches, show mapZ (step i)=basis i by simpa only [zero_add,show mapZ (0:Cover)=(0:E4) by ext i; change (((0:ℤ)):ℝ)=0; exact Int.cast_zero] using mapZ_step 0 i];rfl
lemma tone_step (i:Axis) (k:Site n) : tone (step i) k-1= increment i (frequency k):= by nth_rw 1 [← wrap_lift k]; exact (tone_step_wrap ..).symm
lemma mode_mass {k:Site n} (h:k≠0) : 0<location (frequency k) := by
  obtain ⟨i,hi⟩:=tone_test k h
  apply (pow_pos (a:=‖increment i (frequency k)‖) (norm_pos_iff.mpr <| fun hk=> hi (by rw [tone_swap,←sub_eq_zero,tone_step,hk])) 2).trans_le
  exact Finset.single_le_sum (f:=fun i=>‖increment i (frequency k)‖^2) (fun i _=>sq_nonneg _) (Finset.mem_univ i)

def nV (n:Side):ℂ := n.val^4
def fourier (f: Site n→ℂ) (k) := ∑ x, tone x k*f x
lemma reconstruction (n:Side) (f:Site n→ℂ)(y) : (nV n)⁻¹ * (∑ k,tone (-y) k * fourier f k)=f y:=by
   simp_rw [fourier,Finset.mul_sum,←mul_assoc]
   rw [Finset.sum_comm];let Q (x k:Site n):=tone (x-y) k
   have he (x k) : (nV n)⁻¹ * tone (-y) k * tone x k * f x = Q x k*((nV n)⁻¹*f x):= by dsimp [Q]; rw [(show x-y= -y+x by abel),tone_add]; ring
   simp_rw [he,← Finset.sum_mul,show ∀ x, ∑ k:Site n,Q x k=_ from fun x=> mode_sum (x-y)]
   rw [sum_eq_single y]
   · rw [if_pos (sub_self _),site_card, Nat.cast_pow] -- adjust
     have ht:(n.val:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (by exact_mod_cast n.pos.ne')
     unfold nV; field_simp
   · intro i _ hi;rw [if_neg (show i-y≠0 from sub_ne_zero.mpr hi), zero_mul]
   exact fun h=>False.elim (h (mem_univ y))
end YM.PertExtension.LatticePT.Band
