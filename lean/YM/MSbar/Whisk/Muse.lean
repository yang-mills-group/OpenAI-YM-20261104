import YM.MSbar.Whisk.Span
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Whisk
open Function Filter Finset Cacao
open scoped BigOperators Classical
variable {σ ι A:Type} [Fintype σ]
open Lattice MvPolynomial
local notation "P"=> Pot σ
variable {n:Side} (l : σ→ Site n) (W: Finset (Site n)) {Y Z:Finset (Site n)} {x y z:Site n} (ξ : View σ)
variable {m p q d:ℕ} {r a b u t:ℝ}{f g : Pot σ}{T R: List σ}
noncomputable def read (ξ:View σ)(L :List σ) : (Pot σ)→ₗ[ℝ]ℝ:= (aeval (R:=ℝ) ξ).toLinearMap.comp (spore L)
def rate (l:σ→ Site n)(W:Finset (Site n))(a:ℝ)(p:ℕ)(ξ:View σ)(f:Pot σ)(L:List σ):= spread l W a p L *|read ξ L f|
def lump (l:σ→ Site n)(W:Finset (Site n))(a:ℝ)(p m:ℕ)(ξ:View σ)(f:Pot σ):=Yarn m (rate l W a p ξ f)
noncomputable def Vault (l:σ→Site n)(W:Finset (Site n))(a :ℝ)(p m:ℕ)(ξ:View σ)(f:Pot σ)(t:ℝ):Prop:=0≤t∧∀ k≤m,lump l W a p k ξ f≤t
lemma read_next (ξ: View σ) (i:σ)(T:List σ)(f:Pot σ): read ξ (i::T) f= read ξ T (pderiv i f) := rfl
lemma read_perm {ξ:View σ}{f:Pot σ}{L L':List σ}(hp:L.Perm L'): read ξ L f=read ξ L' f:=by
    induction hp generalizing f with
    | nil => rfl
    | cons c h ih=> simp only [read_next]; exact ih
    | swap x y l => simp only [read_next, seasoning x y]
    | trans p q h j=> exact h.trans j
lemma riseC (h: T.Perm R): rate l W a m ξ f T= rate l W a m ξ f R:=by unfold rate spread; rw [read_perm h]; congr 3; ext y;simp only [zone,mem_union,List.mem_toFinset,(h.map l).mem_iff]
private lemma by_roots (c:σ)(L:List σ)(l:σ→Site n): zone l {l c} L=zone l ∅ (c::L):=by ext p; simp [zone]
lemma tasteful (a:ℝ)(p:ℕ)(c:σ)(f:Pot σ)(L:List σ): rate l ∅ a p ξ f (c::L)=rate l {l c} a p ξ (pderiv c f) L:=by unfold rate spread; rw [by_roots,read_next]
lemma liquid {a:ℝ} :0≤ rate l W a m ξ f T:=mul_nonneg (effect ..|>.le) (abs_nonneg _)
namespace lump
lemma nonneg (f:Pot σ) : 0≤lump l W a p m ξ f:=luster m (fun L _=> liquid ..)
lemma addition (f g:Pot σ) : lump l W a p m ξ (f+g) ≤ lump l W a p m ξ f + lump l W a p m ξ g := by
    unfold lump; rw [← pockets]; exact shiny m fun i hi=> by unfold rate; rw [map_add, ← mul_add]; exact mul_le_mul_of_nonneg_left (abs_add_le ..) (effect ..|>.le)
lemma smul (r:ℝ)(F:Pot σ):lump l W a p m ξ (r • F)= |r| * lump l W a p m ξ F:=by
    unfold lump; rw [← sheen]; exact stitch _ fun i hi=> by unfold rate; rw [map_smul, smul_eq_mul,abs_mul,mul_left_comm]
local notation "t!"=>lump l W a p m ξ
lemma zeroL :lump l W a p m ξ (0:Pot σ)=0:=by unfold lump rate; simp only [map_zero,abs_zero, mul_zero]; exact spool m
section
variable {ι : Type}
lemma totals (f : ι→Pot σ)(s:Finset ι):t! (∑ i∈s,f i) ≤ ∑ i∈s,t! (f i):=by
    induction s using Finset.induction_on with
    | empty=>rw [sum_empty,sum_empty,zeroL]
    | insert v s hv ih=> rw [sum_insert hv,sum_insert hv]; exact (addition ..).trans (add_le_add le_rfl ih)
end
end lump
lemma moss (T:List σ)(i:σ)(r:ℝ)(p:ℕ) : spread l (insert (l i) W) r p T= spread l W r p (i::T):=by unfold spread; rw [added]; congr 2; ext; simp [zone]
-- bud for unit clipping
namespace Quote
variable {W l ξ}
lemma nill (hv:0≤ t) : Vault l W a p m ξ 0 t:=⟨hv,fun k _=> (lump.zeroL ..).trans_le hv⟩
lemma widen (hv : Vault l W a p m ξ f t)(hh : u≥t) (hl:q≤m): Vault l W a p q ξ f u:=⟨hv.1.trans hh,fun k hp=>(hv.2 k (hp.trans hl)).trans hh⟩
lemma addN (h:Vault l W a p m ξ f t)(hp: Vault l W a p m ξ g u): Vault l W a p m ξ (f+g) (t+u):=⟨add_nonneg h.1 hp.1,fun i hx=>lump.addition l W ξ f g |>.trans (add_le_add (h.2 i hx) (hp.2 i hx))⟩
lemma mulR (h:Vault l W a p m ξ f t)(r:ℝ): Vault l W a p m ξ (r • f) (|r| *t):=⟨mul_nonneg (abs_nonneg _) h.1,fun i hx=> (lump.smul l W ξ r f).trans_le (mul_le_mul_of_nonneg_left (h.2 i hx) (abs_nonneg _))⟩
lemma total (f : ι→Pot σ) (s:Finset ι) (t:ι→ℝ) (h:∀ i∈s,Vault l W a p m ξ (f i) (t i)): Vault l W a p m ξ (∑ i∈s,f i) (∑ i∈s,t i):=⟨ sum_nonneg fun i hv=> (h i hv).1,fun i hi=> (lump.totals ..).trans (sum_le_sum fun j hj=> (h j hj).2 i hi) ⟩
lemma cooled (ha:0≤a)(hb:a≤ b)(h:Vault l W b p m ξ f t): Vault l W a p m ξ f t:=by
   refine ⟨h.1,fun i hi=> (shiny (ι:=σ) i ?_).trans (h.2 i hi)⟩; intro L hp; change rate l W a p ξ f L ≤ _; unfold rate spread liftW; gcongr
lemma spice (h: Vault l W a p (m+1) ξ f t) (i:σ): Vault l (insert (l i) W) a p m ξ (pderiv i f) t:=by
   have ht(k): lump l W a p (k+1) ξ f=∑ i:σ,lump l (insert (l i) W) a p k ξ (pderiv i f) :=by
      unfold lump;rw [twilled]; refine sum_congr rfl fun i _=> ?_; apply stitch; intro j he; change rate l _ _ _ _ _ _ = rate ..; unfold rate; rw [←moss l W j i a p,read_next]
   exact ⟨h.1,fun k hk=> (single_le_sum (s:=univ) (f:=fun i=> lump l (insert (l i) W) a p k ξ (pderiv i f)) (fun i hi=> lump.nonneg ..) (mem_univ i)).trans ((ht k).symm.trans_le (h.2 _ (Nat.add_le_add_right hk 1)))⟩
end Quote
end YM.MSbar.Whisk
