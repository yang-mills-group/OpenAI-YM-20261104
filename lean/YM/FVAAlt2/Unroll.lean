import YM.FVAAlt2.Bose

/-! Eval for finite-rank numerical identities within MS computation.
Decimal evaluation reserved for actual tangent vectors, no convergence of a cutoff
Taylor series follows/crucial. This hom is for the *BOSONIC* part only. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Bos
open Finset Function MS MS.Koszul MS.Book MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog MS.Swirl MS.Cylinder MS.Puff
variable {A J:Type}
local notation "p" => pNo A
local notation "E" => Bos A
local infix:70 " ⋄ " => product p
variable [Fintype A] (e:A→ℂ)
set_option linter.unusedSectionVars false

def length_bound (x:E) : ℕ := x.small.choose
lemma length_known (x:E) : Limit x.val (length_bound x):=x.small.choose_spec
abbrev rowX (e:A→ℂ):Matrix Unit A ℂ:= fun _=> e
abbrev times1(n:ℕ):= List.replicate n ()
def partialAt (e:A→ℂ)(n:ℕ): E→ₗ[ℂ] ℂ:= (n.factorial:ℂ)⁻¹ • (LinearMap.proj (R:=ℂ) (φ:=fun _:List Unit=>ℂ) (times1 n)) ∘ₗ (pull (rowX e)) ∘ₗ (FlatEven p).subtype
lemma partial_val(n:ℕ)(x:E): partialAt e n x=(pull (rowX e) x.val (times1 n))/(n.factorial:ℂ):=by change (n.factorial:ℂ)⁻¹ * _ = _; simp only [LinearMap.comp_apply,LinearMap.proj_apply,Submodule.subtype_apply]; ring

def initial (n:ℕ): E→ₗ[ℂ] ℂ:=∑ i∈ Finset.range (n+1),partialAt e i
lemma term {x:E}{n:ℕ}(h:Limit x.val n) (m:ℕ)(he:n<m): partialAt e m x=0:= by
  have hi : Limit (pull (rowX e) x.val) n:= pull_limit _ h; rw [partial_val,hi _ (by simp [times1]; omega),zero_div]
lemma initial_eq {x:E}{n m:ℕ}(hx:Limit x.val n)(h:n≤m): initial e n x=initial e m x:= by unfold initial; simp_rw [LinearMap.sum_apply]; apply Finset.sum_subset (Finset.range_mono (a:=n+1) (b:=m+1) (by omega)); intro i hi hv; exact term e hx i (by simp at hi hv; omega)
lemma settles (x:E){n:ℕ}(hx:Limit x.val n): initial e (length_bound x) x=initial e n x:= by rcases le_total (length_bound x) n with h|h; exact initial_eq e (length_known x) h; exact (initial_eq e hx h).symm

def evalL : E→ₗ[ℂ] ℂ:={
  toFun x:= initial e (length_bound x) x
  map_add' x y:=by
    let n:= max (length_bound x) (length_bound y)
    have he: Limit x.val n:= (length_known x).up (by unfold n; omega)
    have hm: Limit y.val n:= (length_known y).up (by unfold n; omega)
    rw [settles e x he,settles e y hm,settles e (x+y) (show Limit (x+y).val n from he.add hm),map_add]
  map_smul' c x:=by rw [settles e (c • x) (show Limit _ (length_bound x) from Limit.smul c (length_known x)),map_smul];rfl }
lemma eval_eq(x:E){n:ℕ}(hv:Limit x.val n): evalL e x=∑ i∈ Finset.range (n+1),partialAt e i x:= (settles e x hv).trans (LinearMap.sum_apply ..)
lemma eval_rank(x:E){n:ℕ}(hv:rank n x.val): evalL e x=partialAt e n x:= by
  have hx : mask n (pull (rowX e) x.val) = pull (rowX e) x.val:= by rw [← pull_mask,(rank_hat _).1 hv]
  rw [eval_eq e x (show Limit x.val n from by rw [← (rank_hat _).mp hv]; exact Limit.mod _ n),Finset.sum_eq_single_of_mem n (by simp)]; intro i _ hi; rw [partial_val,← hx,strange _ (by simp [times1,hi]),zero_div]
lemma eval_constant(c:ℂ): evalL e (Com.piece c)=c:= by rw [eval_eq e _ (coinN c),Finset.sum_range_one,partial_val,Com.piece_val,pull_coin]; simp [times1,coin]

lemma pull_letter(X : A): pull (rowX e) (letter X).val=e X • atLetter ():= by
  rw [letter_val]; apply ext_D (u:=pull (rowX e) (atLetter X)); · simp [atLetter]
  intro i; cases i; rw [pull_D,sum_eq_single X]; change e X • _ = _; rw [hear,pull_coin,map_smul,hear]; intro i _ hi; rw [unheard X hi,map_zero,smul_zero]; simp

private lemma pair_letter1 (F : Raw Unit ℂ) (n:ℕ):
    product (pNo Unit) (atLetter ()) F (times1 (n+1))=(n+1:ℂ)* F (times1 n):= by
  induction n generalizing F with
  | zero=> rw [show times1 (0+1)= [()] from List.replicate_succ,D_eval () (product _ _ _),D_product,hear,Koszul.sign_id]; simp [times1,atLetter,coin] -- inspect
  | succ n ih=>
    have h : times1 (n+1)= () :: times1 n:= List.replicate_succ
    rw [show times1 (n+1+1)=():: times1 (n+1) from List.replicate_succ, D_eval () (product _ _ _),D_product,hear,Koszul.sign_id,coin_product,one_smul,Pi.add_apply, ih,h,at_D]; push_cast; ring

lemma partial_letter (x:E)(i:A)(n:ℕ): partialAt e (n+1) (letter i*x) = e i*partialAt e n x:= by
  rw [partial_val,partial_val, Com.mul_val, pull_product (q:=pNo Unit) (show Tie p (pNo Unit) _ from fun _ _ _=>rfl), pull_letter, map_smul,LinearMap.smul_apply, Pi.smul_apply, pair_letter1,Nat.factorial_succ]; push_cast; field_simp [(by exact_mod_cast (Nat.factorial_ne_zero n) : (n.factorial:ℂ)≠ 0),(by exact_mod_cast (show n+1≠0 from (by omega)) : (n+1:ℂ)≠0)]; ring
lemma eval_letter (x:E)(i:A): evalL e (letter i*x)=e i*evalL e x:= by
  obtain ⟨n,hn⟩:= x.small
  rw [eval_eq e x hn, eval_eq e (letter i*x) (n:=n+1) (by push_cast; rw [add_comm]; exact (letterN i).pair hn), Finset.sum_range_succ']; simp_rw [partial_letter,← Finset.mul_sum]; apply add_eq_left.mpr; rw [partial_val]; unfold times1; simp only [List.replicate_zero,pull_nil,Com.mul_val,nil_product,letter_val,atLetter,zero_mul,zero_div]

def evalAt : E →ₐ[ℂ] ℂ := {
  evalL e with
  toFun:=evalL e
  map_zero':= map_zero _
  map_one':= eval_constant _ 1
  map_mul' f g:= by
    refine induction (fun f=> evalL e (f*g)= evalL e f*evalL e g) ?_ ?_ ?_ ?_ f
    · rw [one_mul,show (evalL e (1:E))=1 from eval_constant e 1,one_mul]
    · intro x y hx hy; rw [add_mul,map_add,map_add,hx,hy,add_mul]
    · intro r x hx; rw [smul_mul_assoc,map_smul,map_smul,hx,smul_mul_assoc]
    intro i x hx; rw [mul_assoc, eval_letter,eval_letter,hx,mul_assoc]
  commutes' c:= by rw [Com.alg_piece]; exact eval_constant .. }
end YM.FVAAlt2.Bos
