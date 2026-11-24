import Mathlib.LinearAlgebra.Lagrange
import YM.LocalLTE.Taylor
/-!
## LOCAL step PT grading library — deterministic sampler

A finite bandwidth for Laurent continuation (on (0,1], auxiliary coupling, NOT varying along
physical histories). Interpolation only on local predictors given independently. Extractork powers
are `j-k`, with denominator `s^k`. Not series-identity claims on the physical answer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Weft
open Filter Set Metric Function MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff
variable {ι F E : Type*} [AddCommGroup E][Module ℝ E] [AddCommGroup F][Module ℝ F]
variable {k n m : ℕ} {f g : ℝ→E}
abbrev J (k:ℕ):= Fin (2*k+1)
def clip : Set ℝ := Set.Ioc (0:ℝ) 1
/-- `s^index / s^k`. Use `index` comparison before Z pow APIs. -/
def mark (k:ℕ)(j:J k)(s:ℝ):= s^(j.val:ℕ)/s^k
def Hex (k:ℕ)(f:ℝ→E):Prop:= ∃ c:J k→E,∀ s∈ clip,f s=∑ i,mark k i s • c i
section
variable (k)
def probe (i:J k):ℝ:= (i.val+1:ℝ)⁻¹
lemma probes (i:J k):probe k i∈clip:= ⟨inv_pos.mpr (by positivity), (inv_le_one₀ (by positivity : 0<(i.val+1:ℝ))).mpr (by simp)⟩
lemma separate : Injective (probe k) := fun i j hv=> Fin.ext (by unfold probe at hv; rw [inv_inj,add_left_inj] at hv; exact_mod_cast hv)
-- weights for decoding shifts for every output power.
def slate (i j : J k):ℝ:= (Lagrange.basis univ (probe k) i).coeff j.val * probe k i ^k
lemma tally (i j:J k) : ∑ l:J k,slate k l j * mark k i (probe k l)= if i=j then 1 else 0:=by
   let f:= (Polynomial.X (R:=ℝ))^i.val
   let P:= Finset.univ (α:=J k); let g:= probe k
   have h: Set.InjOn g P:= (separate _).injOn
   have hp:= Lagrange.eq_interpolate h (f:=f) (by unfold f P; rw [Polynomial.degree_X_pow, card_univ,Fintype.card_fin]; exact_mod_cast i.isLt)
   have hq : ∑ l:J k,slate k l j* mark k i (g l)= (Lagrange.interpolate P g (fun i=> f.eval (g i))).coeff j.val:=by
      rw [Lagrange.interpolate_apply,Polynomial.finsetSum_coeff]
      apply sum_congr rfl; intro l hl; have hx:0<probe k l:=(probes k l).1; unfold f slate mark P g; rw [Polynomial.eval_pow,Polynomial.eval_X,Polynomial.coeff_C_mul]; field_simp
   rw [hq,←hp,show f= _ from (rfl:f=(Polynomial.X (R:=ℝ))^i.val),Polynomial.coeff_X_pow]; split <;> split
   all_goals try rfl
   · next h1 h2=> exact False.elim (h2 (Fin.ext h1.symm))
   next h1 h2=> exact False.elim (h1 (congr_arg Fin.val h2.symm))
def pick (f:ℝ→E)(j:J k) : E := ∑ i:J k,slate k i j • f (probe k i)
end
lemma picked {c:J k→E} (h:∀ s∈clip, f s=∑ i, mark k i s • c i) (j:J k): pick k f j=c j:=by
    unfold pick; simp_rw [h _ (probes k _), Finset.smul_sum, smul_smul]; rw [sum_comm]; simp_rw [← Finset.sum_smul,tally]; exact (sum_eq_single j (fun i _ he=>by rw [if_neg he,zero_smul]) (by simp)).trans (by simp)
namespace Hex
lemma seen (h:Hex k f){s:ℝ}(hs:s∈ clip) :f s=∑ i, mark k i s • pick k f i:=by
   obtain ⟨c,H⟩:=h; simp_rw [picked H]; exact H _ hs
lemma change (h:Hex k f)(he: Set.EqOn f g clip): Hex k g:= ⟨pick k f,fun _s hs=> (he hs).symm.trans (h.seen hs)⟩
lemma blank : Hex k fun (_:ℝ)=>(0:E):=⟨0,by simp⟩
lemma add {f g:ℝ→E} (h:Hex k f)(H:Hex k g): Hex k (fun s=> f s+g s):=by
   refine ⟨fun i=> pick k f i + pick k g i, fun s hs=> ?_⟩; simp_rw [smul_add, Finset.sum_add_distrib]; exact congr_arg₂ _ (h.seen hs) (H.seen hs)
lemma held (j:J k)(x:E) : Hex k (fun s=> mark k j s • x):= by
   refine ⟨fun i=> if i=j then x else 0,fun s hs=> ?_⟩; rw [sum_eq_single j] <;> simp_all
lemma constant (x:E) : Hex k (fun _=> x):=by
   let i:J k:= ⟨k,by omega⟩; exact (held i x).change fun s (hs:s∈clip)=>by
      change (s^k/s^k) • x=x; rw [div_self (pow_ne_zero _ hs.1.ne'),one_smul]
lemma total (A:Finset ι) {v:ℝ→ι→E}(h:∀ i∈A, Hex k (fun s=> v s i)): Hex k (fun s=>∑ i∈A,v s i):=by
   induction A using Finset.induction_on with
   | empty=> simp [blank]
   | insert i I hi ih=>
      simp_rw [Finset.sum_insert hi]; exact (h _ (mem_insert_self ..)).add (ih (fun j hj=> h j (mem_insert_of_mem hj)))
lemma grow (h:Hex k f)(he:k≤n): Hex n f:=by
   let g s:=∑ i,mark k i s • pick k f i
   apply Hex.change (f:=g) ?_ (fun _ hs=> (h.seen hs).symm); unfold g; apply Hex.total
   intro i _; let j:= i.val+(n-k); have hj: j<2*n+1:= by unfold j; omega
   refine (Hex.held ⟨j,hj⟩ (pick k f i)).change fun (s:ℝ) (hs:s∈clip)=> congr_arg (fun x:ℝ=> x • pick k f i) (?_)
   unfold mark; change s^j/s^n= s^i.val/s^k; rw [div_eq_div_iff (pow_ne_zero n hs.1.ne') (pow_ne_zero k hs.1.ne'),← pow_add,← pow_add]; congr 1; omega
lemma oneZ (h:Hex k f)(r:ℝ): Hex k (fun s=> r • f s):=by
    refine ⟨fun i=> r • pick k f i,fun i hi=>?_⟩
    dsimp only; rw [h.seen hi, Finset.smul_sum]; apply sum_congr rfl fun _ _=> smul_comm ..
lemma wallet {s :ℝ→ℝ} (H:Hex m s) (h:Hex k f) : Hex (m+k) (fun t=> s t • f t):=by
    let u t:= ∑ i, ∑ j, (mark m i t * mark k j t) • (pick m s i • pick k f j)
    refine Hex.change (f:=u) ?_ (?_); swap
    · intro t ht; unfold u; dsimp only; rw [H.seen ht,h.seen ht,Finset.sum_smul]; apply sum_congr rfl fun i _=>?_ ; rw [Finset.smul_sum]; apply sum_congr rfl fun j _=>?_ ; simp_rw [smul_smul,smul_eq_mul]; congr 1; ring
    unfold u; apply Hex.total; intro i _; apply Hex.total; intro j _; let r:=i.val+j.val
    refine (Hex.held (k:=m+k) ⟨r,by unfold r; omega⟩ (pick m s i • pick k f j)).change fun (t:ℝ) (ht:t∈clip) => congr_arg (fun x:ℝ=> x • (pick m s i • pick k f j)) (show mark (m+k) _ t= _ from (?_)); change t^r/t^(m+k)=t^i.val/t^m*(t^j.val/t^k); rw [show r=i.val+j.val from rfl,pow_add,pow_add,div_mul_div_comm]
lemma mul {v w:ℝ→ℝ}(h:Hex k v)(H:Hex n w): Hex (k+n) (fun s=> v s*w s):= wallet h H
lemma powers {v:ℝ→ℝ}(h:Hex k v)(p:ℕ) : Hex (k*p) (fun s=> v s^p):=by
    induction p with
    | zero=> simp only [pow_zero]; exact constant _
    | succ p hp=> rw [Nat.mul_succ]; simp_rw [pow_succ]; exact hp.mul h
lemma product (A:Finset ι) {v:ℝ→ι→ℝ}(h:∀ i∈A, Hex k (fun s=> v s i)): Hex (k*A.card) (fun s=>∏ i∈A,v s i):=by
   induction A using Finset.induction_on with
   | empty=> exact constant _
   | insert i I hi ih=>
      rw [Finset.card_insert_of_notMem hi,Nat.mul_succ, Nat.add_comm (_*_)]; simp_rw [Finset.prod_insert hi]; exact (h _ (mem_insert_self ..)).mul (ih (fun j hj=> h j (mem_insert_of_mem hj)))
lemma alpha (L:E →ₗ[ℝ] F)(h:Hex k f): Hex k (fun s=> L (f s)):=by
   refine ⟨fun j=> L (pick k f j),fun s hs=>?_⟩; dsimp only; rw [h.seen hs,map_sum]; simp_rw [map_smul]
lemma invert {f:ℝ→ι→E}(h:∀ i,Hex k (fun s=> f s i)): Hex k f:=by
   refine ⟨fun j i=> pick k (fun s=>f s i) j,fun s hs=>?_⟩; funext i; rw [Finset.sum_apply]; exact (h i).seen hs
lemma use {f:ℝ→ι→E} (h:Hex k f)(i:ι) : Hex k (fun s=> f s i) :=h.alpha (LinearMap.proj i)
end Hex
end YM.LocalLTE.Weft
