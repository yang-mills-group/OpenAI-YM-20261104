import YM.Contacts.Milling.Reset
import YM.Contacts.Loom.Index
/-!
# Power recalibration bound. Families varying (Warp coefficients) with clocks. Apportions in Meter not packet angular.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Allium
open Function Filter Finset Lattice Wilson RG PowerSeries
open Milling Loom
open Resetter Meter -- alias Pow clash
open scoped Topology BigOperators Classical
variable {N:Meter} {k l i:ℕ} {U V:ℕ→Resetter.Pow}{v p:ℝ}
abbrev Stream := ℕ→ℝ
variable {f g h a b t:Stream}
namespace Flux
abbrev Live (U:ℕ→Resetter.Pow) (N:Meter) (k:ℕ):= ∀ i:ℕ,i<k → N.Rush 0 fun n=> Resetter.pin (U n) i
protected lemma top (hn:N.Rush v a): N.Rush v (-a):= by simpa using! hn.multiplier (-1)
lemma sub (hn:N.Rush v a)(ht:N.Rush v b): N.Rush v (a-b):= by simpa only [sub_eq_add_neg] using! hn.blend (Flux.top ht)
lemma sum {ι:Type*}(q:Finset ι)(f:ι→Stream)(h:∀ i∈q,N.Rush p (f i)): N.Rush p (∑ i∈q,f i):= by
   induction q using Finset.induction_on with | empty => simpa using (Rush.zero (M:=N) (d:=p)) | insert i q hi ih => rw [sum_insert hi]; exact (h i (mem_insert_self ..)).blend (ih fun j hj=> h _ (mem_insert_of_mem hj))
lemma BudgetBy {ι:Type*}(q:Finset ι)(f:ι→Stream)(h:∀ i∈q,N.Rush p (f i)): N.Rush p (fun x=>∑ i∈q,f i x):= (Flux.sum q f h).take (Eventually.of_forall fun x=>(Finset.sum_apply x q f).symm)
protected lemma Live.times (h:Live U N k)(g:Live V N k): Live (U*V) N k:= by
   intro i hi; have hv: ∀ n,Resetter.pin ((U*V) n) i= ∑ j∈ Finset.HasAntidiagonal.antidiagonal i, Resetter.pin (U n) j.1 * Resetter.pin (V n) j.2:= fun n=> coeff_mul _ _ _ -- order
   simp_rw [hv]; apply BudgetBy (Finset.HasAntidiagonal.antidiagonal i) (f:=fun j n=> Resetter.pin (U n) j.1 *Resetter.pin (V n) j.2); intro j hj; have hx:= Finset.HasAntidiagonal.mem_antidiagonal.mp hj; exact (h j.1 (by omega)).times (g j.2 (by omega)) (by norm_num)
-- build rota from sink price only
lemma live_turn (h:Live U N k): Live (fun i=> Resetter.rotate (U i)) N k:= by
   -- recurrence
   suffices he: ∀ l≤ k,Live (fun i=> Resetter.rotate (U i)) N l from he k le_rfl
   intro l; induction l with|zero=>exact fun _ _ hl=> (Nat.not_lt_zero _ hl).elim|succ l ih=>
   intro hu i hi; by_cases ht:i=l
   swap; · exact ih (by omega) i (by omega)
   subst i; by_cases h':l=0; · subst l; exact (Rush.settle (M:=N) 1).take (Eventually.of_forall (fun i=> Resetter.rotate_zero (U i)))
   let V i:=Resetter.rotate (U i); have hh: Live V N l:= ih (by omega)
   have ht(F V:ℕ→Resetter.Pow)(hf:Live F N l)(hv:Live V N l): N.Rush 0 (fun i=> gap (F i) (V i) l):= by
       unfold gap; apply Flux.BudgetBy ((Finset.HasAntidiagonal.antidiagonal l).filter (fun a:ℕ×ℕ=>0 < a.1 ∧ 0 < a.2)) (fun j i=> pin (F i) j.1 * pin (V i) j.2); intro j hj; obtain ⟨hq,hd,hp⟩:=mem_filter.mp hj; have h:= Finset.HasAntidiagonal.mem_antidiagonal.mp hq; exact (hf j.1 (by omega)).times (hv j.2 (by omega)) (by norm_num)
   have hx: N.Rush 0 (fun i=>relative (U i) l (pin (V i))):=( (ht _ _ hh hh).blend (ht U (V*V) (fun i hi=>h i (by omega)) (hh.times hh))).take (Eventually.of_forall fun i=> by unfold relative; dsimp only; rw [show PowerSeries.mk (pin (V i))= V i from PowerSeries.ext fun n=>coeff_mk .. ]; rfl)
   refine ((h l (by omega)).blend hx|>.multiplier (-(1/2:ℝ))).take (Eventually.of_forall fun i=>?_); dsimp only; rw [rotate_pin _ _ (by omega)]; unfold V; ring
-- roles
abbrev grade (k:ℕ) :ℝ:=-(1/2:ℝ)*k
def logit (t:Stream)(k:ℕ)(U:ℕ→Resetter.Pow) : Stream:= fun i=> ∑ j∈ Finset.range k, pin (U i) j*t i^j
structure Looks (N:Meter)(t:Stream)(k:ℕ)(U:ℕ→Resetter.Pow)(f:Stream):Prop where
    alive: Live U N k
    price: N.Rush (grade k) (f-logit t k U)
lemma grade_zero (k:ℕ): grade k ≤0:= by unfold grade; apply mul_nonpos_of_nonpos_of_nonneg (by norm_num) (Nat.cast_nonneg _)
lemma cheaper (h:i≤k):grade k≤grade i:= mul_le_mul_of_nonpos_left (Nat.cast_le.mpr h) (by norm_num:(-(1/2):ℝ)≤0)
variable (ht:N.Rush (-(1/2)) t)
include ht
lemma leap (h:Live U N k)(i)(hi:i<k): N.Rush (grade i) (fun n=>Resetter.pin (U n) i *t n^i):= (h _ hi).times (ht.powers i) (zero_add _)
lemma forecast (h:Live U N k) : N.Rush 0 (logit t k U):= Flux.BudgetBy (Finset.range k) (fun i n=> pin (U n) i *t n^i) fun i hi=> (leap ht h i (Finset.mem_range.mp hi)).mono (grade_zero _)
omit ht in
lemma motto (h:Live U N k): Looks N t k U (logit t k U):= ⟨h,(by rw [sub_self]; exact Rush.zero)⟩
lemma forecasted (h:Live U N k)(hw:l≤k): Looks N t l U (logit t k U):= by
   have hp: logit t k U-logit t l U=∑ i∈Finset.Ico l k,(fun n=> Resetter.pin (U n) i * t n ^ i):= by
     funext n; simp only [Finset.sum_apply]; symm; exact Finset.sum_Ico_eq_sub _ hw
   refine ⟨fun i hi=> h i (lt_of_lt_of_le hi hw), (by rw [hp]; exact Flux.sum _ _ (fun i hi=> (leap ht h _ (mem_Ico.mp hi).2).mono (cheaper (mem_Ico.mp hi).1)))⟩
lemma log_product (hu:Live U N k)(hv:Live V N k) : N.Rush (grade k) (logit t k U*logit t k V-logit t k (U*V)):= by
    let q:= Finset.range k; let R(i:ℕ)(n:ℕ):=pin (U n) i*t n^i; let Y(i n:ℕ):=pin (V n) i*t n^i
    let f (i:ℕ×ℕ):Stream:= fun n=> R i.1 n*Y i.2 n; let S:=q×ˢ q;
    have ha: logit t k U*logit t k V=∑ i∈S,f i:= by ext x; change (∑ i∈q,R i x)*(∑ i∈q,Y i x)= _; rw [Finset.sum_apply, Finset.sum_product]; simp only [f, Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_comm
    have hh: ∀ i,logit t k (U*V) i=∑ j∈ q,∑ a∈ Finset.HasAntidiagonal.antidiagonal j,f a i := by
        intro i; apply sum_congr rfl; intro j _; let W:= U*V; change Resetter.pin (U i*V i) j*_=_; rw [pin,coeff_mul, Finset.sum_mul]; refine sum_congr rfl fun i' hi=>?_ ; rw [← (Finset.HasAntidiagonal.mem_antidiagonal.mp hi),pow_add]; unfold f R Y pin; ring
    let T:= S.filter (fun i=> i.1+i.2≥k); let v:= S.filter (fun i=> ¬i.1+i.2≥k); have he: v=q.biUnion Finset.HasAntidiagonal.antidiagonal:= by
         ext i; simp only [v, mem_filter, S, mem_product,q,Finset.mem_biUnion, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal]; grind
    have hb (x:ℕ): (∑ i∈v,f i x)= logit t k (U*V) x:= by rw [he, Finset.sum_biUnion, hh]; intro i hi j hj h; apply Finset.disjoint_left.mpr; intro x hx hX; exact h ((Finset.HasAntidiagonal.mem_antidiagonal.mp hx).symm.trans (Finset.HasAntidiagonal.mem_antidiagonal.mp hX))
    rw [ha,show (∑ i∈S,f i)-logit t k (U*V)=∑ i∈T,f i from ?_]; apply Flux.sum _ _; intro i hi; obtain ⟨hp,ht'⟩:= mem_filter.mp hi; exact ((leap ht hu _ (Finset.mem_range.mp (mem_product.mp hp).1)).times (leap ht hv _ (Finset.mem_range.mp (mem_product.mp hp).2)) (show _=grade (i.1+i.2) from by unfold grade; push_cast; ring)).mono (cheaper ht')
    ext x; simp only [Pi.sub_apply,Finset.sum_apply,← hb]; apply sub_eq_iff_eq_add.mpr; exact (sum_filter_add_sum_filter_not ..).symm
lemma Looks.multiply (h:Looks N t k U a) (hp:Looks N t k V b): Looks N t k (U*V) (a*b):= by
   let A:= logit t k U; let B:=logit t k V; let C:=logit t k (U*V); have hv: N.Rush 0 a:= ((forecast ht h.alive).blend (h.price.mono (grade_zero _))).take (Eventually.of_forall (fun i=> show a i = A i+(a i-A i) from by abel)); refine ⟨h.alive.times hp.alive, ?_⟩; let p₀:=grade k; have hM: a*b-C=(a-A)* B+a*(b-B)+(A*B-C):= by ring;
   rw [show a*b-logit t k (U*V)=_ from hM]; exact ((h.price.times (forecast ht hp.alive) (add_zero _)).blend (hv.times hp.price (zero_add _))).blend (log_product ht h.alive hp.alive)
omit ht in
lemma identity (hk:0<k): Looks N t k 1 1:= by
   have he : logit t k 1=1:= by ext x; unfold logit; simp [pin, coeff_one,ite_mul,Finset.mem_range,hk]
   rw [← he] -- only target last arg. note replacements
   apply motto; intro i hi; exact Rush.settle (Resetter.pin (1:Resetter.Pow) i)
lemma Looks.powers (hk:0<k)(h:Looks N t k U a) (i:ℕ) : Looks N t k (U^i) (a^i):= by
    induction i with | zero=> rw [pow_zero,pow_zero]; exact identity hk| succ i ih=> rw [pow_succ,pow_succ]; exact ih.multiply ht h
omit ht in
lemma XBound (hk:1<k): Looks N t k (fun _=>X) t:= by
    let U: ℕ→Resetter.Pow:= fun _=> PowerSeries.X; have hf: logit t k U=t:= by ext x; unfold logit U pin; rw [Finset.sum_eq_single 1, coeff_one_X,one_mul,pow_one]; intro i _ hi; rw [coeff_X,if_neg hi]; ring; intro h; exact (h (Finset.mem_range.mpr hk)).elim
    rw [show (fun _:ℕ=>(X:Resetter.Pow))=U from rfl]; refine ⟨fun i _=> Rush.settle (Resetter.pin (X:Resetter.Pow) i),by rw [hf,sub_self]; exact Rush.zero⟩
omit ht
end Flux
end YM.Contacts.Allium
