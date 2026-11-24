import YM.AllOrder.Response.Weigh
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Response
open Finset Filter Function Laplace.SigmaP Laplace PositionX.Jet PertExtension.Series PositionX.Gauss Asymptotics
open scoped Topology ContDiff BigOperators Classical
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X]{P:ℝ→X} (hp:ContDiffAt ℝ ω P 0) {u v:Book X}{n k:ℕ}{x:X}
omit hp in
lemma Budget.sub (h:Budget x u n)(H:Budget x v n): Budget x (u-v) n:= fun i hi=> (h i hi).sub (H i hi)
omit hp in
lemma Budget.transpose (h:Budget x u n)(H:∀ i≤n,u i=v i):Budget x v n:= fun i hi=> H i hi ▸ h i hi
def energy (v:Book X)(k:ℕ): Book X:= Function.swap fun x=> xpow (Function.swap v x) k
def arrow (a:Tape) (v:Book X) (n:ℕ): Book X:= ∑ k∈Finset.range (n+1), a k • energy v k
omit [NormedSpace ℝ X] [NormedAddCommGroup X] in
lemma square_real (a:Tape)(u:Book X)(x:X)(n:ℕ): Function.swap (arrow a u n) x= onward a (Function.swap u x) n := by funext t; unfold arrow onward swap energy; simp [Finset.sum_apply]
omit [NormedSpace ℝ X][NormedAddCommGroup X] in
lemma powered (u:Book X)(i:ℕ): energy u (i+1)= alters (energy u i) u:=by funext j x; exact congr_fun (power i) j
omit [NormedSpace ℝ X][NormedAddCommGroup X] in
lemma level (u:Book X) : energy u 0=wirings (fun _=>1):=by funext k x; exact congr_fun (power_zero _) k
omit hp in
lemma Budget.tips (h:Budget x u n) (r:ℕ):Budget x (energy u r) n:=by
 induction r with
 | zero=> rw [level]; exact install_just _ contDiffAt_const
 | succ r ih=>rw [powered]; exact plus_in ih h
variable {I:Type*}{z:I→ Book X}
omit hp in
lemma Budget.sum {s:Finset I} (he:∀ i∈s,Budget x (z i) n): Budget x (∑ i∈s, z i) n:=by intro i hi; rw [Finset.sum_apply, ← show (fun t=> ∑ j∈s,z j i t)= ∑ j∈s,z j i from funext fun j=> Eq.symm (Finset.sum_apply ..)]; exact ContDiffAt.sum fun j hj=> he j hj i hi
omit hp in
lemma Budget.arrow (h:Budget x u n) (a:Tape)(b:ℕ): Budget x (_root_.YM.AllOrder.Response.arrow a u b) n := Budget.sum fun i _=> (h.tips i).scale
variable (h:Budget (P 0) u n)
include hp
include h
lemma weigh_sub (hk:k≤n)(H:Budget (P 0) v n): weigh P (u-v) k=weigh P u k-weigh P v k:= by
 unfold weigh; rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun i hi=>?_); have hl : i≤n:=(Nat.le_of_lt_succ (mem_range.mp hi)).trans hk; exact congr_fun (some_sub ((h _ hl).comp _ hp) ((H _ hl).comp _ hp)) _
omit h
lemma weigh_sum (hk:k≤n) {s:Finset I} (he:∀ i∈s,Budget (P 0) (z i) n): weigh P (∑ i∈s,z i) k=∑ i∈s,weigh P (z i) k:= by
 induction s using Finset.induction_on with
 | empty=> simp only [Finset.sum_empty]; rw [← show wirings (X:=X) (fun _=>0) = 0 by funext i x; simp [swap,wirings,just]]; rw [just_read hp contDiffAt_const]; exact ((Act.static (n:=k) (0:ℝ)).writes k le_rfl).trans (by simp [just])
 | insert i s hi ih=>
    have hq(k)(hb:k∈s):=he k (mem_insert_of_mem hb)
    rw [Finset.sum_insert hi,Finset.sum_insert hi,weigh_add hp (he i (mem_insert_self ..)) (Budget.sum hq) hk,ih hq]
omit hp in
lemma weigh_transpose (H: ∀ i≤k,u i=v i):weigh P u k=weigh P v k:= Finset.sum_congr rfl fun i hi=>by rw [H _ (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
omit hp in
lemma weigh_trans (Q:∀ᶠ t in 𝓝 0,u 0 (P t)=v 0 (P t)) : weigh P u 0=weigh P v 0:= by simp [weigh,Q.self_of_nhds]
include h
lemma weigh_power (r:ℕ): ∀ k≤n,weigh P (energy u r) k=xpow (weigh P u) r k:= by
 induction r with
 | zero=> intro k _; rw [level,just_read hp contDiffAt_const,power_zero]; exact (Act.static (n:=k) (1:ℝ)).writes _ le_rfl
 | succ r ih => intro k hk; rw [power,powered,weigh_mul hp (h.tips r) h hk,plus_sum,plus_sum]; refine Finset.sum_congr rfl fun i hi=>?_ ; have he:=mem_antidiagonal.mp hi; rw [ih _ (by omega)]
lemma weigh_arrow (hk:k≤n) (a:Tape)(b:ℕ): weigh P (arrow a u b) k= onward a (weigh P u) b k:= by unfold arrow onward; rw [weigh_sum hp hk (fun i (_:i∈ Finset.range (b+1))=> (h.tips i).scale),Finset.sum_apply]; simp_rw [weigh_scale hp (h.tips _) hk, weigh_power hp h _ _ hk]; rfl
-- exp and log convention. u0=0 & u0=1 coefs constant.
abbrev EXP (u:Book X): Book X:= swap (expS ∘ swap u)
abbrev LOG (u:Book X): Book X:= swap (logS ∘ swap u)
omit hp h in
lemma Expo (h:u 0=0)(hk:k≤n): EXP u k= arrow (fun i=>(i.factorial:ℝ)⁻¹) u n k:= by
 funext x; change expS (swap u x) k =_; rw [exp_pay (show light (swap u x) from congr_fun h x) hk, ← square_real]
omit hp h in
lemma Lords (h:u 0=1)(hk:k≤n): LOG u k= arrow (someJ (fun x:ℝ=>Real.log (x+1))) (u-wirings (fun _=>1)) n k:= by
 funext x; change logS (swap u x) k =_; rw [log_pay (show swap u x 0=1 from congr_fun h x) hk, show swap u x-just (1:ℝ)=swap (u - wirings (fun _=>1)) x from rfl, ← square_real]
omit hp h in
lemma Budget.eXp (h:Budget x u k)(h':u 0=0):Budget x (EXP u) k:= (h.arrow _ k).transpose (fun i hi=>(Expo h' hi).symm)
omit hp h in
lemma Budget.loG (h:Budget x u k)(h':u 0=1):Budget x (LOG u) k:= ((h.sub (install_just _ contDiffAt_const)).arrow _ k).transpose (fun i hi=>(Lords h' hi).symm)
lemma weigh_exp (h':u 0=0)(hk:k≤n):weigh P (EXP u) k=expS (weigh P u) k:= by
 rw [weigh_transpose (fun i hi=> Expo h' (hi.trans hk)), weigh_arrow hp h hk, exp_pay (n:=n) (show light (weigh P u) from (by simp [weigh,h',light])) hk]
lemma weigh_log (h':u 0=1)(hk:k≤n):weigh P (LOG u) k=logS (weigh P u) k:= by
 rw [weigh_transpose (fun i hi=> Lords h' (hi.trans hk)),weigh_arrow hp (h.sub (install_just _ contDiffAt_const)) hk, log_pay (show weigh P u 0=1 from (by simp [weigh,h'])) hk, onward,onward, Finset.sum_apply,Finset.sum_apply]
 -- congr via pow
 refine Finset.sum_congr rfl fun i hi=>?_ ; simp only [Pi.smul_apply]; congr 1; induction i generalizing k with
 | zero=> rw [power_zero,power_zero]
 | succ i ih=> rw [power,power,plus_sum,plus_sum]; refine Finset.sum_congr rfl fun j hj=>?_ ; have hh:= mem_antidiagonal.mp hj; rw [ih (by omega) (by simp only [mem_range] at *; omega), weigh_sub hp h (by omega) (install_just _ contDiffAt_const),just_read hp contDiffAt_const]; rw [show someJ ((fun (_:X)=>1) ∘ P) j.2=just (1:ℝ) j.2 from (Act.static (n:=j.2) _).writes _ le_rfl]; rfl
end YM.AllOrder.Response
