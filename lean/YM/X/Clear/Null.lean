import YM.X.Clear.Mine
/-!
Supersmall IR estimates, polynomial budgets. `Void` ⇒Flat powers relative to regulator. UI = uniform via proof ∀ sequences in all relevant sets.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Interval
open Function Filter Set Metric MeasureTheory Lattice PertExtension LatticePT
open scoped Topology ContDiff BigOperators Pointwise Classical
variable {q:ℕ+} {G:Gauge} {R: Side} {j:ℕ} {n:ℕ}
open Pert.Align Asymptotics Real
local notation "r"=> (atTop:Filter ℕ)
set_option quotPrecheck false
variable (hq:1<q.val)

namespace Size

def ticket (q:ℕ+)(k:ℤ)(i:ℕ):ℝ:= magnify q i ^k
lemma ticket_pos (i:ℕ)(k:ℤ):0< ticket q k i:= zpow_pos (amp_pos ..) k
@[simp] lemma tickets_zero (i):ticket q 0 i=1:=zpow_zero _
lemma ticket_le {i:ℕ}{a b:ℤ}(h:a≤b):ticket q a i ≤ ticket q b i:=zpow_le_zpow_right₀ (cane q i) h
lemma ticket_add (q : ℕ+)(a b:ℤ) : ticket q a * ticket q b=ticket q (a+b):= funext fun x=> (zpow_add₀ (amp_pos q x).ne' a b).symm
lemma ticket_neg (q:ℕ+)(d:ℕ)(k:ℕ): ticket q (- (d:ℤ)) k= epsilon q k ^d:= by unfold ticket; rw [eps_eq,zpow_neg, zpow_natCast,inv_pow]
lemma ticket_nat (q:ℕ+)(d:ℕ)(k:ℕ): ticket q (d:ℤ) k=magnify q k^d:= zpow_natCast _ _
variable {α V E:Type*}
abbrev Ripe [Norm V] (q:ℕ+)(f:ℕ→V) (k:ℤ) := f =O[r] ticket q k
def Charged [Norm V](q:ℕ+)(f:ℕ→V): Prop:=∃ d:ℤ,Ripe q f d
def Vanished [Norm V](q:ℕ+)(f:ℕ→V): Prop:=∀ d:ℤ,Ripe q f d
namespace Ripe
section
variable [NormedAddCommGroup V]
variable {f g:ℕ→V}{a b:ℤ}
lemma eventual {B:ℝ} (hb : ∀ᶠ k:ℕ in atTop, ‖f k‖≤B*ticket q a k): Ripe q f a:= IsBigO.of_bound _ (hb.mono fun k h=> le_trans h (by rw [Real.norm_of_nonneg (ticket_pos ..|>.le)])) -- infer
lemma enlarge (h:Ripe q f a)(hx:a≤b):Ripe q f b:= h.trans (IsBigO.of_norm_eventuallyLE (Eventually.of_forall (fun i=> by change ‖ticket q a i‖ ≤ _; rw [Real.norm_of_nonneg (ticket_pos .. |>.le)]; exact ticket_le hx)))
lemma costed {a:ℝ}(hf:∀ᶠ i in atTop,‖f i‖≤a): Ripe q f 0:=eventual (B:=a) (by simpa only [tickets_zero,mul_one] using hf)
lemma constant (x:V):Ripe q (fun _=>x) 0:=costed (a:=‖x‖) (Eventually.of_forall (fun _=> le_rfl))
lemma summary {s:Finset α}{f:α→ℕ→V}(h:∀ i∈s,Ripe q (f i) a): Ripe q (∑ i∈s,f i) a:= by
   induction s using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact isBigO_zero ..
   | insert i s hi ih=>rw [Finset.sum_insert hi];exact (h i (by simp)).add (ih (fun j hj=> h j (by simp [hj])))
end
lemma times [NormedRing V] {f g:ℕ→V}{a b:ℤ}(h:Ripe q f a)(hx:Ripe q g b):Ripe q (f*g) (a+b):= by unfold Ripe;rw [← ticket_add]; exact h.mul hx
end Ripe
namespace Charged
section
variable [NormedAddCommGroup V]
variable {f g:ℕ→V}
lemma zero : Charged q (0:ℕ→V) := ⟨0,isBigO_zero ..⟩
lemma of_pay {d:ℤ} (h:Ripe q f d):Charged q f:=⟨d,h⟩
lemma constant (x:V):Charged q (fun _=>x):=of_pay (Ripe.constant _)
lemma add (h:Charged q f)(hx:Charged q g):Charged q (f+g):= by obtain ⟨a,h⟩:=h; obtain ⟨b,g⟩:=hx; exact ⟨max a b,(Ripe.enlarge h (le_max_left ..)).add (Ripe.enlarge g (le_max_right ..))⟩
lemma neg (h:Charged q f):Charged q (-f):=by obtain ⟨a,h⟩:=h;exact ⟨a,h.neg_left⟩
lemma finSum {s:Finset α}{f:α→ℕ→V}(h:∀ i∈s,Charged q (f i)): Charged q (∑ i∈s,f i) := by
   induction s using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact zero
   | insert i s hi ih=>rw [Finset.sum_insert hi];exact (h i (by simp)).add (ih (fun j hj=> h j (by simp [hj])))
end
lemma mul [NormedRing V] {f g:ℕ→V}(h:Charged q f)(hx:Charged q g):Charged q (f*g):= by obtain ⟨a,h⟩:=h; obtain ⟨b,g⟩:=hx; exact ⟨a+b,Ripe.times h g⟩
end Charged
namespace Vanished
section
variable [NormedAddCommGroup V] [Norm E]
variable {f g:ℕ→V}
lemma zero : Vanished q (0:ℕ→V):=fun _=> isBigO_zero ..
lemma small (h:Vanished q f): Charged q f:= ⟨0,h 0⟩
lemma add (h:Vanished q f)(hx:Vanished q g):Vanished q (f+g):= fun x=>(h x).add (hx x)
lemma neg (h:Vanished q f):Vanished q (-f):= fun x=> (h x).neg_left
lemma const_left [NormedSpace ℝ V] (k:ℝ) (h:Vanished q f):Vanished q (k • f):=fun x=> (h x).const_smul_left k
lemma sub (h:Vanished q f)(hx:Vanished q g):Vanished q (f-g):= sub_eq_add_neg f g ▸ h.add hx.neg
lemma previous {E:Type*}[NormedAddCommGroup E]{e:ℕ→ E} (he: f =O[r] e)(h:Vanished q e):Vanished q f:=fun d=> he.trans (h d)
lemma finSum {s:Finset α}{f:α→ℕ→V}(h:∀ i∈s,Vanished q (f i)): Vanished q (∑ i∈s,f i) := fun d=>Ripe.summary (fun i hi=> h i hi d)
lemma all {f:ℕ→V} (h:∀ d:ℕ,Ripe q f (-(d:ℤ))): Vanished q f:= by
   intro d; have ht:=h d.natAbs; apply Ripe.enlarge ht; omega
lemma goes (hq:1<q.val)(h:Vanished q f): Tendsto f r (𝓝 0):= by
   have ht := h (- (1:ℕ)); refine ht.trans_tendsto ?_; have ha := epsilon_zero hq
   apply ((paths hq).cutoff).congr; intro k; rw [ticket_neg, pow_one]; rfl
end
lemma left [NormedRing V] {f g:ℕ→V}(h:Vanished q f)(hx:Charged q g):Vanished q (f*g):=by intro d; obtain ⟨k,hx⟩:=hx; simpa only [sub_add_cancel] using! Ripe.times (h (d-k)) hx
lemma right [NormedRing V] {f g:ℕ→V}(h:Charged q f)(hx:Vanished q g):Vanished q (f*g):=by intro d; obtain ⟨k,h⟩:=h; simpa only [← add_assoc,add_neg_cancel,zero_add] using! Ripe.times h (hx (-k+d)) -- he
lemma side_small (hq:1<q.val): Vanished q (fun k=> ((side q k).val:ℝ)⁻¹):= by
   apply all; intro d; refine IsLittleO.isBigO (IsLittleO.of_tendsto_div_atTop ?_); change Tendsto (fun k=>ticket q (-(d:ℤ)) k * (((side q k).val:ℝ)⁻¹)⁻¹) r atTop; simp_rw [ticket_neg, inv_inv, mul_comm (epsilon .. ^ (_:ℕ))]; apply runaway hq
end Vanished
end Size
end YM.PositionX.Interval
