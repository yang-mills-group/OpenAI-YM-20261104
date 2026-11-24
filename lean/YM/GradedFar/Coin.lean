import YM.GradedFar.Sold
import YM.GradedFar.Paid
/-!
# C5Price purchases require use after finite trimmings & recrops

Single k purchase (not global all powers simultaneously). Use weights for x profiles as on that installation.
Doesn't push clocks into the index-dependent formal coefficients. Allows them to be actual formal valued
families at those inputs, even varying T. Multiplicative prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff.Tickets
open Function Filter Set PowerSeries
open FVA2.GradedFar
open Fork (Sold Safe)
open scoped Topology BigOperators Classical
variable {X I L : Type*} {φ : Filter X} {W : X→I→Prop} {B : X→I→ℝ} {t:X→ℝ} {p q:ℕ}
    {f h d:X→I→ℂ} {F H:X→I→PowerSeries ℂ}
-- All powers cost in the x weight, possibly uncoupled.
abbrev Prospects (φ : Filter X)(W:X→I→Prop)(B:X→I→ℝ)(F:X→I→PowerSeries ℂ) :=∀ i:ℕ,Sold φ W B (fun _ _=>1) (fun x k=> coeff i (F x k))

structure Coins (φ : Filter X)(W : X→I→Prop)(B:X→I→ℝ)(t:X→ℝ):Prop where
 spaces : Safe φ W B (fun _ _=>1)
 tiny : Tendsto t φ (𝓝 0)
local notation "u"=> Coins φ W B t -- not in variable commands
structure WithTax (p:ℕ)(φ : Filter X)(W : X→I→Prop) (B:X→I→ℝ) (t:X→ℝ) (f:X→I→ℂ)(F:X→I→PowerSeries ℂ): Prop where
 cost: Prospects φ W B F
 error: Sold φ W B (fun i _=> |t i|^(p+1)) (fun i j=> f i j-crop p (t i) (F i j))

local notation "σ"=> Sold φ W B
local notation "η"=> WithTax p φ W B t
variable (H0:Coins φ W B t)
local notation "Ζ"=> fun (x:X)(_i:I)=> |t x|^(p+1)
lemma Lucky (q:X→I→Prop)(hr:Filter X)(B:X→I→ℝ)(a:ℂ): Sold hr q B (fun _ _=>1) (fun _ _=>a):= Fork.Sold.closed a
namespace Coins
lemma safe (H : Coins φ W B t)(p:ℕ): Safe φ W B (fun x _=>|t x|^p):= H.spaces.joint
    (Eventually.of_forall fun i j _=> by positivity)
lemma leOne (H:Coins φ W B t)(p:ℕ): ∀ᶠ i in φ,|t i|^p≤1:= (H.tiny.abs.eventually_le_const (by simp:|(0:ℝ)|<1)).mono
    (fun i hi=> pow_le_one₀ (abs_nonneg _) hi)
lemma revert (H:Coins φ W B t)(v:X→ℝ)(ht:Tendsto v φ (𝓝 0)):Coins φ W B v:=⟨H.spaces,ht⟩
lemma zero (H:Coins φ W B t)(hf:σ (fun _ _=>1) f)(hh:σ (fun _ _=>1) h): σ (fun _ _=>1) (fun i j=> f i j*h i j):=by
 simpa only [mul_one] using Fork.Sold.mul H.spaces hh hf
lemma left (H:Coins φ W B t)(hf:σ (fun _ _=>1) f)(hh:σ Ζ h): σ Ζ (fun i j=>f i j*h i j):= by simpa only [one_mul] using Fork.Sold.mul (H.safe (p+1)) hh hf
lemma right (H:Coins φ W B t)(hf:σ Ζ f)(hh:σ (fun _ _=>1) h): σ Ζ (fun i j=> f i j*h i j):=by simp_rw [mul_comm (f _ _)]; exact H.left hh hf
lemma fixed (H:Coins φ W B t)(p:ℕ): σ (fun _ _=>1) (fun i (_:I)=> (t i:ℂ)^p):=
 Fork.Sold.bounded (c:=1) zero_le_one ((H.leOne p).mono fun i hi j _=>by rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,mul_one]; exact hi)
-- foot for prices along infinite p? no. only through k.
lemma omitted (H:Coins φ W B t)(q k:ℕ)(hq:q≤k): σ (fun i _=>|t i|^q) (fun i (_:I)=> (t i:ℂ)^k):=
 Fork.Sold.bounded (c:=1) zero_le_one ((H.tiny.abs.eventually_le_const (by simp:|(0:ℝ)| <1)).mono
     fun i hi j _=> by rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,one_mul]; exact pow_le_pow_of_le_one (abs_nonneg _) hi hq)
end Coins
include H0
lemma procrop (p:ℕ)(h:Prospects φ W B F): σ (fun _ _=>1) (fun i j=> crop p (t i) (F i j)):= by
 simp_rw [crop_eq]; exact Fork.Sold.sum H0.spaces (fun k _=> H0.zero (H0.fixed k) (h k))
lemma count_pair (p:ℕ)(hf:Prospects φ W B F)(hh:Prospects φ W B H): σ (fun x _=> |t x|^(p+1)) (fun i j=> crop p (t i) (F i j) * crop p (t i) (H i j) - crop p (t i) (F i j*H i j)):=by
 simp_rw [separate,add_sub_cancel_left]; exact H0.right (H0.omitted _ _ le_rfl) (Fork.Sold.sum H0.spaces (fun k _=>
    H0.zero (H0.fixed _) (H0.zero (hf _) (hh _))))
namespace WithTax
omit H0 in
lemma constant (f:ℂ): η (fun _ _=>f) (fun _ _=>PowerSeries.C f):=by
 refine ⟨fun k=>?_,?_⟩
 · simp_rw [coeff_C]; exact Lucky ..
 simp_rw [constant_crop,sub_self]; exact Fork.Sold.zero
lemma total (hf:η f F): σ (fun _ _=>1) f:= by
 obtain hv:= Fork.Sold.more hf.error (H0.spaces.mono fun i hi j hj=> zero_le_one.trans (hi j hj).1)
    ((H0.leOne (p+1)).mono fun x h _ _=> h)
 exact (Fork.Sold.add H0.spaces hv (procrop H0 _ hf.cost)).congr fun i j=>sub_add_cancel ..
omit H0 in
lemma tran (hf:η f F)(hv:∀ᶠ i in φ,∀ j,W i j→ f i j=h i j)(h' :∀ᶠ i in φ,∀ j,W i j→ F i j=H i j): η h H:= by
 refine ⟨fun k=>Fork.Sold.price (hf.cost k) ?_,Fork.Sold.price hf.error ?_⟩
 · filter_upwards [h'] with i hi j hj; rw [hi j hj]
 filter_upwards [h',hv] with i hi hv j hj; rw [hi j hj,hv j hj]
lemma correct (hf:η f F)(hh:σ Ζ (fun x i=>h x i-f x i)): η h F:=
 ⟨hf.cost,(Fork.Sold.add (H0.safe (p+1)) hh hf.error).congr (fun _ _=>sub_add_sub_cancel ..)⟩
lemma add (hf:η f F)(hh:η h H): η (fun i j=> f i j+h i j) (fun i j=> F i j+H i j):= by
 refine ⟨fun k=>?_,?_⟩
 · simp_rw [map_add]; exact Fork.Sold.add H0.spaces (hf.cost _) (hh.cost _)
 simp_rw [map_add]; exact (Fork.Sold.add (H0.safe (p+1)) hf.error hh.error).congr (fun i j=> by abel)
lemma sum (s:Finset L) {f:L→X→I→ℂ} {F:L→X→I→PowerSeries ℂ}(H:∀ i∈s,η (f i) (F i)): η (fun x i=>∑ j∈s,f j x i) (fun x i=>∑ j∈s,F j x i) := by
 induction s using Finset.induction_on with
 | empty => simpa only [Finset.sum_empty, map_zero] using (WithTax.constant (φ:=φ) (W:=W) (t:=t) (B:=B) (p:=p) 0)
 | insert i s hi ih => simp_rw [Finset.sum_insert hi]; exact (H i (Finset.mem_insert_self ..)).add H0 (ih fun j hj=> H j (Finset.mem_insert_of_mem hj))
lemma mul (hf:η f F)(hh:η h H): η (fun i j=> f i j*h i j) (fun i j=> F i j*H i j):= by
 refine ⟨fun k=>?_,?_⟩
 · simp_rw [coeff_mul]; exact Fork.Sold.sum H0.spaces (fun q _=> H0.zero (hf.cost _) (hh.cost _))
 obtain h₁:= H0.right hf.error (hh.total H0); obtain h₂:= H0.left (procrop H0 p hf.cost) hh.error
 exact ((h₁.add (H0.safe _) h₂).add (H0.safe _) (count_pair H0 p hf.cost hh.cost)).congr fun i j=> by ring
lemma product (s:Finset L) {f:L→X→I→ℂ} {F:L→X→I→PowerSeries ℂ}(H:∀ i∈s,η (f i) (F i)): η (fun x i=>∏ j∈s,f j x i) (fun x i=>∏ j∈s,F j x i) := by
 induction s using Finset.induction_on with
 | empty => simpa only [Finset.prod_empty, map_one] using (WithTax.constant (φ:=φ) (W:=W) (t:=t) (B:=B) (p:=p) 1)
 | insert i s hi ih => simp_rw [Finset.prod_insert hi]; exact (H i (Finset.mem_insert_self ..)).mul H0 (ih fun j hj=> H j (Finset.mem_insert_of_mem hj))
lemma crop_later (hp:p≤q) (h: Prospects φ W B F): η (fun i j=> crop q (t i) (F i j)) F:=by
 refine ⟨h,?_⟩; simp_rw [crop_eq, ← Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ hp)]; exact Fork.Sold.sum (H0.safe (p+1))
    (fun k hk=> H0.right (H0.omitted (p+1) k (Finset.mem_Ico.mp hk).1) (h k))
-- no substitute law unless doing larger algebra. just for switching from neighbor clock when clocks are already numerically near at this precision.
lemma switch (a:X→ℝ)(ha:Tendsto a φ (𝓝 0))(hv:σ Ζ (fun x (_:I)=> (a x:ℂ)-(t x:ℂ))) (hp:p≤q)(hc: Prospects φ W B F): η
    (fun i j=> crop q (a i) (F i j)) F := by
 have H(k:ℕ):σ Ζ (fun i (_:I)=> (a i:ℂ)^k-(t i:ℂ)^k):=by
   induction k with
   | zero=> simp_rw [pow_zero, sub_self]; exact Fork.Sold.zero
   | succ k ih=>
        obtain h₁:= H0.right ih ((by convert (H0.revert a ha).fixed 1 using 1; simp : σ (fun _ _=>1) (fun i (_:I)=> (a i:ℂ))))
        exact ((Fork.Sold.add (H0.safe _) h₁ (H0.left (H0.fixed k) hv))).congr fun i _=> by ring
 refine correct H0 (crop_later H0 hp hc) ?_; simp_rw [crop_eq, ← Finset.sum_sub_distrib, ← sub_mul]; exact Fork.Sold.sum (H0.safe (p+1))
   (fun k _=> H0.right (H k) (hc k))
end WithTax
end YM.Integration.GradedFar.Tariff.Tickets
