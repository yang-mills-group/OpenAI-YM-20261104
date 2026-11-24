import YM.GradedFar.Logged.Pages
/-!
# G.5 at all reader layers, and G.7/8 part of bbcb (size of old packet vs basis)
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Logged.Trace
open Finset Filter Function Set Spec Table Extraction OPE.Log Asymptotics Orbits MeasureTheory
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff
open Economy (Paint)
variable {G:Gauge}{C:Family G}{f:Order}{S:Table C.book}
    (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {I L:Type} [Fintype I] (K:Economy.Small L) {M δ:ℝ}(hm:0≤M)(hd:0<δ)
    (x:L→I→E4)(z:L→E4) (hx:∀ᶠ i in K.p,WithinRoom (K.r i) M δ (x i) (z i))
    {d:I→ℕ}
    (bank : LogTrace F R.port) (v: Labels S d) (m:ℕ)
local notation "Q"=>F.sector.derivatives
local notation "r"=>K.r
open Stroke (lifetime)
local notation "ζ"=>fun l:L=>shadowOld R.port m (x l) (z l) v

/-- The budgets here depend on this word; for arbitrary basis callers across this
fixed physical space extend with MLM. Lifetime exact (see `Logged.Stroke`). -/
lemma rise_cut (m:ℕ)(x:S.Field m) : x= ∑ i:Fin (m+1), F.sector.derivatives.rise (d:=i.val) (Nat.le_of_lt_succ i.isLt) (R.cutTest i.val m x):= by
     rw [R.reconstruct m m le_rfl, (Q|>.arrival R.continuum.laws.toSymmetric R.lifts)]
include hd hm bank hx
lemma shadow_pair : Paint K (lifetime d m ∘ K.r)
    (fun i=> R.packet m (x i) v (z i)-ζ i) := by
    let A (i:Fin (m+1)):= (F.sector.derivatives.rise (d:=i.val) (Nat.le_of_lt_succ i.isLt))
    apply Paint.assists (Paint.sum _ (fun i _=> Paint.linear_c (A i) (Pages.fresh_log F R K hm hd x z hx bank v m i.val)))
      (f:=fun j=>∑ i:Fin (m+1), A i (R.fresh i.val (x j) (z j) v -R.cutTest i.val m (ζ j)))
    refine Eventually.of_forall (fun i=>?_)
    simp_rw [map_sub,Finset.sum_sub_distrib]; exact congrArg (R.packet m (x i) v (z i) - ·) (rise_cut F R m _).symm

abbrev core (d:I→ℕ) (m:ℕ) (t:ℝ):= t^m/t^(∑ i,d i)
lemma current : Paint K (core d m ∘ K.r) (fun l=> R.fresh m (x l) (z l) v) := by
    let f (j:Mode Q)(i:L):=((R.port).ope j (x i) (names v) (z i)) • R.cutTest m m (R.port.loaded j m)
    have hp (i:L):R.cutTest m m (ζ i)=∑ j∈bands Q m,f j i:=by simp only [shadowOld,shadow,map_sum,_root_.map_smul,f]
    have h j (hj:j∈ bands Q m) : Paint K (core d m ∘ K.r) (f j) := by
      obtain ht | ht := lt_or_eq_of_le ((full_bands ..).mp hj)
      · exact Paint.assists Paint.none (Eventually.of_forall (fun i=> by unfold f; rw [R.port.cost j hj,R.cut_rise,R.kills_lower _ _ ht,smul_zero]))
      obtain ⟨k,H⟩:= bank.terms I (names v) δ M hd hm j
      have he : Paint K (core d m ∘ K.r) (fun i=>(R.port).ope j (x i) (names v) (z i)) :=
        Paint.from_cost 1 zero_lt_one k (by
            filter_upwards [K.leaps.eventually H,hx] with i hi hx
            rw [one_mul]; exact ht ▸ (hi _ _ hx).2)
      unfold f; simpa only [mul_one,Function.comp_def] using (Paint.const (R.cutTest m m (R.port.loaded j m))).scales he
    apply Paint.assists (((Pages.fresh_log F R K hm hd x z hx bank v m m).eases (U:=core d m ∘ K.r) ?_).plus (Paint.sum _ h))
    swap
    · filter_upwards [K.positive,K.bounded] with i hi h; change |K.r i^(m+1)/_|≤|K.r i^m / _|
      rw [abs_of_pos (show 0 < K.r i^(m+1)/K.r i^(∑ l,d l) by positivity), abs_of_pos (show 0 < K.r i^m/K.r i^(∑ l,d l) by positivity)]; exact div_le_div_of_nonneg_right (pow_le_pow_of_le_one hi.le h (by omega)) (by positivity)
    filter_upwards with i; rw [← hp, sub_add_cancel]
end YM.OPE.Logged.Trace
