import YM.MergeProof.Vale
import YM.MergeProof.Sigil
/-!
# Closure with almost all of the forced suppression retained

`K` is not scaled in the construction. The absolute sums proof amplifies
its ticket prices using that every output `Period` actually spends ≥1 K
(even when all mark coefficients are used together).
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.XPhase
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open MergeProof MergeProof.Accent GridApprox.Nil Extra.Trajectories
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type*}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
variable {w: V→ℝ} {F: I→ Y→Poly B} {X:I→Support n} {b:ℕ}{d C t:ℝ}
-- Absolute arrays retain exact components at frozen radii
lemma zoom (s:ℂ)(F:Y→Poly B)(h:Loci w F t) : Loci w (fun i=>s • F i) (‖s‖*t):=by
   obtain ⟨f,hf,hP,hV⟩:=h
   refine ⟨fun i=> ‖s‖*f i,fun i=>mul_nonneg (norm_nonneg _) (hf i),fun i p=>?_,?_⟩
   · rw [Poly.part_smul, norm_mul]; exact mul_le_mul_of_nonneg_left (hP i p) (norm_nonneg _)
   unfold wordsPrice; exact le_trans (le_of_eq (b:=‖s‖*wordsPrice w f) (by unfold wordsPrice; rw [Finset.mul_sum];exact Finset.sum_congr rfl fun i _=> mul_left_comm ..)) (mul_le_mul_of_nonneg_left hV (norm_nonneg _))
lemma zone (s:ℂ) (h:Towed w X F b d C):Towed w X (s • F) b d (‖s‖*C):=by
    obtain ⟨a,ha,h,hA⟩:=h
    refine ⟨(fun i=>‖s‖*a i), ha.mul_left _,fun i=>?_,fun i=>zoom s _ (hA i)⟩
    have hh := Local.sumBudget_mul_left (h i) (norm_nonneg s)
    convert! hh using 2; rename_i i'; split<;> first|rw [mul_assoc]| rw [mul_zero]
section
variable [Fintype J][Fintype V]
variable (K:Box n→Config G n→Poly B)(u:J→Config G n→Poly B)(X:J→Support n)(s:ℝ)(t:ℝ)
set_option quotPrecheck false
local notation "KA"=> ((↑s:ℂ)⁻¹ • K)
set_option maxRecDepth 4000 in
omit [Fintype V] [Fintype J] in
lemma climbs (hs:0<s)(U:Config G n)(i:Period X) : crow K u X t i U=(↑s:ℂ)^i.val.toLeft.card • crow ((↑s:ℂ)⁻¹ • K) u X t i U:=by
    unfold crow; dsimp only; split; swap; · rw [smul_zero]
    have hx:(∏ j∈ i.val.toLeft,K j U)= (↑s:ℂ)^i.val.toLeft.card • ∏ j∈ i.val.toLeft,KA j U:=by
       have ht (j: Box n): K j U=(↑s:ℂ) • KA j U:=by change K j U=(s:ℂ) • ((↑s:ℂ)⁻¹ • K j U); rw [smul_inv_smul₀ (by exact_mod_cast hs.ne')]
       have hl : ∀ A: Finset (Box n), (∏ j ∈ A,K j U)=(↑s:ℂ)^A.card • ∏ j∈A,KA j U:=by
          intro A; induction A using Finset.induction with
          | empty=> simp only [Finset.prod_empty, Finset.card_empty, pow_zero, one_smul]
          | insert j A hj ih=>
              rw [prod_insert hj,prod_insert hj,card_insert_of_notMem hj,ih,pow_succ',mul_smul]
              conv_lhs => lhs; rw [ht]
              rw [smul_mul_assoc, mul_smul_comm]
       apply hl
    rw [prod_sum_eq_prod_toLeft_mul_prod_toRight,prod_sum_eq_prod_toLeft_mul_prod_toRight]; change (∏ j∈ i.val.toLeft,K j U)*(∏ j∈i.val.toRight,u j U) = (↑s:ℂ)^_ • ((∏ j∈i.val.toLeft,KA j U)*(∏ j∈i.val.toRight,u j U)); rw [hx]; exact smul_mul_assoc ..
private lemma branchBase {e v P : ℝ}(hp:Towed w Prod.fst K b (d+e) P)(hh:Towed w X u b (d+e) v)(hx:∀ i,0<w i)(he:0≤d)(ht:((b+b+1:ℕ):ℝ)^4*(P+v)≤ e): Towed w (Prod.fst ∘ forst X) (crow K u X t) b d (Real.exp (P+v)-1):=by
   -- reproduce proof of branch from YM.MergeProof.Vale. Each complete pinned crown.
   let l:=bloom X
   obtain ⟨a,ha,hA,h⟩:=hp; obtain ⟨f,hf,hB,hp⟩:=hh
   let g(i: FlowKind J n):= i.elim a f; have hv i:Loci w (pork K u i) (g i):=by cases i;exact h _; exact hp _
   have hG i : 0 ≤ g i:= (hv i|>.fares hx).1
   choose C hC hh h0 using hv
   let e'(i:Period X):=∏ j∈i.val,g j
   have ht' : Hit l b g (d+e) (P+v):=by
     intro i
     refine Extra.Multi.Budget.certify (fun j=>by split; exact mul_nonneg (hG _) (Real.exp_pos _).le; exact le_rfl) fun p=>?_ ; rw [sum_sum_eq_sum_toLeft_add_sum_toRight]; exact add_le_add (Extra.Multi.Budget.cap (hA i) _) (Extra.Multi.Budget.cap (hB i) _)
   have ht(z):= forest_price (f:=g) l b he hG ht' ht ((tsum_nonneg (ht' 0).1|>.trans (ht' 0).2.2)) z
   refine ⟨e',Summable.of_finite,fun i=> ?_, fun i=>?_⟩
   · refine Extra.Multi.Budget.pull_le (q:=Subtype.val) (p:=fun _=>True) (ht i) (fun i=> by split; exact mul_nonneg (prod_nonneg (fun j _=> hG j)) (Real.exp_pos _).le;exact le_rfl) (fun _ _=> trivial) Subtype.val_injective.injOn (fun j _=> ?_)
     unfold Ac.roots; by_cases h:i∈ (forst X j).1
     · rw [if_pos (show i∈(Prod.fst ∘ forst X) j from h),if_pos ⟨j.property.spark,h⟩]; exact le_of_eq (mul_comm ..)
     rw [if_neg (show i∉(Prod.fst ∘ forst X) j from h),if_neg (fun hh=> h hh.2)]
   obtain ⟨q,hq,he,hw⟩:= all_prices i.val C g (fun x l=>pork K u l x) w hx hC h0 (fun x i=>hh i x); refine ⟨q,hq,fun U p=>?_,he⟩
   unfold crow; dsimp only; split; exact hw U p; simpa using hq p

set_option maxHeartbeats 400000 in
lemma branch_scaled {e v P : ℝ}(hs:0<s)(h1:s≤1)(hp:Towed w Prod.fst K b (d+e) P)(hh:Towed w X u b (d+e) v)(hx:∀ i,0<w i)(he:0≤d)(ht:((b+b+1:ℕ):ℝ)^4*(P/s+v)≤e):Towed w Prod.fst (Accent.closure K u X t) b d (s*(Real.exp (P/s+v)-1)):=by
    apply towing _ _ _ hx
    have h:Towed w Prod.fst KA b (d+e) (P/s):=by
       have hh:= XPhase.zone (↑s:ℂ)⁻¹ hp; rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg hs.le, inv_mul_eq_div] at hh; exact hh
    obtain ⟨a,ha,hf,hA⟩:= branchBase KA u X t h hh hx he ht
    refine ⟨fun i=> s*a i,ha.mul_left _,fun i=>?_,fun i=>?_⟩
    · have hh:= Local.sumBudget_mul_left (hf i) hs.le; convert! hh using 2; rename_i j; split<;>first|rw [mul_assoc]|rw [mul_zero]
    let p:= i.val.toLeft.card; let F:= (↑s:ℂ)^p
    obtain ⟨g,hg,hP,hV⟩:= XPhase.zoom F _ (hA i)
    refine ⟨g,hg,fun U x=> ?_, hV.trans (mul_le_mul_of_nonneg_right ?_ ((hA i).fares hx).1)⟩
    · rw [climbs K u X s t hs]; exact hP _ _
    unfold F; rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg hs.le]; have hp:0<p:= Finset.card_pos.mpr i.property.life; exact (pow_le_pow_of_le_one hs.le h1 hp).trans_eq (pow_one _)
end
end YM.LocalLTE.XPhase
