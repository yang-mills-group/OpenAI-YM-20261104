import YM.RGLocalTaylor.Mayer.Wing
import YM.RG12.Burst.Weight

/-!
# Taylor Reserve. Pay all geometric costs AND the number of vertices whose
own inside-expansion we start. Keep also the *whole* seed coefficient, used
later for hard and marked estimates. Adaptation of RG12.Burst's scent,
Coupon and width proofs, with no change to the membership at which used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}

open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
open Trees
namespace Mayer

abbrev firstLayer (Q : ConnectedActivityE6.Target G P) (L : Side) (μ x : ℝ) (j:ℕ) (u:ℝ) : ℝ :=
  Reserves.extract Q.ε j 0 0 * Reserves.treeYield (u*(Q.costs L μ 1 x 0).rootHit) (1/2) 0

lemma paid_mark (H : Cash W s μ L Q o C T R) (w e : Head S → ℝ)
    (hw:∀ i,0≤w i)(he:∀ i,0≤e i) {z u : ℝ} (hr : Ready H.supportP (radiusB s)
      (Reserves.tariff w e (fun i=> Q.mark L μ s * Mixed.shares S i) Q.ε) (Q.exp+2*Q.ε) z Q.δ q)
    (hu:0 < u) (hx:∀ i,H.shapeW i= Reserves.setPrice H.supportP (radiusB s) e i)
    (hpay : degreePrice (radiusB s) (u*z) Q.δ ≤ 1/2) (k:ℕ) :
    Ac.Hit H.unionP (radiusB s) (fun i=>
      (if H.ticketsP 0 0 0 i then (∏ i∈i,w i)*(1+H.shapeW i)^k else 0)*marking H i *u^i.card)
      Q.exp (Reserves.extract Q.ε k 0 0 * Reserves.treeYield (u*z) (1/2) 0) := by
  let c:= Q.exp; let B:= radiusB s; let f i:= u * Real.exp (Q.mark L μ s * Mixed.shares S i) * w i
  have heq:Reserves.tariff f e 0 Q.ε = fun i=> u*Reserves.tariff w e (fun i=> Q.mark L μ s * Mixed.shares S i) Q.ε i:=by
    funext i; unfold f Reserves.tariff; rw [Real.exp_add _ (Q.mark _ _ _ * _),Pi.zero_apply,add_zero]; ring
  have hf i : 0≤ f i:= mul_nonneg (mul_nonneg hu.le (Real.exp_pos _).le) (hw i)
  have hW:= Mixed.Coupons.inflate H.supportP B (Reserves.tariff w e (fun i=> Q.mark L μ s * Mixed.shares S i) Q.ε) hr hu hpay (by norm_num); rw [← heq] at hW
  intro x; let S i:= H.ticketsP 0 0 0 i; have hM:= Reserves.sets H.supportP B f e 0 hf he Q.usable Q.bound hW 0 k x S (T:=0) (U:=0) (fun i _ _ _ _=> ⟨hx i ▸ H.positive_volume i,by simp⟩)
  convert! hM using 2; rename_i i
  unfold Reserves.rooted; dsimp only; by_cases ht:H.ticketsP 0 0 0 i; swap
  · simp only [ht, ↓reduceIte,S,zero_mul,false_and]; split <;> rfl
  by_cases hv:x∈H.unionP i
  · have hζ:Ac.Spark H.supportP i:=(H.attends i).1 ht
    have hx':x∈i.biUnion H.supportP:=hv
    rw [if_pos ht,if_pos hv,if_pos ⟨ht,Nat.zero_le _⟩,if_pos ⟨hζ,hx'⟩,←hx i]
    unfold marking f; rw [Cash.numP,Nat.cast_sum,mul_sum,Real.exp_sum]; simp only [prod_mul_distrib,prod_const]; rw [show Finset.biUnion i H.supportP=H.unionP i from rfl]; unfold B Trees.currency; ring
  rw [if_neg hv,if_pos ⟨ht,Nat.zero_le _⟩,if_neg (show ¬ (Ac.Spark H.supportP i∧ x∈i.biUnion H.supportP) from fun h=> hv (show x∈H.unionP i from h.2)), zero_mul]

variable {ρ discount θ K α uJ vJ e : ℝ} {M : ℕ} {p : Molecule S} {N : Captain H j C' d v Y A b r B q n χ}

lemma marked_hits (H : Cash W s μ L Q o C T R) (Ξ : Utopia H j v d r C' χ) (l:ℕ) {u w:ℝ}
    (hu:0<u)(he: degreePrice (radiusB s) (u*(Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2) (hw : w ≤ Q.exp) :
    Ac.Hit H.smallAt (radiusB s) (fun i=> Ξ.meant i.val l * marking H i.val * u^i.val.card) w (firstLayer Q L μ s l u) := by
  let X:=Q.costs L μ R.beta s C'; let f (i:H.ThinP):= Ξ.meant i.val l * marking H i.val * u^i.val.card
  let e:= Mixed.lengths S X (ConnectedActivityE6.lengths T R)
  have h : Ready _ _ (Reserves.tariff Ξ.fare e _ _) (Q.exp+2*Q.ε) _ _ _:= Mixed.ready_vertices S Q.halo (radiusB s) X H.birth Ξ.flair _ _ Ξ.lives Ξ.accrues
  have he' i:0≤ e i:=by rcases i with i|i; exact mul_nonneg Ξ.lives.extra (Nat.cast_nonneg _); exact Nat.cast_nonneg _
  intro i; have hh:= budget_pull (fun i:H.ThinP=>Subtype.val i) Subtype.val_injective (paid_mark H Ξ.fare e Ξ.fares he' (z:=(Q.costs L μ 1 s 0).rootHit) h hu (fun _=>rfl) he l i)
  have hf j : 0 ≤ f j:= mul_nonneg (mul_nonneg (Ξ.meant_nonneg ..) (Real.exp_pos _).le) (pow_nonneg hu.le _)
  refine budget_mono hh (fun j=> ?_) (fun j=>?_) -- exponent charge helper
  · split; exact mul_nonneg (hf _) (Real.exp_pos _).le;rfl
  split
  next hx => dsimp only; rw [if_pos (show i∈H.unionP _ from hx)]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone
    (mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg _))) (hf _)
  exact hh.1 j

abbrev carrier (Ξ : Utopia H j v d r C' χ) (l M : ℕ) (e uJ θ ρ α : ℝ) (p : Molecule S) :=
  ((M+2:ℕ):ℝ)*prenex Ξ l M e uJ θ ρ α p

abbrev parentFee (Q:YM.ConnectedActivityE6.Target G P) (L:Side) (μ s uJ θ e ρ α:ℝ) (j l M:ℕ) :=
  Q.goal L s + ( (2^j:ℝ) * ((M+2:ℕ):ℝ) * speedBill e uJ α j)* firstLayer Q L μ s (l+j) (spreadRate M θ ρ)
set_option quotPrecheck false
local notation "vₜ" => parentFee Q L μ s uJ θ e ρ α j l M

lemma positions_pay (h : Awning H N.conduit A b discount e uJ vJ k l)
    (hk:Approved K θ j M) (hr:1 ≤ ρ) (hα:1 ≤ α) (he:degreePrice (radiusB s) (spreadRate M θ ρ * (Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2)
    (hp:degreePrice (radiusB s) vₜ η ≤ 1/2) (hη:0<η) (hA:a+η+η≤ Q.exp):
    Trees.Ready H.smallAt (radiusB s) (fun p=> (2^j:ℝ)*carrier N.conduit l M e uJ θ ρ α p.val)
      (a+η) vₜ η (1/2) := by
  let b:= spreadRate M θ ρ; let c:= speedBill e uJ α j; let A:=(2^j:ℝ)*((M+2:ℕ):ℝ)*c
  have hb:0<b:= zero_lt_one.trans_le (spread_pos hr hk.nonneg); have ht:= marked_hits H N.conduit (l+j) hb he hA
  have he:0≤A:= mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _)) (mul_nonneg h.earn (by have hv:=h.bSc; positivity))
  have hx:1 ≤ betaF G s L:=by rw [← H.laws.data.funds.length_eq]; exact H.laws.intake.height.le
  have hf:0 < Q.goal L s:= Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) _
  refine ⟨add_pos_of_pos_of_nonneg hf (mul_nonneg he (budget_nonneg (ht 0))),hη,hp,by norm_num,fun i=>
    mul_nonneg (pow_nonneg zero_le_two _) (mul_nonneg (Nat.cast_nonneg _) (pn_check h hk hα hr)),fun x=> ?_⟩
  apply budget_loosen (C:=A*firstLayer Q L μ s (l+j) b) ?_ (le_add_of_nonneg_left hf.le)
  convert! budget_scale he (ht x) using 2; rename_i i; dsimp only
  split
  · unfold carrier prenex A c b; ring
  simp
end Mayer
end YM.RGLocalTaylor
