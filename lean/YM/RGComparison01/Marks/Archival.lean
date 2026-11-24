import YM.RGComparison01.Marks.Slate
import YM.RGComparison01.Ranch
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Archival
open Function Filter Finset MeasureTheory Merge Switch Marker GridRenewal.Rain
open AuxJets AuxStage AuxFabric AuxStage.Points Slate Lattice
open scoped Topology ContDiff BigOperators Classical
variable {ι:Type} [Fintype ι] {G:Gauge}{L:Lattice.Side}{u : ℝ→ℝ}
variable {i m k j w n:ℕ} {d v h:ℝ} {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {x:E}
-- unvaluated shell generator for TOTAL cumulants independent of c valuation
open Spline
abbrev CoBook (ι E: Type):= Finset ι→ Co E
def bundle (H:CoBook ι E): ℕ → CoBook ι E
 | 0=> fun p=> scalar (Switch.bench ∅ 1 p)
 | n+1=> fun p=> ∑ z:Finset ι × Finset ι,if p=z.1∪z.2 ∧ Disjoint z.1 z.2 then weave (bundle H n z.1) (H z.2) else 0
-- budgets depend only on demanded aux instance
local notation "𝕀"=>Fintype.card ι
def vessel (k j m:ℕ)(v:ℝ) : ℕ→ℝ
 | 0=>1
 | n+1=> ((2:ℝ)^m)^2 * fuse k j (vessel k j m v n) v
def imageSet (H:CoBook ι E)(m:ℕ): ℕ → CoBook ι E
 | 0=> 0
 | n+1=> fun p=> if p=∅ then 0 else H p- ∑ i∈Finset.range (m+1), (levy (i+2)) • bundle (imageSet H m n) (i+2) p
-- powers pay
def fee (k j m:ℕ)(v:ℝ): ℕ → ℝ
 | 0=> 0
 | n+1=>v + ∑ i∈Finset.range (m+1), levy (i+2) * vessel k j m (fee k j m v n) (i+2)
local notation "ℝ₊"=> (0:ℝ)
lemma vat {a b : ℝ} (h : 0 ≤ a) (he:0 ≤ b): ℝ₊ ≤ fuse k j a b := by unfold fuse allowance cores; positivity
lemma produce (hv : 0 ≤ v)(n : ℕ) : 0 ≤ vessel k j m v n:= by induction n with|zero=> rw [vessel]; exact zero_le_one|succ i ih=> rw [vessel]; exact mul_nonneg (sq_nonneg _) (vat ih hv)
lemma aside (hv : 0 ≤ v)(n : ℕ) : 0 ≤ fee k j m v n:= by
  induction n with
  | zero=>rw [fee]
  | succ i ih=> rw [fee]; exact add_nonneg hv (sum_nonneg fun i _=>mul_nonneg (by unfold levy; positivity) (produce ih _))
lemma hum (hv : Geo G L u)(n : ℕ) : Geo G L (fun t=> vessel k j m (u t) n):= by
  induction n with
  | zero=> exact Geo.fixed _
  | succ i ih=> simp only [vessel]; exact (Geo.fixed _).times (fusion_geo _ _ ih hv)
lemma accepts (hv : Geo G L u)(n : ℕ) : Geo G L (fun t=> fee k j m (u t) n):= by
  induction n with
  | zero=>exact Geo.fixed _
  | succ i ih=>
    simp only [fee]; exact hv.joins (Geo.expel _ (fun i t=> levy (i+2)*vessel k j m (fee k j m (u t) _) (i+2)) (fun i _=> (Geo.fixed _).times (hum ih _)))
variable {p : Finset ι} {M:CoBook ι E}
lemma degree (hM:∀ i,Spline.Field w n (M i))(p:Finset ι)(i:ℕ) : Spline.Field (w*i) n (bundle M i p):= by
  induction i generalizing p with
  | zero=> exact Field.scalar (E:=E) _ _ _
  | succ i ih=>
    simp only [bundle]; rw [Nat.mul_succ]; refine Field.roots _ _ (fun t _=>?_); split
    · exact (ih t.1).weave (hM t.2)
    exact fun _ _=> Spline.vacant (E:=E) _ _
-- polynomial degree after Shell delta matrix. Simple safe Bound.
def waf (m w:ℕ): ℕ→ℕ
 | 0=> 0
 | n+1=> w+waf m w n*(m+2)
lemma artist (hM:∀ i,Spline.Field w n (M i))(m i:ℕ)(p:Finset ι) : Spline.Field (waf m w i) n (imageSet M m i p):= by
   induction i generalizing p with
   | zero=> exact fun _ _=> Spline.vacant (E:=E) _ _
   | succ i ih=>
     simp only [imageSet]; split
     · exact fun _ _=> Spline.vacant (E:=E) _ _
     rw [show M p - _=M p+(-1:ℝ) • ∑ i'∈range (m+1), levy (i'+2) • bundle (imageSet M m i) (i'+2) p from (by simp [sub_eq_add_neg]),waf]; refine Field.add ((hM p).weaken (Nat.le_add_right _ _)) (Field.smul (Field.roots _ _ (fun t ht=>?_)) _)
     have hp:= mem_range.mp ht; refine Field.smul (Field.weaken (degree ih p _) (le_trans (Nat.mul_le_mul_left (waf m w i) (show t+2 ≤ m+2 from (by omega))) ?_)) _
     omega

-- p cost with upper ℙ bound
lemma tallyR (h:𝕀 ≤ m) : (Fintype.card (Finset ι × Finset ι):ℝ) ≤ ((2:ℝ)^m)^2 := by
  rw [Fintype.card_prod,Fintype.card_finset]; push_cast; rw [← pow_two]; exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) h) _

variable (hd:0 ≤ d)(hh: 0 ≤ h)(hH:h ≤ 1) {F : E→Score ι} (ht:Fintype.card ι ≤ m)
include hd hh hH ht
lemma boundP (hM:∀ p, AuxStage.Points v d h k j (fun x=> F x p) x (M p))(n:ℕ)(p:Finset ι) : AuxStage.Points (vessel k j m v n) d h k j (fun x=>stack (F x) n p) x (bundle M n p):= by
  induction n generalizing p with
  | zero=>
    unfold bundle vessel; apply (start (bench ∅ 1 p) hd hh).funding _ hh le_rfl
    unfold Switch.bench; split
    · rw [norm_one]
    rw [norm_zero]; norm_num
  | succ i ih=>
    let v':= fuse k j (vessel k j m v i) v
    have h₀ : 0 ≤ v':= vat (produce ((hM p).nonneg) i) (hM p).nonneg
    unfold bundle vessel
    let y (z: Finset ι× Finset ι) := weave (bundle M i z.1) (M z.2); let W z:= if p=z.1∪z.2∧Disjoint z.1 z.2 then y z else (0:Co E)
    let f (z: Finset ι× Finset ι) (x:E) := if p=z.1∪z.2∧Disjoint z.1 z.2 then stack (F x) i z.1 * F x z.2 else 0
    have hx z : AuxStage.Points v' d h k j (f z) x (W z):= by
      unfold f W; split
      next hz=> exact (ih z.1).multiply (hM z.2) hh hH
      next hz=> exact constant_zero hd hh|>.funding h₀ hh le_rfl
    have hp:=Points.summing (fun z=>v') W f univ hd hh (fun i _=>hx i);
    rw [sum_const,card_univ,nsmul_eq_mul] at hp
    refine (hp.funding (mul_le_mul_of_nonneg_right (tallyR ht) h₀) hh le_rfl).adjust (Eventually.of_forall fun i' => ?_)
    simp only [stack,flesh, Finset.sum_apply, f]
lemma source (hv: 0 ≤v) (hp:∀ p: Finset ι,p≠∅ → AuxStage.Points v d h k j (fun x=> F x p) x (M p)) (n:ℕ)(p:Finset ι) : AuxStage.Points (fee k j m v n) d h k j (fun x=>shell m (F x) n p) x (imageSet M m n p):= by
   induction n generalizing p with
   | zero=> exact constant_zero hd hh
   | succ i ih=>
     simp only [imageSet,shell]; split
     next hz=> exact constant_zero hd hh|>.funding (aside hv _) hh le_rfl
     next hz=>
      rw [show M p - _=M p+(-1:ℝ) • ∑ i'∈range (m+1), levy (i'+2) • bundle (imageSet M m i) (i'+2) p from (by simp [sub_eq_add_neg])];
      let Φ z:=levy (z+2)
      let f t (x:E):= Φ t *stack (shell m (F x) i) (t+2) p
      have hk t (ht':t∈range (m+1)) := (boundP hd hh hH (F:=fun x=> shell m (F x) i) ht ih (t+2) p).scale (Φ t)
      have hv t : ‖Φ t‖= Φ t := Real.norm_of_nonneg (by unfold Φ levy; positivity)
      simp_rw [hv] at hk
      have hx:=(Points.summing _ _ f _ hd hh hk).scale (-1)
      rw [norm_neg,norm_one,one_mul] at hx
      apply ((hp p hz).add hx).adjust; refine Eventually.of_forall (fun i'=>?_); simp only [f,Φ,Pi.add_apply, Finset.sum_apply]; ring
end YM.RGComparison01.Archival
