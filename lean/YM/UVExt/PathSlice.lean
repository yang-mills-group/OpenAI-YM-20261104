import YM.UVExt.PoolAlign
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.TurnZero

set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open RG Function Filter Real Wilson Precision Lattice Bid Exterior Set Matrix Laurent Bloch
open Work.F08
open Next.Free.UV
open scoped BigOperators Classical Topology ContDiff

structure Shadow (G : Gauge) where
  row : PlaqAxes → Slot→ℝ
  cubic : Token G 3→ℝ
  quartic : Token G 4→ℝ
  loop : Token G 2→ℝ

variable {G : Gauge} {n : Side} (Z : Shadow G)

def wick (W : PathData G) : Shadow G := ⟨ink W,necklace W.cubic,necklace W.quartic,necklace W.loop⟩

def score (b : PlaqAxes) : Slot×Slot →ℝ := fun i=> Z.row b i.1* Z.row b i.2
def ringLit (v : Dir G n) (p : Clip) (b : Face (Per n)) :=
    (p.direct) • (fun t : ℝ=>G.price (faceValue (represent (t • v)) b))

def facet (N : Bool) (v : Dir G n) (p : Clip) :=
    ∑ x : Face (Per n), (ringLit v p x + ((1/2):ℝ) • (liftAir v N x.1 (fun i=> score Z x.2 i.1)))

def qulit (N : Bool) (v : Dir G n) (p : Clip) := ((Fintype.card Signed:ℝ)⁻¹) • ∑ s : Signed, facet Z N (pulled v s) p

def bench (v : Dir G n) (p : Clip) := ((Fintype.card Signed:ℝ)⁻¹) • ∑ s : Signed, (
      (∑ x : Face (Per n), (ringLit (pulled v s) p x + (1/2:ℝ) • words (pulled v s) x.1 (fun i => score Z x.2 i.1))))

def payload (v : Dir G n) (p : Clip) := ((Fintype.card Signed:ℝ)⁻¹) • ∑ s : Signed, (
     (∑ x : Face (Per n), (ringLit (pulled v s) p x + (1/2:ℝ) • words (pulled v s) x.1 (fun i => score Z x.2 i.1))) +
       (∑ x, song (pulled v s) x Z.cubic) + (∑ x, song (pulled v s) x Z.quartic))

def spiral (v : Dir G n) := ((Fintype.card Signed:ℝ)⁻¹) • ∑ s : Signed, ∑ x, song (pulled v s) x Z.loop

structure PaidShadow (T : Shadow G) (C Λ σ : ℝ) : Prop where
  row (b) : Carries C σ SlotSize (T.row b)
  coeffThree : Carries C σ breath T.cubic
  coeffFour : Carries C σ breath T.quartic
  coeffTwo : Carries Λ σ breath T.loop

variable {p : Clip} {C A Λ σ : ℝ}
lemma shadow_pay (R : PathData G) (h : R.Bounds p σ C Λ) : PaidShadow (wick R) C Λ σ :=
  ⟨row_money h, necklaces_paid _ _ _ h.three h.width, necklaces_paid _ _ _ h.four h.width,necklaces_paid _ _ _ h.two h.width⟩ -- fix ..
lemma pay_nonneg (h : PaidShadow Z C Λ σ) : 0≤C ∧ 0≤Λ :=
  ⟨(h.coeffThree.2 ∅).trans' (by simp), (h.coeffTwo.2 ∅).trans' (by simp)⟩
lemma paid_chord (h : PaidShadow Z C Λ σ) (b) : Weighted ((Fintype.card G.ColorIndex:ℝ) * C^2) σ (fun (i:Chord G)=> score Z b i.1) := by
  let W := score Z b
  let L (t : Slot×Slot) := breath' t.1 t.2
  have hs : Carries (C^2) σ (L) W := by
    rw [pow_two]
    exact squared_money (a:=Z.row b) (b:=Z.row b) (h.row b) (h.row b) (pay_nonneg _ h).1
  change Carries _ σ (fun i=>breath (parallel i)) (fun i=> W i.1)
  simp_rw [parallel_breath]
  exact product_money (R:=fun j _ => W j) L hs.1 (fun t=>(Fintype.card G.ColorIndex:ℝ) * ‖W t‖) (fun i=>by simp) (by
     simp_rw [mul_right_comm (Fintype.card _:ℝ),mul_assoc (Fintype.card _:ℝ)]; refine ⟨fun _=>by positivity,hs.paid.2.1.mul_left _,?_⟩
     rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hs.paid.2.2 (Nat.cast_nonneg _))

lemma bench_raw (R : PathData G) (v : Dir G n) (h : R.Bounds p σ C Λ): bench (wick R) v p = fun t=> secondTerm p R (represent (t • v)) := by
  funext t
  unfold bench secondTerm Patch.average
  rw [Pi.smul_apply,smul_eq_mul,Finset.sum_apply]; refine congr_arg ((Fintype.card Signed:ℝ)⁻¹*·) (Finset.sum_congr rfl fun s _=> ?_)
  dsimp only []; rw [Work.F03.represent_pulled]; unfold quadratic; rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun b _=> ?_
  rw [ringLit,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.smul_apply,smul_eq_mul]; congr 1
  rw [row_word (C:=C) _ _ _ _ h]; change (1/2:ℝ) * words (pulled v s) b.1 (note R b.2) t = _; rw [one_div,mul_comm]; rfl

set_option maxHeartbeats 120000 in
lemma payload_main (R : PathData G) (v : Dir G n) (h : R.Bounds p σ C Λ): payload (wick R) v p = fun t => mainTerm p R (represent (t • v)) := by
  funext t
  unfold payload mainTerm Patch.average
  rw [Pi.smul_apply,smul_eq_mul,Finset.sum_apply]; refine congr_arg ((Fintype.card Signed:ℝ)⁻¹*·) (Finset.sum_congr rfl fun s _=> ?_)
  simp only [Pi.add_apply, Finset.sum_apply, Work.F03.represent_pulled]
  unfold quadratic; congr 1; congr 1
  · refine Finset.sum_congr rfl fun b _=> ?_
    simp only [ringLit,Pi.smul_apply,smul_eq_mul]; congr 1
    rw [row_word (C:=C) _ _ _ _ h]; change (1/2:ℝ) * words (pulled v s) b.1 (note R b.2) t = _; rw [one_div,mul_comm]; rfl
  all_goals exact Finset.sum_congr rfl fun z _=>neck_song (C:=C) (pulled v s) (by first|exact h.three|exact h.four) h.width z t

lemma spiral_loop (R : PathData G) (v : Dir G n) (h : R.Bounds p σ C Λ) : spiral (wick R) v=fun t=> Precision.loop R (represent (t • v)) := by
  funext t; unfold spiral Precision.loop Patch.average
  rw [Pi.smul_apply,smul_eq_mul,Finset.sum_apply]; refine congr_arg ((Fintype.card Signed:ℝ)⁻¹*·) (Finset.sum_congr rfl fun s _=>?_)
  dsimp only []; rw [Work.F03.represent_pulled,Finset.sum_apply]; unfold uncut; exact Finset.sum_congr rfl fun z _=>neck_song (pulled v s) h.two h.width z t

-- sum across all sites BEFORE dropping the common base patch; finite period okay
lemma rotated_bench (h : PaidShadow Z C Λ σ) (he : 0 < σ) (v : Dir G n) : bench Z v p = qulit Z true v p := by
  unfold qulit bench facet
  apply congr_arg ((Fintype.card Signed:ℝ)⁻¹ • ·)
  refine Finset.sum_congr rfl fun s _=>?_
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.smul_sum,←Finset.smul_sum]
  refine congr_arg₂ _ rfl (congr_arg ((1/2:ℝ) • ·) ?_)
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm (f:=fun i:Site n => fun j:PlaqAxes=> words _ i _),Finset.sum_comm (f:=fun i:Site n => fun j:PlaqAxes=> liftAir _ _ i _)]
  exact Finset.sum_congr rfl fun b _ => words_trans _ he (paid_chord Z h b) -- b swap order

attribute [local instance] Gauge.frobInner
open scoped Matrix.Norms.Frobenius in
lemma lit_flow (p : Clip) (v : Dir G n) (x) : ContDiff ℝ ω (ringLit v p x) := by
  change ContDiff ℝ ω (p.direct • _)
  suffices h : ContDiff ℝ ω (fun t:ℝ => G.price (faceValue (represent (t • v)) x)) by exact ContDiff.const_smul p.direct h
  let z := fun t : ℝ=> faceValue (represent (t • v)) x
  change ContDiff ℝ ω (fun t=>G.price (z t))
  rw [show (fun t : ℝ=> G.price (z t)) = fun t=> ‖G.mat (z t) - 1‖^2 / G.colorScale^2/2 from
       funext fun _=> by rw [← div_pow]; change _ = G.chord _ ^2/2; rw [G.chord_price]; ring]
  change ContDiff ℝ ω (fun t=>‖curve v (square _ _) x.1 t-1‖^2 /G.colorScale^2/2)
  exact ((contDiff_norm_sq ℝ).comp ((curve_smooth v _ _).sub contDiff_const) |>.div_const _).div_const _

lemma flow_sum {ι : Type*} [Fintype ι] {r : ℕ∞ω} {f : ι→ℝ→ℝ} (h : ∀ i,ContDiff ℝ r (f i)) : ContDiff ℝ r (∑ i,f i) := by convert (ContDiff.sum (fun i (_hi : i∈Finset.univ)=>h i)) using 1; ext1; simp

lemma payload_smooth (h : PaidShadow Z C Λ σ) (he : 0<σ) (v : Dir G n) : ContDiff ℝ ∞ (payload Z v p) := by
  unfold payload
  exact ContDiff.const_smul ((Fintype.card Signed:ℝ)⁻¹) (flow_sum (ι:=Signed) fun s => ((flow_sum fun x : Face (Per n)=> ((lit_flow _ _ _).of_le le_top).add (ContDiff.const_smul (1/2:ℝ) (words_flow _ x.1 (paid_chord Z h x.2) he))).add (flow_sum (ι:=Site n) fun x=>song_smooth _ h.coeffThree he x)).add (flow_sum (ι:=Site n) fun x=>song_smooth _ h.coeffFour he x))
lemma bench_smooth (h : PaidShadow Z C Λ σ) (he : 0<σ) (v : Dir G n) : ContDiff ℝ ∞ (bench Z v p) := by
  unfold bench
  exact ContDiff.const_smul ((Fintype.card Signed:ℝ)⁻¹) (flow_sum (ι:=Signed) fun s => flow_sum fun x : Face (Per n)=> ((lit_flow _ _ _).of_le le_top).add (ContDiff.const_smul (1/2:ℝ) (words_flow _ x.1 (paid_chord Z h x.2) he)))
lemma spiral_smooth (h : PaidShadow Z C Λ σ) (he : 0<σ) (v : Dir G n) : ContDiff ℝ ∞ (spiral Z v) := by
  unfold spiral
  exact ContDiff.const_smul ((Fintype.card Signed:ℝ)⁻¹) (flow_sum (ι:=Signed) fun s => flow_sum (ι:=Site n) fun x=>song_smooth _ h.coeffTwo he x)

private lemma map_spin (s : Signed) (z : Cover) (w : Walk) : stop (affine s 0 z) (w.map (·.rotate s)) = affine s 0 (stop z w) := by
  induction w generalizing z with
  | nil => rfl
  | cons h w ih => exact Eq.trans (congr_arg (stop · (w.map _)) <| show affine s 0 z+(h.rotate s).vec=affine s 0 (z+h.vec) by rw [Step.vec_rotate]; unfold affine; rw [s.act_add]; simp) (ih (z+h.vec))

open scoped Matrix.Norms.Frobenius in
lemma rotate_links (z : Site n) (s : Signed) (w : Walk) (v : Dir G n) :
    linkSum (collect G (pulled v s)) z w=linkSum (collect G v) (affine s 0 z) (w.map (·.rotate s)) := by
  apply G.colorMat_injective
  have ht : curve (pulled v s) w z=curve v (w.map (·.rotate s)) (affine s 0 z) := funext fun t=>by unfold curve; rw [← Work.F03.represent_pulled, travel_pull]
  exact (Push.travell _ z (pulled v s)).deriv.symm.trans <| (congr_arg (deriv · 0) ht).trans (Push.travell _ _ v).deriv

lemma paid_curl (v : Dir G n) (s : Signed) : ‖pulled v s‖ ≤ ‖v‖ ∧ ‖dColor G n 1 (pulled v s)‖ ≤ 16*‖dColor G n 1 v‖ := by
  refine ⟨AnalyticBridge.LocalGaussianLaws.Lift.swapped ..,(pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_⟩
  rcases i with ⟨z,i⟩; obtain ⟨a,rfl⟩ := plaqEquiv.surjective i; rw [plaq_map,←fundamental,rotate_links]
  exact (show _ from (basket_bound v _ _ (by simpa [affine] using map_spin (w:=square a.val.1 a.val.2) s 0) |>.trans_eq (by norm_num [square])))

end YM.UVExt.Paths
