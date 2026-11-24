import YM.RGComparison01.AuxPlay

/-!
# Interior on the actual primary/gStep ball

Bound simultaneously true truncated integrals on a fixed analytic patch and
polynomial moments for the full cover jet candidate. Includes estimates for
unscaled analytic insertions. At this layer know nothing about masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.AuxFabric
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Lattice Wilson RG Pressure RG Gauge PhysicalNext.Repeat
open Input Precision Tree Push.AbsoluteSums
open ConnectedActivityE6 Blaze Brush Poll Shield WithLp Work.G05
open AuxJets AuxCurtain AuxStage WilsonStartup Tensor AuxConstant
open scoped Topology MatrixOrder ContDiff BigOperators Classical Interval ENNReal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {u v d D a h C : ℝ} {j k n w t t' q q' : ℕ}

section coord
variable {g f:ℝ×E→ℝ} {x:E}
-- Real rescaled polynomial, valence costs remove noncontributing Laurent terms
def ritual (f : ℝ×E→ℝ) (q : ℕ) : AuxStage.Co E := fun i x=> Tensor.diagonal (Tensor.coeff f (i+q) 0) (1,x)
lemma ritual_H (i:ℕ) (y:E) (he : 0 < h) : headAt (ritual f q) h i y = h⁻¹^q * Tensor.diagonal (Tensor.coeff f (i+q) 0) (h,y):= by
  unfold headAt ritual
  rw [show ((h,y):ℝ×E)= h•(1,h⁻¹ • y) from (by change (h,y)=(h*(1:ℝ),_); simp [he.ne']), Tensor.homogeneous,smul_eq_mul,pow_add]; rw [inv_pow]; field_simp
lemma ritual_A (H : FlatAt q f 0) (k : ℕ) (y:E) (he : 0<h) : price (ritual f q) h k y=h⁻¹^q* blockTaylor (k+q) f (h,y):= by
  unfold AuxStage.price blockTaylor; rw [Finset.sum_apply, Finset.mul_sum]
  let u(i:ℕ):= h⁻¹^q*Tensor.diagonal (Tensor.coeff f i 0) (h,y)
  have hx : ∑ i∈Finset.range q,u i=0:= Finset.sum_eq_zero (by
    intro i hi; unfold u Tensor.diagonal Tensor.coeff; rw [H i (Finset.mem_range.mp hi),smul_zero]; simp)
  change _ = ∑ i∈Finset.range (k+q+1),u i
  rw [show k+q+1=q+(k+1) by omega,Finset.sum_range_add u,hx, zero_add]
  refine Finset.sum_congr rfl fun i _=>?_ ; rw [ritual_H _ _ he]; simp only [u, add_comm q i]
def ritual_fee (q k : ℕ) (C U d : ℝ):= let n:=q+k+1; (n:ℝ)*(C+U)*d^n+(C*d^n+(n:ℝ)*U)
lemma ritual_P (hk : k+q < n) (hj : j ≤ n) (hf : ContDiffAt ℝ (↑(k+q :ℕ)) f 0) (H : FlatAt q f 0) (he : 0<h)
    (hv : 1 < d) (hh : d*h ≤ 1) (hx : ‖x‖ < d*h)
    (hp : ∀ y∈ball 0 (d*h), Brush n C 1 g y) (ht : Brush (k+q) (u*h^(k+q+1)) 1 (g-f) 0):
    AuxStage.Points (ritual_fee q k C u d) ((d*h)⁻¹) h k j (fun x:E=> h⁻¹^q * g (h,x)) x (ritual f q) := by
  let m:=q+k+1
  let r:=d*h; have hr:0<r:=mul_pos (zero_lt_one.trans hv) he
  have hw : (h,x)∈ ball 0 r := mem_ball_zero_iff.mpr (max_lt (by rw [Real.norm_of_nonneg he.le]; exact lt_mul_of_one_lt_left he hv) hx)
  have hs:= hp _ hw
  have hC:= hs.nonneg
  let p:= C*d^m+m*u
  let B:=m*(C+u)*d^m
  have hu : 0≤u:= (nonneg_of_mul_nonneg_left ht.nonneg (pow_pos he _))
  have hM : 0≤p:= by unfold p; positivity
  have hB:0≤B:=by unfold B; positivity
  let b:=u*h^(k+q+1)
  have hV : b ≤ u:= mul_le_of_le_one_right hu (pow_le_one₀ he.le (by linarith only [hh, (mem_ball_zero_iff.mp hw), norm_fst_le (h,x),Real.norm_of_nonneg he.le] : h ≤ 1))
  have hp₀ := hp 0 (mem_ball_self hr)
  have hz i (hi:i ≤ k+q): normJ i f 0 ≤ C+u:= by
    have hx:= ((hp₀.smaller (show k+q ≤ n from hk.le)).separating (ht.climb hV le_rfl)).shimmy (g:=f) (Eventually.of_forall fun i=> (sub_sub_self _ _).symm)
    exact (Brush.offer.1 hx).2 i hi
  constructor
  · intro i hi
    let j':= i+q
    have ha:j' ≤ k+q:=by omega
    have ht:=diag_brush (hf.of_le (Nat.cast_le.mpr ha)) (hz _ ha) hr hh (ha.trans_lt hk) hw
    rw [show headAt (ritual f q) h i=(fun x => h⁻¹^q * Tensor.diagonal (Tensor.coeff f j' 0) (h,x)) from funext (fun x=> ritual_H i x he)]
    refine ((on_arc ht|>.smaller hj).smul (h⁻¹^q)).climb ?_ le_rfl; rw [Real.norm_of_nonneg (by positivity)]
    change _ ≤ (B+p)*h^i; refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hM) (pow_pos he _|>.le))
    have hg: h⁻¹^q*((↑(j'+1):ℝ)*((C+u)*r^j'))=(↑(j'+1):ℝ)*(C+u)*d^j'*h^i:= by unfold r j'; rw [mul_pow,pow_add h]; rw [inv_pow]; field_simp
    refine hg.trans_le (mul_le_mul_of_nonneg_right ?_ (pow_pos he _|>.le)); exact mul_le_mul (mul_le_mul_of_nonneg_right (by apply Nat.cast_le.mpr; omega) (add_nonneg hC hu)) (pow_le_pow_right₀ hv.le (by omega)) (by positivity) (mul_nonneg (Nat.cast_nonneg _) (add_nonneg hC hu))
  have ht:= drifting hr hh hk hC ht.nonneg (fun x hx=> (hp x hx).smooth) (fun i _ hi y hy=>(Brush.offer.1 (hp y hy)).2 _ hi) hf ht _ hw
  have he' := (on_arc ht|>.smaller hj).smul (h⁻¹^q)
  refine (he'.climb ?_ le_rfl).shimmy (Eventually.of_forall (fun i=>?_) )
  · rw [Real.norm_of_nonneg (by positivity : 0 ≤ h⁻¹^q)]
    have hx: ↑(k+q+1:ℕ) * (u*h^(k+q+1))= (m:ℝ)*(u*h^m):= by rw [show m=k+q+1 by omega]
    change _≤(B+p)*h^(k+1); refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB) (pow_pos he (k+1)|>.le)); rw [hx]; unfold p r; rw [show k+q+1=m by omega, mul_pow, show h^m=h^q*h^(k+1) from (by rw [show m=q+(k+1) by omega,pow_add])]; rw [inv_pow]; field_simp
  change h⁻¹^q*g (h,i)- _=h⁻¹^q*(g _- _); rw [mul_sub]; rw [ritual_A H k i he]
end coord
variable {ι:Type} [Fintype ι] [DecidableEq ι]
local notation "Y" => Poll.Body ι
variable [FiniteDimensional ℝ E]
variable {f g : Poll.Body ι→E→ℝ} {Q : Matrix ι ι ℝ}
local notation "µ" => Poll.sweep Q
local notation "s" => closedBall (0:Y) D

structure Being (f : Poll.Body ι→E→ℝ) (k : ℕ) : Prop where
  outer (D : ℝ) (h : 0 ≤ D) : ∃ C:ℝ, ∀ᶠ y in 𝓝 (0:E), Measurable (truncate f D y) ∧
    ∀ z:Y, Brush k C 1 (fun x=>truncate f D x z) y
structure Purchase (f : Poll.Body ι→E→ℝ) (k : ℕ) (d D C v : ℝ) : Prop where
  positive : 0 ≤ v
  toll (x) (hx : x ∈ ball 0 d) : Measurable (truncate f D x) ∧ ∀ z:Y,
    Brush k v C (fun y=>truncate f D y z) x
-- permit distinct polynomial-growth budget
structure Probe (f : Poll.Body ι→E→ℝ) (k j q : ℕ) (d D C v : ℝ) : Prop extends Being f k where
  stencil : Purchase f k d D 1 C
  origin (z:Poll.Body ι) : Brush k (v*(1+‖z‖)^j) 1 (f z) 0
  null (z: Poll.Body ι) : FlatAt q (f z) 0
section cut
omit [FiniteDimensional ℝ E] [DecidableEq ι]
lemma Purchase.shrink (p : Purchase f k d D C v) (_hh : 0 ≤ u) (hv:u ≤ d) (hi : j ≤ k) : Purchase f j u D C v:= ⟨p.positive,fun i h=> ⟨(p.toll i (ball_subset_ball hv h)).1, fun z=> ((p.toll i (ball_subset_ball hv h)).2 z).smaller hi⟩⟩
omit [NormedSpace ℝ E] [NormedAddCommGroup E] in
lemma product (x:E) (f g : Y→E→ℝ) : truncate (f*g) D x =truncate f D x*truncate g D x := by
  ext z; by_cases H:z∈s <;> unfold truncate <;> simp only [Pi.mul_apply]
  · simp [H]
  simp [H]
lemma joint {x:E} {z : Poll.Body ι} {B : ℝ} (p : Brush k B C (fun y=> truncate f D y z) x) (h : Brush k v C (fun y=> truncate g D y z) x): Brush k (B*v*2^k) C (fun y=>truncate (f*g) D y z) x :=
    (together p h).shimmy (Eventually.of_forall fun i=>congr_fun (product i _ _) z)
lemma Purchase.productP {u : ℝ} (h : Purchase f k d D C v) (p : Purchase g k d D C u) : Purchase (f*g) k d D C (v*u*2^k) := by
  refine ⟨by have h:= h.positive; have hp:=p.positive; positivity,fun x hx=> ⟨by rw [product]; exact ((h.toll x hx).1).mul (p.toll x hx).1,fun z=> joint ((h.toll x hx).2 z) ((p.toll x hx).2 z)⟩⟩
lemma Being.productP (p : Being f k) (u : Being g k) : Being (f*g) k:= by
  constructor; intro r hr; obtain ⟨A,hA⟩:= p.outer r hr; obtain ⟨B,hB⟩:= u.outer r hr
  refine ⟨A*B*2^k,?_⟩; filter_upwards [hA,hB] with x hx hv
  exact ⟨by rw [product]; exact hx.1.mul hv.1, fun z=> joint (hx.2 z) (hv.2 z)⟩
lemma Probe.productP {q q' i j u' v'} (p : Probe f k i q d D u u') (h : Probe g k j q' d D v v') (hh : q+q' ≤ k+1) : Probe (f*g) k (i+j) (q+q') d D (u*v*2^k) (u'*v'*2^k):= by
  refine ⟨p.toBeing.productP h.toBeing,p.stencil.productP h.stencil,(fun z=> (together (p.origin z) (h.origin z)).climb ?_ le_rfl),fun z=>prod_fades (p.origin z).smooth (h.origin z).smooth (p.null z) (h.null z) hh⟩
  apply le_of_eq; rw [pow_add]; ring
lemma truncH {w:ℝ} (hq : 0≤C) (hw:|w|≤v) (hh : 0 ≤ v) (z:Y) (x:E) : Brush k v C (fun y=>truncate (fun _ _=>w) D y z) x := by
  by_cases he:z∈s
  · exact (constant (p:=v) (u:=w) (k:=k) hq hw).shimmy (Eventually.of_forall fun _=>indicator_of_mem he _)
  exact (constant (p:=v) (u:=0) (k:=k) hq (by simpa using hh)).shimmy (Eventually.of_forall fun _=> indicator_of_notMem he _)
lemma Purchase.scalar (x:ℝ) (hh : 0≤C) : Purchase (ι:=ι) (E:=E) (fun _ _=>x) k d D C ‖x‖:= by
  refine ⟨norm_nonneg _,fun _ _=> ⟨Measurable.indicator measurable_const measurableSet_closedBall, fun z=> truncH hh (le_refl _) (norm_nonneg x) z _⟩⟩
lemma Being.scalar (x:ℝ) : Being (ι:=ι) (E:=E) (fun _ _=>x) k:= by
  constructor; intro D h; refine ⟨_,Eventually.of_forall (fun y=> both x D y)⟩
where
  both x' (D' : ℝ) (y:E) : Measurable (truncate (ι:=ι) (fun _ _=>x') D' y) ∧ ∀ z:Y, Brush k ‖x'‖ 1 (fun y=> truncate (fun _ _=>x') D' y z) y :=
    Purchase.scalar (E:=E) x' zero_le_one |>.toll y (show y∈ ball (0:E) (‖y‖+1) from mem_ball_zero_iff.mpr (lt_add_one _))
lemma Probe.unit : Probe (ι:=ι) (E:=E) 1 k 0 0 d D 1 1 := by
  refine ⟨Being.scalar _,?_,?_,fun z i hi=>(Nat.not_lt_zero _ hi).elim⟩
  · simpa only [norm_one] using! Purchase.scalar (ι:=ι) (E:=E) (d:=d) (k:=k) (D:=D) 1 zero_le_one
  intro z; simpa only [pow_zero,norm_one,one_mul] using! Brush.certified (x:=(0:E)) (k:=k) zero_le_one (1:ℝ)
lemma Probe.trivial : Probe (ι:=ι) (E:=E) 0 k j q d D 0 0 := by
  refine ⟨Being.scalar _,?_,?_, fun z i hi=>by simp⟩
  · simpa only [norm_zero] using! Purchase.scalar (ι:=ι) (E:=E) (d:=d) (k:=k) (D:=D) 0 zero_le_one
  intro z; simpa only [norm_zero,zero_mul] using! Brush.certified (x:=(0:E)) (k:=k) zero_le_one (0:ℝ)
lemma Probe.powP {i:ℕ} (p : Probe f k j q d D C v) (hh : q*i ≤ k+1) : Probe (f^i) k (j*i) (q*i) d D ((C*2^k)^i) ((v*2^k)^i):= by
  induction i with
  | zero=> rw [mul_zero,mul_zero,pow_zero,pow_zero,pow_zero]; exact unit
  | succ i ih=>
    rw [Nat.mul_succ] at hh
    simpa only [Nat.mul_succ,pow_succ,mul_assoc] using! (ih (by omega)).productP p hh
end cut

section integral
lemma Being.buys (p : Being f k) (hr : 0≤D) : Meristem (truncate f D) 0 µ k:= by
  obtain ⟨v,hv⟩:= p.outer D hr
  exact (Meristem.points _ µ ⟨fun _=> v,integrable_const _,hv.mono fun i hi=> hi.2⟩ (hv.mono fun i hi=> hi.1)).1
variable (p : Purchase f k d D C v)
include p
abbrev intake (Q : Matrix ι ι ℝ) (f:Y→E→ℝ) (D:ℝ) (x:E):=∫ z, truncate f D x z ∂Poll.sweep Q
lemma at_center (Q : Matrix ι ι ℝ) (x:E) (hx:x∈ball 0 d) :
    Integrable (truncate f D x) (Poll.sweep Q) ∧ Brush k v C (intake Q f D) x:= by
  have ht:=p.toll x hx; obtain ⟨he,hv⟩ := Meristem.points (truncate f D) (Poll.sweep Q) (x:=x) ⟨fun _=>v*(1+C)^k,integrable_const _, Eventually.mono (isOpen_ball.mem_nhds hx)  (fun y hy z=> ((p.toll y hy).2 z).trim)⟩ (Eventually.mono (isOpen_ball.mem_nhds hx)  (fun y hy=> (p.toll _ hy).1))
  exact ⟨hv.self_of_nhds,he.buds (fun _=>v) (integrable_const _) (ht.2 0|>.pos) (by simp) (ae_of_all _ ht.2)⟩
end integral
end YM.RGComparison01.AuxFabric
