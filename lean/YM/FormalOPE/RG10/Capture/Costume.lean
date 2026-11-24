import YM.FormalOPE.RG10.Capture.Shelf

/-!
# Structural gates at any one finite capture epoch

Field lift and emitted kernel compatibility pointwise in each required test φ (not just this
far observation useful for prices). The owner constructs the literal `K b` called `M` from
those pre-residual resources; equality & documentation witnessing `pov` really is the intended lifts are required to legitimize it, never claiming equality of
newly chosen representatives in a different subspace or multiple windings. State terminal
observation theorem only through these.

`Cluster` internal profile pairwise distances, `A` is the *macro interior* support including any
translated inner shapes at which φ is seen. `t` is far scale, choose nearest repeated-step scale
before any use. Can center simultaneously in Euclidean or periodic true positions when those
Tile hypotheses are met. Using support sets estimated by powers of `C`, e.g. in Occupancy, no
postulate factor inherently bounded volume. Use `C ≤ 2+some polynomial in
log(μ_t/μ_b)` and h cap parameters to see this as a log-budgeted assertion. No choice law on
actual group markers used to price these pre-regulator calculations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Capture
open PowerSeries Function Finset MeasureTheory Filter Route Transit Cylinder Weave
open scoped Topology BigOperators Classical
variable {X : Type} [MeasurableSpace X] {U T J : ℕ → Type} {K:ℕ→Type*} {ι α β I I': Type*}
    [∀ i,AddCommGroup (K i)] [∀ i,Module Series (K i)]
    [∀ i,Fintype (T i)] [∀ i,Fintype (U i)] [∀ i,Fintype (J i)] [Fintype ι] [∀ i,DecidableEq (U i)]
    {V : Voyage U J} {W : Scale X U} {S : Locale T X α β} {Z : Cylinder T U K α ι}
    {b i k m t N r d d₁ n n₁ s δ : ℕ} {L : Cover W S b} {Y : X→ Lens W.tape}
    {J₀ : Fibers T} {F : ∀ i, Subalgebra ℂ (Channel (U i))}
    {A E O : Lens W.tape} {v:Finset I} {P : I→ Channel (U N)} {g : I → X → ℂ}
    {w:Finset I'} {D h j:I'→ℕ} {P' : X → I' → Channel (U N)} {A' : X → I' → Lens W.tape}
    {M : K b} {pov : Submodule Series (K b)} {φ : α}
    {C ξ:ℝ}

open Film
structure Install (W : Scale X U) (S : Locale T X α β) (J₀ : Fibers T) (V : Voyage U J) (Z : Cylinder T U K α ι)
    (F : ∀ i, Subalgebra ℂ (Channel (U i))) (b k t s N r d d₁ n n₁ δ m : ℕ) (L : Cover W S b) (M : K b) (pov : Submodule Series (K b)) (φ : α)
    (C ξ : ℝ) (Y : X → Lens W.tape) (v : Finset I) (P : I → Channel (U N)) (g : I→X→ℂ)
    (w : Finset I') (D h j : I'→ℕ) (P' : X → I'→Channel (U N)) (A' : X → I'→Lens W.tape) (A O : Lens W.tape) : Prop where
  cluster : Cluster V W S b N L P g v F Y w D j h P' A' r d n₁ δ C
  regular : Regular V W (W.μ t) C δ t N r d n (fun i=> (F i).toSubring) O
  reading : Reading J₀ V W m s N Z
  -- previous `Tariff` adapter is `Tariff.lends`
  loan : Loan W Z S b s t N r n₁ C ξ δ pov M (C^toBook r d n₁ δ (∑i∈w, j i) (∑i∈w, h i))
  printed : Z.prints b M=blue V W S b N L P g v
  admitted : M∈pov
  order : t ≤ b ∧ s ≤ t ∧ b ≤ k ∧ k ≤ N
  health : maximumNeeded n r d≤ n₁ ∧ (∑ i∈w,h i)+2 ≤ n₁ ∧ (r:ℝ)+1 ≤ C
  growth : ξ ≤ 1
  promised : 0 < ξ
  rank : ∑ i∈w,D i ≤ d₁
  test : Integrable (S.test φ) L.volume
  volume : (∫ x, ‖S.test φ x‖ ∂ L.volume) ≤ C
  scope : ∀ᵐ x∂ L.volume,S.test φ x≠0 → A.m ≤ (Y x).m
  occasion : ∀ i∈ Icc t N, Occupancy W S t C i A φ
  laneTrace : ∀ v:ι→Series,Guard (coupon W m Z φ k N v) r d₁
  laneWard : ∀ v:ι→Series,coupon W m Z φ k N v ∈ F N

namespace Install
variable (Q : Install W S J₀ V Z F b k t s N r d d₁ n n₁ δ m L M pov φ C ξ Y v P g w D h j P' A' A O)

local notation "η" => ∑ x∈w,h x
local notation "τ" => ∑ x∈w,j x
local notation "χ" => report W m Z M s k
local notation "λ₀" => designated Z M s
local notation "T₁" => toBook r d n₁ δ τ η
local notation "R" => W.μ t
local notation "B" => W.μ b
local notation "A₀" => W.Y C (W.μ t)
local notation "Q₁" => smear W S b N L P g v φ
local notation "Q₂" => coupon W m Z φ k N χ
local notation "L₁" => maximumNeeded n r d
include Q

lemma heavy : V.yield b N Q₁ = restore W m Z φ b b M := by
  obtain ⟨h1,h2,h3,h4⟩:=Q.order; rw [issue V (h3.trans h4) Q.cluster.ready m φ,← Q.printed]; rfl
lemma gather (hi:i∈Icc t b) : V.yield i N (Q₁-Q₂)= restore W m Z φ b i (Z.spin i b (M-Z.column b λ₀)) := by
  obtain ⟨h1,h2,h3,h4⟩:=Q.order; obtain ⟨ho,ht⟩:=mem_Icc.mp hi; exact Q.reading.residual φ (h2.trans h1) h3 h4 M _ Q.heavy (h2.trans ho) ht
lemma stamps : Fits W S b (Z.prints b M) n₁ r (C^T₁) := by
  obtain ⟨h1,h2,h3,h4⟩:=Q.order; rw [Q.printed]; exact booking Q.cluster (h3.trans h4) Q.health.2.1

def quiver (K j : ℕ) := j+j+1+K
lemma home : scaleC r λ₀ ≤ (A₀ b)^(quiver T₁ δ) := by
  have hx:=Q.stamps; have hr:=Q.cluster.ok; obtain ⟨h1,h2,h3,h4⟩:=Q.order
  have h := Q.regular.toHours; have he := h.zees h1; have h0:=h.paid h1
  have hC : 0≤C:=by linarith
  unfold quiver; rw [pow_add (m:=δ+δ+1)]; exact (Q.loan.extent Q.admitted (by positivity) hx).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hC he _) (by positivity))
lemma rank_signed : Guard (Q₁-Q₂) r d₁ := (Guard.mono Q.cluster.guard Q.rank).sub (Q.laneTrace _)
lemma identity : (Q₁-Q₂)∈ (F N).toSubring := (F N).sub_mem Q.cluster.belongs (Q.laneWard _)

-- same exponent budget across all uses; no issue with demanding higher internal field horizons
-- for squeezing

def creator (u δ p : ℕ) := (2*u+3)+(δ+quiver p δ)

-- Lemma with ζ requirement for use, not implying invariance on stereographic translated torus
lemma closedCost (hi : i∈ Icc t b) : W.value i L₁ r A (V.yield i N (Q₁-Q₂)) ≤
     (A₀ b)^creator n₁ δ T₁ * W.fade (m+ξ) b i := by
  obtain ⟨h1,h2,h3,h4⟩:=Q.order
  have h := Q.regular.toHours; have h' := h.richAt h1
  have hC:0≤C:=by linarith [h.rich]
  have hx : 0≤ A₀ b:=h.paid h1
  rw [Q.gather hi]; apply (W.sooner i A L₁ r _ _ Q.health.1).trans
  have α0 := Q.loan.terminal Q.admitted (by positivity : 0 ≤ C^T₁) Q.stamps _ hi
  have hε : 0≤W.fade ξ b i:=W.fade_nn; let ω₀:= (A₀ b)^δ*C^T₁*W.fade ξ b i; have hw : 0≤ω₀:= by unfold ω₀; positivity -- shadows w not good
  apply (restored W S φ A _ h.rich Q.health.2.2 α0 (Q.occasion i (Icc_subset_Icc le_rfl (h3.trans h4) hi)) hw).trans
  let B₁:= B/W.μ i; have hz:= h.R_pos; have ht:=W.positive i; have hg:=W.positive b; have hZ:0≤ B₁:= div_nonneg hg.le ht.le
  have hl: W.fade (m+ξ) b i=B₁^m*W.fade ξ b i:= by
    rw [Scale.fade_rpow,Scale.fade_rpow,Real.rpow_add, Real.rpow_natCast];
    positivity
  have hu : 1≤ A₀ b:= by linarith
  rw [hl]; unfold creator; erw [pow_add (A₀ b) (2*n₁+3),pow_add (A₀ b) δ];
  have hp:= pow_le_pow_left₀ hC (h.zees h1) (2*n₁+3)
  have he:= (pow_le_pow_left₀ hC (h.zees h1) T₁).trans (pow_le_pow_right₀ hu (show T₁ ≤ quiver T₁ δ by unfold quiver; omega))
  apply le_trans (mul_le_mul (mul_le_mul_of_nonneg_left hp (show 0≤ (B/W.μ i)^m by positivity)) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) hε) hw (by positivity)); apply Eq.le; unfold B₁; ring -- inspect

lemma coupons (hi : i∈Icc b N) : W.value i L₁ r A (V.yield i N Q₂) ≤ tally W C R i (creator n₁ δ T₁) m := by
  obtain ⟨h1,h2,h3,h4⟩:=Q.order; obtain ⟨ht,hk⟩:= mem_Icc.mp hi
  rw [shiny M φ (h2.trans h1) h3 h4,coupon,Q.reading.smearing φ b (h2.trans (h1.trans ht)) hk le_rfl,Q.reading.transaction (h2.trans (h1.trans ht)) hk le_rfl]
  rw [show Z.roll i N ((Z.roll b N).symm λ₀)=(Z.roll b i).symm λ₀ from ?_]; swap
  · apply (Z.roll b i).injective; rw [← Z.rollNow ht hk,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  apply (W.sooner i A _ r _ _ Q.health.1).trans
  have H := Q.regular.toHours; have ha:= H.paid (h1.trans ht); have hb:=H.paid h1; have hz : 0≤C:=by linarith [H.rich]
  have hT:=W.positive i; have hw:=W.positive b
  apply (restored W S φ A _ H.rich Q.health.2.2 (Q.loan.seed λ₀ i hi) (Q.occasion i (mem_Icc.mpr ⟨h1.trans ht,hk⟩)) (mul_nonneg (by positivity) (scaleC_nn ..))).trans
  unfold tally creator; exact calc
    _ ≤ (R/W.μ i)^m * (A₀ i)^(2*n₁+3)*((A₀ i)^δ*((A₀ i)^(quiver T₁ δ))) := by
      have hx:=W.positive t
      have hu:= scaleC_nn r λ₀
      gcongr
      · exact W.decrease h1
      · exact H.zees (h1.trans ht)
      exact Q.home.trans (pow_le_pow_left₀ hb (W.sees R C H.base ht) _)
    _ = _ := by simp only [pow_add]; ring
-- normalize powers with a single demand p

def fixedCost (tt K n δ root : ℕ) := max (K+1) (creator n δ (tt+K+root)) -- unused
private def nearPow (r d n δ Q t : ℕ) := max Q (Weave.debited r d n δ Q t)+1
-- `u` cost bound uniform independent placement

def arity (r d n δ Q t : ℕ) := let K:= nearPow r d n δ Q t; max (K+1) (creator n δ (toBook r d n δ Q t))+1

lemma hotter (hi : i∈Icc b N) :
    W.value i L₁ r A (V.yield i N (Q₁-Q₂)) ≤ tally W C R i (arity r d n₁ δ τ η) (max η m) := by
  have hn := younger Q.cluster Q.health.2.1 A Q.scope Q.test Q.volume hi
  obtain ⟨h1,h2,h3,h4⟩:=Q.order; have ht := mem_Icc.mp hi; let B₁:= nearPow r d n₁ δ τ η
  let S:=creator n₁ δ T₁; let L':= max (B₁+1) S
  let Y:=A₀ i; let X:= (R/W.μ i); have H:=Q.regular.toHours
  have hc : 1≤C:= le_trans (by norm_num) H.rich
  have hz : 2≤Y:= H.richAt (h1.trans ht.1)
  have hg : 0<C:=by linarith
  have hW:= W.positive i; have hh:= W.positive b; have hu : 1≤X:= H.near1 (h1.trans ht.1); have h'' : Y=A₀ i:=rfl
  have hr : W.Y C B i≤ Y:= add_le_add (le_refl C) (Real.log_le_log (div_pos hh hW) (div_le_div_of_nonneg_right (W.decrease h1) hW.le))
  have hY' : 0≤ W.Y C B i:= by apply le_trans (b:=2) (by norm_num); exact W.rich B C (le_refl B) H.rich ht.1
  have hY : 1≤Y:=by linarith
  let K:=Y^L' * X^ (max η m); have hK : 0 ≤ K:= by unfold K; positivity
  rw [map_sub]; apply le_trans (b:=K+K) (le_trans (mag_sub (W.eyes i A) L₁ r (W.alive i A) _ _) (add_le_add ?_ ?_)) ?_;
  · -- inspect
    apply ((W.sooner i A L₁ r _ n₁ Q.health.1).trans hn).trans -- reorder
 
    unfold tally at *
    apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_left₀ hY' hr B₁) (le_trans (pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right (W.decrease h1) hW.le) η) (pow_le_pow_right₀ hu (le_max_left ..))) (by positivity) (by positivity)) hg.le)
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right (H.zees (h1.trans ht.1)) (show 0≤Y^B₁ by positivity)).trans ((by simpa [pow_succ'] using (pow_le_pow_right₀ hY (show B₁+1 ≤ L' from le_max_left ..)) : Y*Y^B₁≤ Y^L'))) (by positivity)
  · apply (Q.coupons hi).trans; exact mul_le_mul (pow_le_pow_right₀ hY (le_max_right ..)) (pow_le_pow_right₀ hu (le_max_right ..)) (show 0 ≤ X^m by positivity) (by positivity)
  change K+K ≤ Y^(L'+1)*X^ (max η m)
  rw [pow_succ']; exact le_trans (by linarith : K+K ≤ 2*K) (le_trans (mul_le_mul_of_nonneg_right hz hK) (by rw [mul_assoc]))
end Install
end YM.FormalOPE.RG10.Capture
