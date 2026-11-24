import YM.FormalOPE.RG10.Capture.Cohere

/-!
# Capture at one chosen finite approximant of the same direction

Cell-centered estimate and macro envelope estimate from the earlier fine history, not from a
postulated bound on the projected answer. Γ-test *at macro center* of the replacement and of the
original product; no use of package `Final`/`Reader`. `Film` depends only on cluster and its stated
inner shapes (incl all test derivatives), a finite top expression on that lattice; define the
printed capture at every test φ charging its integrability. The support hypotheses are at the
correct scale for each application: in particular the far A site budget can include the whole
circle of possible interior locations where macro φ is tested, while the statement when
proving b-cell budget applies in b's native units. No analysis of infinite-volume rank-stencil
transport is provided by this adaptor.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Capture
open PowerSeries Function Finset MeasureTheory Filter Route Transit
open Weave
open scoped Topology BigOperators Classical
variable {X : Type} [MeasurableSpace X] {T U J : ℕ→ Type} {α β I I': Type*}
    [∀ i,Fintype (T i)] [∀ i,Fintype (J i)]

namespace Film
variable (V : Voyage U J) (W : Scale X U) (S : Locale T X α β)
    (b N : ℕ) (L : Cover W S b) (P : I→Channel (U N)) (g : I→ X→ℂ) (v:Finset I) (φ:α)

/-- Absolute smear using true address-zero macro test (if using derivative kernel bring with it
`Locale.test`). Choose its input f_i(·) in `P` coherently with the representation in
`Capture.Wheel`. At this fixed-regulator every genuine pre-capture product at a continuously
translated center is assumed presented in finite rank via its tested top profiles. This produces
ONE sector kernel, preserving all its other marks in actual calculation. -/
def smear := smeared L.volume v P (Cover.versions (S:=S) g φ)

def lands (i : ℕ) := fun j=> V.yield i N (P j)

def blue := L.material v (lands V N P b) g

variable {V W S b N L P g v φ}
variable (h : Cover.Legible L v g)
lemma smears (V : Voyage U J) {i : ℕ} (hi:i≤N) : V.yield i N (smear W S b N L P g v φ)= smeared L.volume v (lands V N P i) (Cover.versions (S:=S) g φ) := by
  unfold smear lands smeared; rw [map_sum]; exact sum_congr rfl fun j _ => V.currency hi _ (P j)
lemma issue (V : Voyage U J) (h: b ≤ N) (h':Cover.Legible L v g) (r) (φ):
    V.yield b N (smear W S b N L P g v φ) = fingerprint φ W r b b (blue V W S b N L P g v) := (smears V h).trans (Cover.stamp_eq L v (lands V N P b) g h' r φ).symm -- inspect
omit [MeasurableSpace X] [∀ i,Fintype (T i)] in
lemma collects {i : ℕ} (hi:i≤N) (x : X) : collection v (lands V N P i) g x = V.yield i N (collection v P g x) := by
  unfold collection lands; rw [map_sum]; exact sum_congr rfl fun j _ => (V.currency hi _ (P j)).symm

variable (F : ∀ i, Subalgebra ℂ (Channel (U i))) [∀ i,Fintype (U i)] [∀ i,DecidableEq (U i)]
    (Y : X → Lens W.tape) (w : Finset I') (D t H : I'→ℕ) (P' : X→ I'→ Channel (U N)) (A': X→I' → Lens W.tape) (r d n δ : ℕ) (C:ℝ)

-- organic Oil supplies through all needed centers. If wanted cofinal sets, provide a.e. versions via a patch
structure Cluster (V : Voyage U J) (W : Scale X U) (S : Locale T X α β) (b N : ℕ) (L : Cover W S b)
    (P : I→Channel (U N)) (g : I→ X→ℂ) (v:Finset I) (F : ∀ i, Subalgebra ℂ (Channel (U i)))
    (Y : X→ Lens W.tape) (w : Finset I') (D t H : I'→ ℕ) (P' : X→I'→ Channel (U N)) (A': X→I' → Lens W.tape) (r d n δ : ℕ) (C:ℝ) : Prop where
  ready : Cover.Legible L v g
  ok : 2 ≤ C
  mark x : collection v P g x=∏ j∈w,P' x j -- independent of cutoff; define by this each input
  cap x : Contracts V W (fun i => (F i).toSubring) b N r d n (W.μ b) C δ w (P' x) (Y x) (A' x) D t H
  cellLens (z:T b) x (hx : x∈S.park b z) y : (W.tape.sphere (S.point b z) 0).m y ≤ C^δ*W.μ b+(Y x).m y
variable {F Y w D t H P' A' r d n δ C}
variable (X₀ : Cluster V W S b N L P g v F Y w D t H P' A' r d n δ C) (hb:b ≤ N)
include X₀
omit [∀ i,Fintype (T i)] in
lemma Cluster.true (x) {i} (hi : i ≤ N) : collection v (lands V N P i) g x= Weave.all V w (P' x) i := by rw [collects hi,X₀.mark]; rfl
lemma Cluster.guard : Guard (smear W S b N L P g v φ) r (∑ i∈w,D i) := by
  apply stationed L.volume v P _ (fun j hj=> L.earns v g X₀.ready φ j hj) (∑ i∈w,D i) r
    (Eventually.of_forall fun x => ?_)
  rw [Cover.specialized,X₀.mark]; exact (Guard.prod w _ D (X₀.cap x).rankMark).const_smul _ -- inspect
lemma Cluster.belongs : smear W S b N L P g v φ∈ F N := by
  change _∈ (F N).toSubmodule; apply obeys L.volume v P (Cover.versions (S:=S) g φ) (fun j hj=> L.earns v g X₀.ready φ j hj) (F N).toSubmodule
      (Eventually.of_forall fun x => ?_)
  rw [Cover.specialized, X₀.mark]; exact (F N).smul_mem ((F N).prod_mem (fun i hi => (X₀.cap x).invariantMark i hi)) _ -- inspect
local notation "η" => ∑ i∈w,H i
local notation "τ" => ∑ i∈w,t i
local notation "B" => W.μ b
local notation "p" => max τ (Weave.debited r d n δ τ η)+1
variable (he : (∑ i ∈ w,H i) + 2 ≤ n)
def toBook (r d n δ u ζ : ℕ) := (1+δ)*n + (max u (Weave.debited r d n δ u ζ)+1)
local notation "Y₁" => toBook r d n δ τ η
include hb he in
omit [∀ i,Fintype (T i)] in
/-- Cost as requested generator pre-price for assembled markup, *not* cost in some unrelated
rootless proof. -/
theorem booking : Fits W S b (blue V W S b N L P g v) n r (C^Y₁) := by
  apply L.fits v (lands V N P b) g X₀.ready n
  intro z; filter_upwards [L.centered z] with x hx
  have h' : 1 ≤ C:= le_trans (by norm_num) X₀.ok
  have hy:=zero_le_one.trans h'
  have hB:=W.positive b
  have hh:= W.shift b (W.tape.sphere (S.point b z) 0) (Y x) n r (Weave.all V w (P' x) b) (show 0 ≤ C^δ*B by positivity) (X₀.cellLens z x hx)
  rw [X₀.true x hb]; apply hh.trans; rw [mul_div_cancel_right₀ _ (W.positive _).ne'];
  have hi:=propagates (X₀.cap x) he (show b ∈ Icc b N by simpa);
  rw [Scale.Y,div_self (W.positive b).ne',Real.log_one, add_zero, one_pow,mul_one] at hi
  have hk : tip (C^δ) n ≤ (C^(1+δ))^n:= by unfold tip; apply pow_le_pow_left₀ (by positivity); rw [pow_add,pow_one]; nlinarith [X₀.ok,one_le_pow₀ (n:=δ) h']
  apply (mul_le_mul hk hi (W.nn ..) (by positivity)).trans
  unfold toBook; rw [← pow_mul,← pow_add] -- inspect

include he in
omit [∀ i,Fintype (T i)] in
lemma Cluster.gains (A : Lens W.tape) (x:X)
    (hr:(S.test φ x ≠ 0)→ A.m ≤ (Y x).m) {i:ℕ} (ht:i∈Icc b N) :
    W.value i n r A (collection v (lands V N P i) (Cover.versions (S:=S) g φ) x) ≤ ‖S.test φ x‖ * tally W C B i p η := by
  rw [Cover.specialized,Cluster.true X₀ x (mem_Icc.mp ht).2];
  unfold Scale.value; rw [mag_smul]; by_cases h:S.test φ x=0
  · rw [h,norm_zero,zero_mul,zero_mul]
  exact mul_le_mul_of_nonneg_left ((W.mono i A (Y x) n r _ (hr h)).trans (Weave.propagates (X₀.cap x) he ht)) (norm_nonneg _)
include he in
lemma younger (A : Lens W.tape) (hA:∀ᵐ x∂ L.volume,S.test φ x ≠ 0 → A.m ≤ (Y x).m) (hφ : Integrable (S.test φ) L.volume)
    {K:ℝ} (hK : (∫ x,‖S.test φ x‖ ∂ L.volume) ≤ K) {i} (ht:i∈Icc b N) :
    W.value i n r A (V.yield i N (smear W S b N L P g v φ)) ≤ K * tally W C B i p η := by
  rw [smears V (mem_Icc.mp ht).2]; apply (applies L.volume v (lands V N P i) _ (fun j hj=> L.earns v g X₀.ready φ j hj) _ n r (W.alive i A)
    _ (hφ.norm.mul_const (tally W C B i p η)) (hA.mono fun x he' => Cluster.gains X₀ he A x he' ht)).trans
  rw [integral_mul_const]; apply mul_le_mul_of_nonneg_right hK
  have hm:=W.positive i; have hi:=(W.decrease (mem_Icc.mp ht).1); have hh : 0≤W.Y C B i:= by unfold Scale.Y; linarith [X₀.ok,Real.log_nonneg ((one_le_div hm).mpr hi)]
  have hb:=W.positive b; unfold tally; positivity
end Film
end YM.FormalOPE.RG10.Capture
