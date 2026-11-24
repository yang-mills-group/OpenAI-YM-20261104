import YM.FormalOPE.RG10.Capture.Costume
import YM.FormalOPE.RG10.Transit.Conductor
/-!
# Far normalized identity response difference after capture (in bulk formal episodes)

This is a nested-estimation input. Fixed arity/order not nonperturbatively asymptotic;
works proof-costed for one or many exteriors, even with positive-order interactions before and
after capture, at all preregulated apertures obeying the stated Schedule hypotheses. The stop
matrices/projections and candidate are chosen from incoming data **before the test** (for fixed
cutoff, soft stop and cluster); no rechoosing according to beating two different losses.
Local choices on approximation/wrapping must be recorded before any projection. The stencil
in `Z` computes with true fields; none of the hypotheses let you skip checking that about the given
Wilson scheme. No claim about actual reconstruction or map densities. -/
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

-- one variable for exterior polynomial representation cost. take p*=max of the costs, ζ attenuation. Exterior lens and clearance supplied by profiles in application.

variable {p q d₂ u ξ' : ℕ} {R₀ : Channel (U N)}
    (exhibit : ∀ i∈Icc t N, W.value i (maximumNeeded n r d) r E (V.yield i N R₀) ≤ tally W C (W.μ t) i p q) -- exhibit shadow label cost!
    (hk:d₁+d₂ ≤ d) (hr : Guard R₀ r d₂) (hm : R₀∈F N)
    (ho : O.m ≤ A.m) (he : O.m ≤ E.m) (hl : A.Spaced E (W.μ t/C^δ))
local notation "Vp" => max p (arity r d n₁ δ τ η)
local notation "π" => Far.invoice r d n δ Vp q (max η m) m
local notation "Pay" => A₀ b ^ π * W.fade (m + ξ) b t
-- exterior query costs are w.r.t. through-degree n inner lives. read for all levels. rank separately.
include exhibit hk hr hm ho he hl
lemma entrance : Far.Monitor V W (fun i=> (F i).toSubring) A E O C ξ t b N Vp (max η m) q n r d d₁ d₂ δ (Q₁-Q₂) R₀ m := by
  obtain ⟨h1,h2,h3,h4⟩:=Q.order
  refine ⟨Q.regular,Q.rank_signed,hr,hk,Q.identity,hm,hl,ho,he,?_,?_,?_⟩;
  · intro i hi; have hb:= h1.trans (mem_Icc.mp hi).1; have H0:=W.positive i; have hR:=W.positive t
    apply (Q.hotter hi).trans; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_trans (by norm_num) (Q.regular.at2 hb)) (le_max_right ..)) (by positivity)
  · intro i hi; have H0:=W.positive i; have hR:=W.positive t
    apply (exhibit _ hi).trans; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_trans (by norm_num) (Q.regular.at2 ((mem_Icc.mp hi).1))) (le_max_left ..)) (by positivity)
  intro i hi; apply (Q.closedCost hi).trans; apply mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_trans (by norm_num) (Q.regular.at2 h1)) _) W.fade_nn;
  apply le_trans ?_ (le_max_right ..); unfold arity;
  exact le_trans (le_max_right ..) (Nat.le_succ _)

variable (hn : max (∑ x∈w,h x) m + q +2 + m ≤ n) -- notation with scoped var before binder! Danger
include hn

theorem watches : W.value t n r O (V.yield t N (Q₁*R₀)-V.yield t N (Q₂*R₀)) ≤ Pay := by
  obtain ⟨h1,h2,h3,h4⟩:=Q.order
  rw [← map_sub,← sub_mul]; exact Far.looks (Q.entrance exhibit hk hr hm ho he hl) h1 (h3.trans h4) Q.growth hn

/-- To an identity response in the bulk prior to medium-scale or continuum/position normalization.
Generic stability of the additional soft segment separate. Use uniformly where that polynomial cost
is verified at announced (e.g. square-log) ages. Choose μ_b ≤ poly(ρapprox) times reference length
so the exponent attenuates according to `Far`. Don't estimate at real coupling with this.
-/
theorem voices (ht:u ≤ t) (hf: Fence V W O (fun i=> (F i).toSubring) r n d u t (A₀ b ^ ξ')) :
    rate r (echo V u N (Q₁ * R₀) - echo V u N (Q₂ * R₀)) ≤ A₀ b ^ ξ' * Pay := by
  obtain ⟨h1,h2,h3,h4⟩:=Q.order; have hu':t ≤ N:= h1.trans (h3.trans h4);
  let F₀:= (Q₁-Q₂)*R₀; have hP : F₀∈F N := (F N).mul_mem (show Q₁-Q₂∈F N from Q.identity) hm -- inspect (fun i=> (F i).toSubring) notation
  rw [← map_sub,← sub_mul]
  have hy:= Voyage.positions Q.regular.rank (Guard.mono (Q.rank_signed.mul hr) hk) hu' -- instance
  have H0 : 0 ≤ A₀ b := Q.regular.toHours.paid h1
  have hh := Q.watches exhibit hk hr hm ho he hl hn; rw [← map_sub,← sub_mul] at hh; apply (reflects _ _ _ ht hu' _ _ _ _ hf hy (Voyage.keeping Q.regular.selfish (show F₀ ∈ (F N).toSubring from hP) hu')).trans (mul_le_mul_of_nonneg_left hh (by positivity))

omit hn exhibit hk hr hm in
/-- Example port direction, from any distant bundle of mutually test-separated inserted columns,
not a requirement that the exterior-estimates for an already joined bundle are provided. -/
lemma swarm {β : Type*} {S' : Finset β} {Q' : β → Channel (U N)} {H l D' : β → ℕ} {E':β→Lens W.tape} (ht: Contracts V W (fun i=> (F i).toSubring) t N r d n₁ R C δ S' Q' E E' D' l H)
    (hu:(∑ i∈S',H i)+2 ≤ n₁) :
    let z:=∑ i∈S',l i; let q:=∑ i∈S',H i;
    let Y:=max z (debited r d n₁ δ z q)+1; let d₂:=∑ i∈S',D' i
    let P:=∏ i∈S',Q' i
    d₁+d₂ ≤ d → Far.Monitor V W (fun i=> (F i).toSubring) A E O C ξ t b N (max Y (arity r d n₁ δ τ η)) (max η m) q n r d d₁ d₂ δ (Q₁-Q₂) P m := by
  intro z q Y d₂ P hu'
  apply Q.entrance (R₀:=P) ?_ hu' (Guard.prod S' Q' D' ht.rankMark) ((F N).prod_mem fun i hi=>ht.invariantMark i hi) ho he hl
  exact fun i hi => (W.sooner i E _ _ _ _ Q.health.1).trans (Weave.propagates ht hu hi)
end Install
end YM.FormalOPE.RG10.Capture
