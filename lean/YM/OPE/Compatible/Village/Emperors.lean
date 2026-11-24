import YM.OPE.Compatible.Village.Labor
/-!
# Genuine polylog costs (conditional on projection price). Logical quantifier: exists a single d for uniform over all layouts at each radius sufficiently small. This in turn implies the convention C product log^C by enlarging constant. Integrals consume exactly like before.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset Extraction Word Spec
open Allot Pixel Arcade Cov Cov.Display Metric
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius NNReal
variable {X I J: Type}[PartialOrder X][OrderBot X][Fintype X][Fintype J](D:Origin X)
    {G:Gauge}{C:Family G}{Λ:Extraction.Order}{S:Table C.book}(T:Final C Λ S)
variable (p:X→ S.Tag)(M η c:ℝ) (v:X→ℕ)(a:Tones T) (q:J→ S.Tag)(n:ℕ)
local notation "U"=> heart X
local notation "U'"=> rest (heart X)
variable (h:⊥∈heart X)(hM:0 ≤ M)(hη:0<η)(hC:0<c)
variable (A: Allot C)(hO:Lanes (F:=Λ) T.sector.derivatives)(H:Services C Λ S)
include A H hO h hM hη hC
lemma allYears : ∃ d:ℕ,∀ᶠ r:ℝ in 𝓝[>] 0, ∀ (s:X→ℝ)(x:X→ E4), Layout D M η s x → s ⊥=r→ ∀ y:J→ E4, ClearOf (x ⊥) y c → Empire T p v a q n D s x d y :=by
    by_contra! hf
    -- explicit blows
    have he (d:ℕ):∃ (s:X→ℝ)(x:X→E4)(y:J→E4),Layout D M η s x ∧ s ⊥ ≤ 1/(d+1:ℝ) ∧ ClearOf (x ⊥) y c ∧ ¬Empire T p v a q n D s x d y:=by
        have hP:= hf d
        -- unpack
        obtain ⟨r,hr,hR⟩:= (hP.and_eventually (eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds (by positivity:0<1/(d+1:ℝ))))).exists
        obtain ⟨s,x,hx,hs,y,hy,hh⟩:=hr; exact ⟨s,x,y,hx, hs.symm ▸ hR,hy,hh⟩
    choose s x y hx hs hy hg using he
    have hh :∀ᶠ i in atTop, Layout D M η (s i) (x i):=Eventually.of_forall hx
    have hR:Tendsto (fun i=>s i ⊥) atTop (𝓝[>]0):=by
        have hp :∀ᶠ i in atTop,s i ⊥ > 0:=Eventually.of_forall fun i=> (hx i).pos _ h
        refine tendsto_nhdsWithin_iff.mpr ⟨squeeze_zero' (hp.mono fun _ h=>h.le) (Eventually.of_forall hs) (tendsto_one_div_add_atTop_nhds_zero_nat),hp⟩
    obtain ⟨d,hd⟩:=atlasPrice D T v a q n hh hR h hM hη hC (Eventually.of_forall hy) A hO H p; let Y:= dawn D hh hR h
    obtain ⟨i,he1,hL,hK,hQ,hP⟩:= (hd.and ((eventually_ge_atTop d).and ((pad_up D Y a.fst p).and ((pad_up D Y (n+1) p).and ((Burst.life D Y).eventually_ge_atTop 1))))).exists
    have hb(k d:ℕ)(hh: 0<padding D (heart X) p k (s i))(hv:d ≤ i) : watt D p k d (s i) ≤ watt D p k i (s i):=by
       unfold watt; rw [earns_scale D p (hx i) h]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hP hv) (inv_pos.mpr hh).le
    have hw:=hb a.fst d hK hL
    refine hg i ⟨he1.ready,he1.price.trans hw, ?_, he1.error.trans (mul_le_mul_of_nonneg_right hw (Finset.sum_nonneg (fun V hv=> pow_nonneg ((hx i).ratios D hv).1.le _)))⟩
    obtain ⟨hi,hz,hb',ht⟩:=he1.seen
    refine ⟨hi,hz,hb',ht.trans ?_⟩; rw [show (n+1:ℝ)= ((n+1:ℕ):ℝ) from (by norm_cast)]; exact hb (n+1) _ hQ hL
omit hM hη hC H A hO
section testing
variable {B:Type}[TopologicalSpace B] [MeasurableSpace B][BorelSpace B] (x:B→ X→ E4)(s:X→ℝ)(hx:Continuous x)
variable (μ:Measure B)(y:B→ J→ E4)(φ:B→ℂ) (hφ:Integrable φ μ) (d:ℕ)
  (grounds: ∀ b, Empire T p v a q n D s (x b) d (y b))
include h hx grounds hφ μ
lemma running : let W b:= frontierCoefficient D T (heart X) a s (x b) p
    let z b:= nests D T v (heart X) a s (x b) p
    let u:= watt D p a.fst d s
    Integrable (fun b=> φ b*W b) μ ∧
      ‖∫ b,φ b*W b ∂μ‖ ≤ u*(∫ b, ‖φ b‖ ∂μ) ∧
      Integrable (fun b=> φ b*z b) μ ∧
      ‖(∫ b,φ b*W b ∂μ)-(∫ b,φ b*z b ∂μ)‖ ≤ u*plugs D v s*(∫ b, ‖φ b‖ ∂μ) := by
  intro W z u
  have hw : Continuous W := direct_continuous D T p a _ (tall h) x s hx (fun b=> (grounds b).ready)
  have hz : Continuous z := nested_continuous D T p v a _ (tall h) x s hx (fun b=> (grounds b).ready)
  obtain ⟨he,hf⟩:= within_price μ φ hw.aestronglyMeasurable hφ (fun b=> (grounds b).price)
  obtain ⟨hg,hj⟩:= within_price μ φ (p:= fun b=> W b-z b) (hw.sub hz).aestronglyMeasurable hφ
    (fun b=> (grounds b).error)
  change Integrable (fun b=>φ b * W b) μ at he
  change Integrable (fun b=> φ b*(W b-z b)) μ at hg
  have ht:Integrable (fun b=>φ b*z b) μ := (he.sub hg).congr (Eventually.of_forall (fun b=> by
    change φ b *W b-φ b*(W b-z b)=_; ring))
  refine ⟨he,hf,ht,?_⟩
  change ‖(∫ b,φ b*(W b-z b) ∂μ)‖ ≤ _ at hj
  simp_rw [mul_sub,integral_sub he ht] at hj; exact hj
end testing
omit h
-- signature; target not claimed until physical input
structure CrownLaw (T:Final C Λ S):Prop where
    prices {X I:Type} [PartialOrder X][OrderBot X][Fintype X][Fintype I] (D:Origin X) (p:X→ S.Tag)(v:X→ ℕ)(a:Tones T)
       (M η c:ℝ)(q:I→ S.Tag)(n:ℕ) : ⊥∈heart X→ 0 ≤ M → 0 < η→ 0<c → ∃ b:ℕ,∀ᶠ r:ℝ in 𝓝[>] 0,
           ∀ (s:X→ℝ)(x:X→ E4), Layout D M η s x → s ⊥=r → ∀ y:I→ E4, ClearOf (x ⊥) y c → Empire T p v a q n D s x b y
include A hO H
lemma attaches : CrownLaw T:=⟨fun D p v a M η c q n h hM hη hC=> allYears D T p M η c v a q n h hM hη hC A hO H⟩ -- implicit types
end YM.OPE.Arboreal.Trace
