import YM.OPE.Compatible.Village.Dune
/-!
# Effective price along scales. Common exponent on the log product. Bounded mass testers as before. Fresh simultaneous. Can use near collisions inside any compact collection as in Layout. Same as all_trees without changed representation or budget metrics.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset Extraction Word Spec
open Allot Pixel Arcade Cov Cov.Display
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {X I J: Type}[PartialOrder X][OrderBot X][Fintype X][Fintype J](D:Origin X)
    {G:Gauge}{C:Family G}{Λ:Extraction.Order}{S:Table C.book}(T:Final C Λ S)
variable (p:X→ S.Tag)(M η c:ℝ) (v:X→ℕ)(a:Tones T) (q:J→ S.Tag)(n:ℕ)
local notation "U"=> heart X
local notation "U'"=> rest (heart X)
-- predicates using product
abbrev watt (k:ℝ) (d:ℕ) (s:X→ℝ):= fuel D p 0 k s * shine s^d
structure Empire (D:Origin X)(s:X→ℝ)(x:X→E4)(d:ℕ)(y:J→E4) :Prop where
    ready : Fresh D S s x
    price : ‖frontierCoefficient D T (heart X) a s x p‖ ≤ watt D p a.fst d s
    seen : Seen T n (s ⊥) (picked (brim D (heart X)) x) (picked (brim D (heart X)) p) (x ⊥) y q (watt D p (n+1:ℝ) d s)
    error : ‖frontierCoefficient D T (heart X) a s x p- nests D T v (heart X) a s x p‖ ≤ watt D p a.fst d s* plugs D v s
variable {p}
variable {M η c :ℝ} {φ:Filter I} [φ.NeBot] {s:I→X→ℝ}{x:I→X→E4}{y:I→J→E4}
variable (hp:∀ᶠ i in φ, Layout D M η (s i) (x i)) (hc:Tendsto (fun i=>s i ⊥) φ (𝓝[>] 0))(h:⊥∈heart X)(hm: 0 ≤ M)(hi:0 < η)(hv:0<c)(hy:∀ᶠ i in φ,ClearOf (x i ⊥) (y i) c)
variable (A: Allot C)(hO:Lanes (F:=Λ) T.sector.derivatives)(H:Services C Λ S)
local notation "W"=> shine∘s
local notation "K"=>fun k i=> padding D (heart X) p k (s i)
local notation "z"=>p
include A hO H hp hc h hm hi
omit [φ.NeBot] in
lemma errorPrice (p:X→ S.Tag) : ∃ d:ℕ,∀ᶠ i in φ, ‖frontierCoefficient D T U a (s i) (x i) p-nests D T v U a (s i) (x i) p‖ ≤ watt D p a.fst d (s i)*plugs D v (s i):=by
    -- plugs and divide for nonempty
    by_cases he:(rest U).Nonempty; swap
    · refine ⟨0,Eventually.of_forall fun i=>?_⟩; rw [nests,dif_neg he,sub_self,norm_zero,plugs,not_nonempty_iff_eq_empty.mp he]; simp
    let L:=dawn D hp hc h; let P:= fun i=> plugs D v (s i); let F:= fun i=> padding D U p a.fst (s i)
    have hY := basisR D hp hm; have hQ: 0≤ envelope X M:= by unfold envelope; positivity
    have hF :∀ᶠ i in φ, 0< F i:= pad_up D L a.fst p
    let b i:= ‖frontierCoefficient D T U a (s i) (x i) p - nests D T v U a (s i) (x i) p‖
    have hK (t:X)(h:t∈U'):∀ᶠ i in φ,0< (rat D (s i) t)^(v t+1)∧ (rat D (s i) t)^(v t+1) ≤ P i:= by
       refine hp.mono fun i hi=> ?_; exact ⟨pow_pos (hi.ratios D h).1 _, Finset.single_le_sum (s:=U') (f:=fun t=>(rat D (s i) t)^(v t+1)) (fun _ hg=> pow_nonneg (hi.ratios D hg).1.le _) h⟩
    obtain ⟨t,ht⟩:=he; have hP:∀ᶠ i in φ,0<P i := (hK t ht).mono fun _ hi=> hi.1.trans_le hi.2
    obtain ⟨d,hd⟩:= (show Score φ W (fun i=>F i * (P i)⁻¹*b i) from mayor D T A hY L hi hQ hO H a v (hP.mono fun i hi=>(inv_pos.mpr hi).le) (fun t ht=> (hK t ht).mono fun i hi=> inv_anti₀ hi.1 hi.2) p).fitsQ (Burst.life D L)
    refine ⟨d,?_⟩; filter_upwards [hd,hF,hP,hp] with i hi hF hP hg; unfold watt; rw [earns_scale D p hg h]; change b i≤ (F i)⁻¹* W i^d* P i; change ‖_‖≤ W i^d at hi; rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hF.le (inv_pos.mpr hP).le) (norm_nonneg _))] at hi; field_simp at hi ⊢; nlinarith only [hi]
include hy hv
lemma atlasPrice (p:X→ S.Tag):∃ D':ℕ,∀ᶠ i in φ, Empire T p v a q n D (s i) (x i) D' (y i):=by
    let L:=dawn D hp hc h; have hX:=basisR D hp hm; have hQ: 0≤ envelope X M:= by unfold envelope; positivity
    have hf:=Burst.life D L; let p':=picked (brim D U) p; let X':= fun i=> picked (brim D U) (x i)
    let F:=fun (a:ℕ) (i:I)=> padding D U p a (s i)
    let β i:= (frontierCoefficient D T U a (s i) (x i) p); let μ i:= drift T n (s i ⊥) (X' i) p' (x i ⊥) (y i) q
    obtain ⟨k,hk⟩:= Score.fitsQ (p:=fun i=> F a.fst i * ‖β i‖) (solid_beam T D A hO H L hX hi hQ p' a) hf
    obtain ⟨l,hl⟩:= Score.fitsQ (p:=fun i=> F (n+1) i* ‖μ i‖) (solid_price T D A hO H L hX hi hQ p' y q n hv hy) hf
    obtain ⟨e,he⟩:=errorPrice D T v a hp hc h hm hi A hO H p
    let b:=k+l+e
    have hV :∀ᶠ i in φ,Fresh D S (s i) (x i):=by
       filter_upwards [hc.eventually (ground_price D T p v a H h hm hi zero_lt_one hv q n),hp,hy] with i hi hx he; exact (hi _ _ hx rfl _ he).ready -- Fresh
    refine ⟨b,?_⟩; have hA:= pad_up D L a.fst p; have hB:= pad_up D L (n+1) p
    filter_upwards [hA,hB,hV,hp,hf.eventually_ge_atTop 1,(clear_awayU D L hX hi y hy hv).2,hk,hl,he] with i hA hB hV hL hS he1 hk hl he
    have hx : (n+1:ℝ) = ((n+1:ℕ):ℝ):=by norm_cast
    refine ⟨hV,?_,⟨fresh_direct D hV _ (tall h),he1.1,he1.2,?_⟩,?_⟩
    · unfold watt; rw [earns_scale D p hL h]; change ‖β i‖≤ (F a.fst i)⁻¹* W i^b
      rw [Real.norm_of_nonneg (mul_nonneg hA.le (norm_nonneg _))] at hk
      exact (le_inv_mul_iff₀ hA).2 (hk.trans (pow_le_pow_right₀ hS (by unfold b; omega)))
    · unfold watt; rw [hx,earns_scale D p hL h]; change ‖μ i‖≤ (F (n+1) i)⁻¹* W i^b
      rw [Real.norm_of_nonneg (mul_nonneg hB.le (norm_nonneg _))] at hl
      exact (le_inv_mul_iff₀ hB).2 (hl.trans (pow_le_pow_right₀ hS (by unfold b; omega)))
    exact he.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (show 1 ≤ shine _ from hS) (show e ≤ b by unfold b; omega)) (by rw [earns_scale D p hL h]; exact inv_nonneg.mpr hA.le)) (Finset.sum_nonneg fun x hx=> pow_nonneg (hL.ratios D hx).1.le _))
end YM.OPE.Arboreal.Trace
