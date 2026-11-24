import YM.OPE.Compatible.Turbine.Drive
import YM.OPE.Compatible.Village.Turn
/-!
# Finite partition scoring, staying on genuine filters.
Avoid choosing infinite demands or changing the scoring exponent on successively smaller infinite refinements. Choose fixed work widths even if only finitely many regimes occur infinitely often. Includes bottom filters where vacuous.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Filter Set
open scoped Topology BigOperators Classical
variable {I J X:Type*}{p:I→X} [Norm X]{φ:Filter I}{s:I→ℝ}{S: I→Prop}
-- maybe existing eq
lemma Score.chunk (h:Tendsto s φ atTop)
    (hh: Score (φ ⊓ 𝓟 {i| S i}) s p)
    (hp: Score (φ ⊓ 𝓟 {i| ¬ S i}) s p): Score φ s p:= by
    obtain ⟨a,ha⟩:=Score.fitsQ hh (h.mono_left inf_le_left); obtain ⟨b,hb⟩:= Score.fitsQ hp (h.mono_left inf_le_left); rw [eventually_inf_principal] at ha hb; apply Score.under (Score.power (max a b) (Score.time h) h)
    filter_upwards [ha,hb,h.eventually_ge_atTop 1] with i hi hV he; by_cases hx:S i; exact (hi hx).trans (pow_le_pow_right₀ he (le_max_left ..)); exact (hV hx).trans (pow_le_pow_right₀ he (le_max_right ..))
lemma Score.finitely {S : J→ I→Prop} (P: Finset J) (h:Tendsto s φ atTop) (hh:∀ᶠ i in φ,∃ j∈P,S j i)(hp:∀ j∈P, Score (φ ⊓ 𝓟 {i| S j i}) s p): Score φ s p:=by
    induction P using Finset.induction_on generalizing φ with
    | empty => simp only [Finset.notMem_empty,false_and,exists_false,eventually_false_iff_eq_bot] at hh; subst φ; exact (Score.time h).liftp (by simp)
    | insert j P hj ih =>
       let a:= {i|¬ S j i}; let l:= φ⊓ 𝓟 a
       refine Score.chunk h (hp j (Finset.mem_insert_self ..)) (ih (h.mono_left (show l ≤ φ from inf_le_left)) ?_ ?_)
       · filter_upwards [hh.filter_mono (show l ≤ φ from inf_le_left), (show ∀ᶠ i in l,i∈a from (le_principal_iff ..|>.1 inf_le_right))] with i h hI; obtain ⟨b,hb,ha⟩:= h; rcases Finset.mem_insert.mp hb with rfl|hb; exact absurd ha hI; exact ⟨b,hb,ha⟩
       intro a ha; exact (hp a (Finset.mem_insert_of_mem ha)).shoot (inf_le_inf_right _ inf_le_left)
namespace Arboreal.Trace
open Spec
variable {X I:Type} [PartialOrder X][OrderBot X][Fintype X](D:Origin X){P:Finset X}{φ:Filter I}{T:I→ℝ}{s:I→X→ℝ}
-- max scheduling
lemma Bright.lit_rules {k:X→ℕ}(h: Series P k)(hp:(rest P).Nonempty):∃ x∈ rest P, whenHigh P k=k x ∧ Maximal (·∈ P) x:=by
    obtain ⟨x,hx,he⟩:=Finset.exists_mem_eq_sup P ⟨⊥,h.base.base⟩ k
    let F:=(rest P).filter fun i=> k i=k x
    have hp': F.Nonempty:=by
       by_cases hf:x=⊥
       · obtain ⟨a,ha⟩:= hp; have hh:= Finset.mem_erase.mp ha; refine ⟨a,Finset.mem_filter.mpr ⟨ha,le_antisymm ?_ (h.timing _ _ (hf.symm ▸ bot_le) hh.2)⟩⟩; rw [← he]; exact Finset.le_sup hh.2
       exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hf,hx⟩,rfl⟩⟩
    obtain ⟨y,hy⟩:= F.exists_maximal hp'; have hb:= Finset.mem_filter.mp hy.1
    refine ⟨y,hb.1,he.trans hb.2.symm,(Finset.mem_erase.mp hb.1).2,fun {a} hA hv=>?_⟩
    have hw : a ≠ ⊥:=ne_bot_of_le_ne_bot (Finset.mem_erase.mp hb.1|>.1) hv
    exact hy.2 (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hw,hA⟩, le_antisymm (le_trans (Finset.le_sup hA) he.le) (le_trans hb.2.ge (h.timing _ _ hv hA))⟩) hv
lemma Burst.pinch (Y:Burst D P φ T s){ψ:Filter I}(h:ψ ≤ φ): Burst D P ψ T s:=by
    refine ⟨fun η he=>?_,Y.fronts.filter_mono h⟩; let X:=Y.fresh η he; exact ⟨X.crowned,X.ray.mono_left h,he,fun v hv=> (X.fade v hv).mono_left h,fun v hv=> (X.charge v hv).shoot h,X.dim.filter_mono h⟩
-- ratio price failure
variable {G:Gauge}{C:Family G}{S:Table C.book}{Λ:Extraction.Order}
variable (A: Allot C)(hG:G.Simple)(Y:Burst D P φ T s){v:X}(hv:v∈rest P){η:ℝ}(hη:0<η) (b:ℕ)
include hη A hG Y hv
lemma breather (h:∀ᶠ i in φ, ¬ aperture D C b 2 η (T i) (s i) v ≤ schedule C b η (s i) v-1): Score φ T (fun i=> s i (par D v) / s i v):=by
    let H':=Y.fresh η hη; let j i:= aperture D C b 2 η (T i) (s i) v; let k i:= schedule C b η (s i) v-1; have hj:= Finset.mem_erase.mp hv |>.2
    have hf := Pixel.gleans D A hG b H' hj
    have hz := (arrive D hG A H' b 2 (Finset.mem_union_left _ hj)).2; have hi:= (hf.2.2).up.product hz.down
    have he:∀ᶠ i in φ, 0<s i v := (H'.fade v hj).eventually self_mem_nhdsWithin
    have hw:∀ᶠ i in φ,0<s i (par D v):=(H'.fade _ (H'.crowned.roots (par_le ..) hj)).eventually self_mem_nhdsWithin
    apply hi.pointwise ?_ ((he.and hw).mono fun i hi=> (div_pos hi.2 hi.1).le)
    filter_upwards [h,he,hw] with i hp hv hK; change ¬ j i ≤ k i at hp
    change _ ≤ C.S.a (k i)/_ * (C.S.a (j i)/_)⁻¹
    have h0:=C.S.a_pos (j i); have hc:= C.S.strictAnti (lt_of_not_ge hp)
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hc.le hv.le) (inv_pos.mpr (div_pos h0 hK)).le); field_simp
end Arboreal.Trace
end YM.OPE
