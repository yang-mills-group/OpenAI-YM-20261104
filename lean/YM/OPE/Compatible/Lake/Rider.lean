import YM.OPE.Compatible.Lake.Lance
/-!
# Result in Tall. Bound shift-inverse ratio exposure.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lake
open Function Filter MeasureTheory Spec Lattice RG Word Cov Allot MergeProof Next.Extract Dash Extra.Histories
open Next.Rank Next.Rank.Price Extraction
open ContinuousLinearMap
open scoped Topology Classical BigOperators
variable {G:Gauge} {C:Family G}
variable {d i:ℕ} {E: Fin (d+1)→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℂ (E i)]
local notation "I"=> Fin (d+1)
namespace Treaty
variable {U s t:ℝ}{F:Dock E≃L[ℂ] Dock E}
set_option quotPrecheck false
variable (h:G.Simple) (H:Treaty (extent C i) (Real.exp (t*levy C i)) U F) (hs:0<s)
local notation "X"=> rescale F (cram C E s (i+1)) (cram C E s i)
local notation "l"=> levy C i
def edgeWt (C:Family G)(s:ℝ)(d i:ℕ):= Real.exp (d*s*levy C i)*Real.exp (-s*hill C i)
include H h hs
lemma pins (j:I) : ‖route (X).toContinuousLinearMap j j‖ ≤ extent C i^(d-j.val)*Real.exp ((t+d*s)* levy C i) ∧ ‖route (X).symm.toContinuousLinearMap j j‖≤ (extent C i^(d-j.val))⁻¹*Real.exp ((t+d*s)*levy C i):=by
    rw [(axesX F j j).1,(axesX F j j).2, norm_smul,norm_smul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg (Real.exp_nonneg _),Real.norm_of_nonneg (Real.exp_nonneg _)]
    have hx(i):0≤ extent C i:=by have := extent_two C i;linarith
    have hW: 0 ≤ s*l:= mul_nonneg hs.le (levy_pos h i).le
    have hh: s*j.val*l ≤ s*d*l:=by linarith only [mul_le_mul_of_nonneg_left (show (j.val:ℝ)≤ (d:ℝ) by exact_mod_cast Nat.le_of_lt_succ j.isLt) hW]
    have hv: -(s*j.val*l) ≤ s*d*l:=by
        linarith only [mul_nonneg hW (Nat.cast_nonneg (α:=ℝ) j.val),hh]
    set a:= extent C i^(d-j.val)
    have ha:0≤a:=(pow_nonneg (hx i) _)
    unfold levy at *
    constructor
    · apply (mul_le_mul_of_nonneg_left (H.grace j) (Real.exp_nonneg _)).trans; rw [mul_left_comm,← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ ha; apply Real.exp_monotone; linarith only [hh]
    apply (mul_le_mul_of_nonneg_left (H.value j) (Real.exp_nonneg _)).trans; rw [mul_left_comm,← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ha); apply Real.exp_monotone; linarith only [hv]
omit h hs in
lemma lowMark (i' j:I) (he:i'<j): route (X).toContinuousLinearMap i' j=0 ∧ route (X).symm.toContinuousLinearMap i' j=0:=by rw [(axesX F i' j).1,H.toC _ _ he,smul_zero,(axesX F i' j).2,H.ofC _ _ he,smul_zero]; exact ⟨rfl,rfl⟩
lemma spreadEq (j k:I)(hc:j≠k): ‖route (X).toContinuousLinearMap j k‖ ≤ edgeWt C s d i * U ∧ ‖route (X).symm.toContinuousLinearMap j k‖≤ edgeWt C s d i * U:=by
    have hp:0 ≤ U:=(norm_nonneg _).trans H.charge
    rcases lt_or_gt_of_ne hc with hk|hk
    · obtain ⟨hv,he⟩:=H.lowMark (s:=s) j k hk; rw [hv,he,norm_zero]; have hb:0≤ edgeWt C s d i*U:= by unfold edgeWt; positivity
      exact ⟨hb,hb⟩
    rw [(axesX F j k).1,(axesX F j k).2, norm_smul,norm_smul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg (Real.exp_nonneg _),Real.norm_of_nonneg (Real.exp_nonneg _),edgeWt,← Real.exp_add]
    have ht:0≤ s*l:=mul_nonneg hs.le (levy_pos h i).le; have hL:0 ≤ s*hill C i:=mul_nonneg hs.le (hill_pos C _|>.le)
    have hh := mul_le_mul_of_nonneg_left (show (k.val:ℝ)+1 ≤ (j.val:ℝ) by exact_mod_cast Fin.lt_def.mp hk) hL
    have hz := mul_le_mul_of_nonneg_left (show (k.val:ℝ)≤ (d:ℝ) by exact_mod_cast Nat.le_of_lt_succ k.isLt) ht
    have heq := mul_nonneg ht (Nat.cast_nonneg (α:=ℝ) j.val); have hu := mul_nonneg ht (Nat.cast_nonneg (α:=ℝ) d)
    constructor
    · refine mul_le_mul ?_ ((tolls F.toContinuousLinearMap ..).trans H.charge) (norm_nonneg _) (Real.exp_nonneg _); apply Real.exp_monotone; unfold levy at *; linarith only [hz,hh]
    refine mul_le_mul ?_ ((tolls F.symm.toContinuousLinearMap ..).trans H.inverse) (norm_nonneg _) (Real.exp_nonneg _); apply Real.exp_monotone; unfold levy at *; linarith only [hh,heq,hu]
omit H h hs
def radiator (C:Family G)(s:ℝ)(d i:ℕ):= Real.exp ((d:ℝ)*s*hill C (i+1))
include h hs
lemma diffWay (a b:Dock E ≃L[ℂ] Dock E)
 (x:ℝ) (hV: ‖a.toContinuousLinearMap-b.toContinuousLinearMap‖ ≤ x)(hW: ‖a.symm.toContinuousLinearMap-b.symm.toContinuousLinearMap‖ ≤ x)(i:ℕ):
    let Tv:= cram C E s (i+1);let Y:=cram C E s i
    ‖(rescale a Tv Y).toContinuousLinearMap-(rescale b Tv Y).toContinuousLinearMap‖ ≤ radiator C s d i*x∧
    ‖(rescale a Tv Y).symm.toContinuousLinearMap-(rescale b Tv Y).symm.toContinuousLinearMap‖ ≤ radiator C s d i*x:=by
       intro q r
       let K(u:Dock E ≃L[ℂ] Dock E):= rescale u q r
       let Q(u v:Dock E ≃L[ℂ] Dock E):Train E:= u.toContinuousLinearMap-v.toContinuousLinearMap
       have hx:=sand (E:=E) C hs.le i; have hz:=sand (E:=E) C hs.le (i+1)
       let R:= radiator C s d i; have hp:0≤ x:= (norm_nonneg _).trans hV
       have hl: Real.exp ((d:ℝ)*s*hill C i) ≤ R:=Real.exp_monotone (mul_le_mul_of_nonneg_left (le_of_lt (show hill C i<hill C (i+1) from sub_pos.mp (levy_pos h i))) (mul_nonneg (by positivity) hs.le))
       have he(p q:Dock E ≃L[ℂ] Dock E) (f:Train E) (hr:‖p.toContinuousLinearMap‖ ≤ 1)(hs: ‖q.toContinuousLinearMap‖ ≤ R)(ha: ‖f‖ ≤ x): ‖p.toContinuousLinearMap.comp (f.comp q.toContinuousLinearMap)‖ ≤ R*x:=by
          apply (opNorm_comp_le ..).trans; apply (mul_le_of_le_one_left (norm_nonneg _) hr).trans; rw [mul_comm]; exact (opNorm_comp_le ..).trans (mul_le_mul ha hs (norm_nonneg _) hp)
       constructor
       · change ‖Q (K a) (K b)‖≤_; rw [show Q (K a) (K b)=r.toContinuousLinearMap.comp ((Q a b).comp q.symm.toContinuousLinearMap) from ?_]; swap
         · ext1; simp [Q,K,rescale]
         exact he r q.symm _ hx.1 hz.2 hV
       change ‖Q (K a).symm (K b).symm‖≤_; rw [show Q (K a).symm (K b).symm=q.toContinuousLinearMap.comp ((Q a.symm b.symm).comp r.symm.toContinuousLinearMap) from ?_]; swap
       · ext1; simp [Q,K,rescale]
       exact he q r.symm _ hz.1 (hx.2.trans hl) hW
end Treaty
end YM.OPE.Lake
