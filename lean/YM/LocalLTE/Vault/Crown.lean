import YM.LocalLTE.Vault.Pass
/-!
# Unmasked curvature-chart summary on arbitrary course
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Vault
open Finset Function Filter Lattice Wilson RG Source Labels Extra.Histories
open Push Local PhysicalNext.Repeat MeasureTheory ConnectedActivityE6 Blaze
open Next.Foundations Push.AbsoluteSums Animals Port FrameBox Grove
open Pressure
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{n : Side} {o : Site n} {ι : Type} {d:ℕ}
-- scaled probes from actual operator axis. 
attribute [local instance] Gauge.frobInner
noncomputable def apprise (G:Gauge) (d j:ℕ):= 1+∑ i: ((Labels.frames G).level d).Index, (Sect.authorityL G d j i false).choose
lemma app_one (G:Gauge)(d j:ℕ):1 ≤ apprise G d j:=le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => ((Sect.authorityL G d j i false).choose_spec.1))) -- order check
set_option quotPrecheck false
local notation "R"=> localSection G d
local notation "F"=> (Labels.frames G).level d
set_option quotPrecheck false
variable (j:ℕ)
lemma probe_b (v:((Labels.frames G).level d).Coeff)(A:Directions G n)(h: ‖A‖≤ 1)(o:Site n): Brush j (apprise G d j*((Labels.frames G).level d).coeffSize v) 1 ((localSection G d).places v o ∘ FrameBox.Grove.soloV) A:=by
    let C:= apprise G d j; have he:= app_one G d j; let b(i:(F).Index):= R|>.places (Size.axis (F) i) o
    have hx(i:(F).Index): Brush j (C*‖v i‖) 1 (fun z:Directions G n=> v i*b i (FrameBox.Grove.soloV z)) A:=by
         have hf:= (Sect.authorityL G d j i false).choose_spec.2 _ o A h
         have hu(i'): ‖Hue 1 false i'‖ ≤ 1*‖i'‖:= by rw [hueCost,norm_one]
         have hb:= hf.report (Hue 1 false) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one hu)
         let f(i:(F).Index):= (Sect.authorityL G d j i false).choose
         have hg: Brush j C 1 (b i ∘ FrameBox.Grove.soloV) A:=by
            have hS: Hue 1 false ∘ ((Port.scaleQ false) ∘ b i) = b i:= (Sect.basisT G d o i).symm
            have h':Brush j (1*f i) 1 (b i ∘ FrameBox.Grove.soloV) A:= by
                exact hS ▸ (show Brush j (1*f i) 1 ((Hue 1 false ∘ Port.scaleQ false ∘ b i) ∘ FrameBox.Grove.soloV) A from hb)
            exact h'.climb (by rw [one_mul]; exact (single_le_sum (f:=f) (fun j' _=> (Sect.authorityL G d j j' false).choose_spec.1) (mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)) le_rfl
         let L:= ContinuousLinearMap.mul ℝ ℂ (v i); have hz(i'): ‖L i'‖≤ ‖v i‖*‖i'‖:= (norm_mul _ i').le
         rw [mul_comm]; exact hg.report L (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) hz)
    have ht: ((localSection G d).places v o ∘ FrameBox.Grove.soloV)=(fun z:Directions G n=>∑ i: (F).Index,v i*b i (FrameBox.Grove.soloV z)):=by funext z; rw [Function.comp_apply, Multi.Maquette.portions, Finset.sum_apply]; rfl
    change Brush _ (C*_) _ _ _; rw [ht,Frame.coeffSize,mul_sum]; exact Brush.spree _ _ _ zero_le_one (fun i _=>hx i) -- args
variable {x:ℝ} (A:BudgetPoint)
lemma scaled_ledger (v:((Labels.frames G).level d).Coeff)(hv:((Labels.frames G).level d).coeffSize v≤1)(D:ℕ)(hd:d≤ D)(ht:1≤ x)(hk:A.threshold⁻¹ ≤x) : ((Labels.frames G).level d).coeffSize (((Labels.frames G).level d).scaled A.threshold⁻¹ v) ≤ x^(most G D):=by
   let u:= x^(most G D); refine le_trans ?_ (mul_le_of_le_one_right (show 0≤u from pow_nonneg (zero_le_one.trans ht) _) hv); unfold Frame.coeffSize; rw [mul_sum]; refine sum_le_sum fun i _=>?_ ; have h0:A.threshold>0:=A.threshold_pos
   rw [Frame.scaled_apply, norm_mul,Complex.norm_real, Real.norm_of_nonneg (by positivity)]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
   exact (pow_le_pow_left₀ (by positivity) hk _).trans (pow_le_pow_right₀ ht (le_sup_of_le (mem_range.mpr (Nat.lt_succ_of_le hd)) (le_sup (f:=fun i=> ((Labels.frames G).level d|>.grades i).2) (mem_univ i))))
variable {A}
noncomputable def alb (G:Gauge) (D j:ℕ):= 1+∑ i∈ Finset.range (D+1), apprise G i j
lemma alb_one (G:Gauge)(D j:ℕ): 1≤ alb G D j:= le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _=>zero_le_one.trans (app_one ..)))
noncomputable def input_rate (G:Gauge) (D j c:ℕ) (t:ℝ):= (alb G D j*t^(most G D))^c
noncomputable def glass (G:Gauge)(D j c:ℕ)(t:ℝ):= input_rate G D j c t * (1+((c:ℝ)))^j +1
lemma glass_bill (L:Side)(D K:ℕ): Rate G L ((most G D:ℝ)*K) (fun x:ℝ=> Vault.glass G D j K (betaF G x L)):=by
    let f :ℝ→ℝ:= fun x=> betaF G x L; let u : Rate G L 1 f:= Rate.hat; let v:= alb G D j
    have hu: Rate G L ((most G D:ℝ)* K) (fun x:ℝ=> input_rate G D j K (betaF G x L)):=by convert! (((u.pow _).mul_left v).pow K) using 1; ring -- placeholder
    exact (hu.mul_right _).add ((Rate.const 1).weaken (by positivity))
section
variable (P: BudgetPoint)(i:ι→ℕ)(k:∀ z:ι, ((Labels.frames G).level (i z)).Coeff)(I: Finset ι)
variable (ht:∀ z∈I, ((Labels.frames G).level (i z)).coeffSize (k z) ≤1)
variable (D c:ℕ)(he:∀ z∈I,i z≤D)(hi:I.card ≤ c)
    (hq:1≤x)(hP:P.threshold⁻¹ ≤ x) (o:Site n)
local notation "p₁"=> fareK P i k I o
local notation "p₀"=> (p₁ - halcyon p₁)
include ht he hi hq hP j
lemma gloss (A:Directions G n)(h:‖A‖≤1): Brush j (glass G D j c x) 1 (p₀ ∘ FrameBox.Grove.soloV) A:=by
    have he' := fare_small P i k I ht (o:=o)
    let q :=alb G D j*x^(most G D); have hq' : 1 ≤ q:=one_le_mul_of_one_le_of_one_le (alb_one ..) (one_le_pow₀ hq)
    have hf(z:ι)(hz:z∈I): let f:= presented (localSection G (i z)) o P.threshold (k z); Brush j q 1 (f ∘ FrameBox.Grove.soloV) A:=by
        intro f; let g:= (Labels.frames G).level (i z); apply (probe_b j A h o (d:=i z) (v:=g.scaled P.threshold⁻¹ (k z))).climb _ le_rfl
        apply mul_le_mul _ (scaled_ledger P (k z) (ht _ hz) D (he _ hz) hq hP) (Work.G08.size_nonneg ..) (zero_le_one.trans (alb_one ..)); exact (single_le_sum (f:=fun i=> apprise G i j) (fun _ _=>zero_le_one.trans (app_one ..)) (mem_range.mpr (Nat.lt_succ_of_le (he _ hz)))).trans (le_add_of_nonneg_left zero_le_one)
    have h (u:Finset ι): u ⊆ I→ Brush j (q^u.card) (u.card:ℝ) (fareK P i k u o ∘ FrameBox.Grove.soloV) A:=by
       induction u using Finset.induction_on with
       | empty => intro _; simpa [fareK] using! Brush.certified (x:=A) (k:=j) (show (0:ℝ)≤0 from le_rfl) (1:ℂ)
       | insert i' s hi ih=>
          intro h; obtain ⟨hz,hq⟩:= insert_subset_iff.mp h; let f:=fareK P i k s o; let g:Config G n→ℂ:= presented (localSection G (i i')) o P.threshold (k i')
          rw [show fareK P i k (insert i' s) o = _ from (show _=g*f from prod_insert hi), Finset.card_insert_of_notMem hi]; push_cast; rw [pow_succ]; simpa [mul_comm q,add_comm (1:ℝ)] using! (Brush.paints (f:=g ∘ FrameBox.Grove.soloV) (g:=f ∘ FrameBox.Grove.soloV) (hf _ hz) (ih hq)) -- order?
    have hg:Brush j (q^c) (c:ℝ) (p₁ ∘ FrameBox.Grove.soloV) A:= (h I (Finset.Subset.refl _)).climb (pow_le_pow_right₀ hq' hi) (Nat.cast_le.mpr hi)
    exact (hg.trim).separating ((Brush.certified zero_le_one (fareK P i k I o 1)).climb he' le_rfl)
-- demand one H proof for real θ
lemma shades (b:Bool)(A:Directions G n)(h:‖A‖≤1): Brush j (glass G D j c x) 1 ((Port.scaleQ b ∘ p₀) ∘ FrameBox.Grove.soloV) A:=by
    have hx:= gloss j P i k I ht D c he hi hq hP o A h -- order
    have ht: ‖Port.scaleQ b‖≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun i=> by cases b; simpa only [Port.scaleQ, one_mul] using! Complex.abs_re_le_norm i; simpa only [Port.scaleQ,one_mul] using! Complex.abs_im_le_norm i)
    have he:= hx.report (Port.scaleQ b) ht; rw [one_mul] at he;exact he
end
end YM.LocalLTE.Vault
