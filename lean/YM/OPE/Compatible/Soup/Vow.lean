import YM.OPE.Compatible.Soup.City
/-!
# Uniform derivative bounds along rays of lattice fields

`atlasK` and `atlasY` give uniform `seedD` bounds for `oathV` and `oathL` under
the path-data bounds and `t * k ≤ s / 4`. `pastV` turns a `seedD` estimate into
bounds on the positive-order derivatives through order `k` along the ray `t • x`,
assuming `SerT x b`, the norm bound on `x`, and the stated scale conditions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant.Aloof
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG Gauge Precision
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ENNReal ContDiff
open Eyrie Push Push.AbsoluteSums Push.Mark Cascade Flume Flume.Page Flume.Script Pilot Finset
variable {G:Gauge}{b i j k r:ℕ}{n:Side}
variable {v s a c:ℝ}{p:Clip}{Z:PathData G}
open Next.Free Next.Scheduling
lemma sesh (_s:ℝ)(h:0<_s)(k:ℕ):∃ a:ℝ,0<a ∧ a*k≤ _s/2:=by
        refine ⟨_s/2/(k+1:ℝ),by positivity,?_⟩; set y:=_s/2/(k+1:ℝ); calc
             _ ≤ y*(k+1:ℝ):=mul_le_mul_of_nonneg_left (by norm_num) (by unfold y; positivity)
             _ =_:=div_mul_cancel₀ _ (by positivity)
lemma atlasK (G:Gauge)(p:Clip)(s b:ℝ)(hs:0<s)(hp:0 ≤ b)(k:ℕ) (t:ℝ)(ht:0<t)(hT:t*k ≤ s/2/2):∃ c:ℝ,0 ≤ c∧∀ R:PathData G,∀ U:ℝ,R.Bounds p s b U→seedD (oathV R p) t k c:=by
        let A:= heraldD G; have ha:=lumenD G; obtain ⟨V,hv,H⟩:=plants (I:=Unit) G 1 k A s t hs ht (hT.trans (by linarith)) ha; obtain ⟨C,hC,Y⟩:= plants (I:=ℕ×ℕ) G 2 k A (s/2) t (half_pos hs) ht hT ha; obtain ⟨L,hL,Z⟩:=plants (I:=ℕ×Cue G 3) G 3 k A (s/2) t (half_pos hs) ht hT ha; obtain ⟨K,hK,I⟩:= plants (I:=ℕ× Cue G 4) G 4 k A (s/2) t (half_pos hs) ht hT ha; let f(i:PlaqAxes):= ‖p.direct‖*(V*Real.exp (s*4))+‖(1/2:ℝ)‖*(∑ _ :G.ColorIndex,C*(b*b)); let z(i:Signed):=(∑ x,f x)+L*b+K*b; have hF(i):0≤ f i:=by unfold f; positivity
        refine ⟨‖avgF‖*∑ i,z i,mul_nonneg (norm_nonneg _) (sum_nonneg fun i _=> by unfold z; positivity),fun R b' h=>?_ ⟩; refine seedScale (seedSet _ (loftV R p) z (fun i _=> ?_)) _; dsimp only [z]; refine seedSum (seedSum (seedSet _ (waistV R p i) f ?_) (Z (smelt R.cubic i) _ b (smelt_cost h.three hs i) (fun j a=>brightD _ _ _))) (I _ _ b (smelt_cost h.four hs i) (fun j a=>brightD _ _ _)); intro j _; exact seedSum (seedScale (H (gateUnit G j i) 1 (Real.exp (s*4)) (ledgerF ..) (fun j _=>litD _ _)) _) (seedScale (seedSet (Finset.univ:Finset G.ColorIndex) (twinV R i j) (fun _=>C*(b*b)) (fun u _=>Y _ _ _ (duet_cost h i j u) (duet_funds R i j u))) (1/2))
lemma atlasY (G:Gauge)(s:ℝ)(hs:0<s)(k:ℕ) (t:ℝ)(ht:0<t)(hT:t*k ≤ s/2/2):∃ c:ℝ,0 ≤ c ∧ ∀ (R:PathData G)(p:Clip)(b U:ℝ), R.Bounds p s b U→ seedD (oathL R) t k (c*U):=by
        obtain ⟨C,hC,H⟩:= plants (I:=ℕ× Cue G 2) G 2 k (heraldD G) (s/2) t (half_pos hs) ht hT (lumenD G); refine ⟨‖avgF‖*∑ _:Signed,C,by positivity,fun R p b U h=>?_⟩; rw [mul_assoc,Finset.sum_mul]; refine seedScale (seedSet _ (exactAtoms R.loop) (fun _=>C*U) (fun i _=>?_)) _; exact H _ _ _ (smelt_cost h.two hs i) (fun j a=>brightD _ _ _)
-- birth depths
section
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
abbrev Past (p:E→ℝ)(x:E)(k:ℕ)(a K:ℝ):Prop:= let f:= fun t:ℝ=> p (t • x); ContDiff ℝ ∞ f∧∀ i:ℕ,0 < i → i ≤ k → ∀ t:ℝ,‖iteratedDeriv i f t‖ ≤ a^i*K
lemma pastV (A:CoverConfig G→ℝ)(h:seedD A s k a)(ha:0 ≤ a)(hs:0<s) (x:Bid.Dir G n)(hx:SerT x b)(ht:‖x‖ < c)(f: Config G n→ℝ)(hp: waterV A=f): Past (fun v=>f (represent v)) x k c (a*Squad b s):=by
         rw[←hp]; obtain ⟨H,h⟩:=seren x A h ha hx ht hs; exact ⟨H,fun i hi hv t=> (h i hi hv t).trans_eq (by ring)⟩
end
end YM.OPE.Merchant.Aloof
