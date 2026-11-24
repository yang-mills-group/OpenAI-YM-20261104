import YM.OPE.Compatible.Gems.Vires
/-! # continuity pull pay and independent copy arithmetic. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
open Silt Cloud PertExtension Series Libra GaussianScore Stranded Radial Jargon Cinders Flock Lav
variable {X Y:Type}{t s:ℝ}{i:ℕ} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X] [MeasurableSpace X][BorelSpace X]
variable (A:Law X)(μ:Measure X)[μ.IsAddHaarMeasure]
local notation "M"=>quart A μ
noncomputable abbrev Amalg:=quart (united A A) (μ.prod μ)
local notation "V"=>Amalg A μ
lemma a_fst(p:X→ℝ): a_ V (p ∘ Prod.fst)=a_ M p:=by
       have he:= Swear.prodV A μ p (1:X→ℝ); rw [show a_ M (1:X→ℝ)=1 from (by unfold a_; simp), mul_one, show (1:X→ℝ) ∘ Prod.snd=(1:X×X→ ℝ) from rfl,mul_one] at he; exact he
lemma a_snd(p:X→ℝ): a_ V (p ∘ Prod.snd)=a_ M p:=by
       have he:= Swear.prodV A μ (1:X→ℝ) p; rw [show a_ M (1:X→ℝ)=1 from (by unfold a_; simp), one_mul, show (1:X→ℝ) ∘ Prod.fst=(1:X×X→ ℝ) from rfl,one_mul] at he; exact he
lemma fst_F (p:X→ℝ)(h:Fault M i p s):Fault V i (p ∘ Prod.fst) s :=Reprice (united A A) _ _ _ (ContinuousLinearMap.fst ..) (a_fst A μ) h
lemma snd_F (p:X→ℝ)(h:Fault M i p s):Fault V i (p ∘ Prod.snd) s :=Reprice (united A A) _ _ _ (ContinuousLinearMap.snd ..) (a_snd A μ) h
variable [NormedAddCommGroup Y][NormedSpace ℝ Y]
variable (S:X→ₗ[ℝ] Y)(u:Y→ₗ[ℝ] X)(h:Swear A S u)
namespace Swear
include h
local notation "U"=>ren S u
lemma u_F (p:X→ℝ)(hv:Fault M i p s): Fault V i (p ∘ ren S u) s:=Reprice (united A A) _ _ _ ((U).toContinuousLinearMap) (aboard A S u h μ) hv
omit h in lemma R_F (g:Module.Dual ℝ X)(hv:Fault M i (fun i=>g (u (S i))) s)(hi:1 ≤ i): Fault V i ((g ∘ Prod.fst)- (g ∘ ren S u)) (s+s):=by
         let H(i:X):=g (u (S i)); apply Eq.mp (show Fault V i ((H ∘ Prod.fst)-(H ∘ Prod.snd)) (s+s)= _ from ?_) ((fst_F A μ H hv).sub (snd_F A μ H hv) hi); refine congr_arg (fun f:X×X→ℝ=>Fault V i f _) (funext (fun i=>?_)); change H i.1-H i.2=g i.1-_; unfold H; rw [Function.comp_apply,shan,_root_.map_add]; change _= g i.1-(g (i.1-u (S i.1))+_); rw [_root_.map_sub]; ring
-- Holder triangle. Inputs B µ all. P2 needs b.integrability
lemma key {r:ℝ}(f:X→ℝ)(g:X→ℝ)(hp:Fault M 2 f t)(hz: Pu M g)(hx: ∃ p:Y→ℝ,f=p ∘ S)(he:Fault V 2 ((g ∘ Prod.fst)-(g ∘ ren S u)) r): ‖κ2 M f g‖≤ t*r:=by
        obtain ⟨q,hq⟩:=hx; let D: X×X→ℝ:= f ∘ Prod.fst; let a: X×X→ℝ:= g ∘ Prod.fst; let b:= g ∘ U; have ht:= fst_F A μ _ hp; have hx':Fault V 2 D t:=ht; have hy:Pu V a:=by intro i hi; obtain ⟨r,h⟩:=hz i hi; exact ⟨r,fst_F A μ g h⟩
        have hg:Pu V b:=by intro i hi; obtain ⟨r,hR⟩:=hz i hi; exact ⟨r, u_F A μ S u h g hR⟩
        have hV: (∫ i,D i*a i ∂V)= a_ M (f*g):= a_fst A μ (f*g); have hψ: (∫ i,D i*b i ∂V)= a_ M f * a_ M g:= by unfold D;rw [hq]; exact sideP A S u h μ q g
        have hm: ∀ p:X×X→ℝ, Pu V p → Integrable (D*p) V:=by
              intro p hp; obtain ⟨a,hv⟩:= hp (2*1) (by decide); exact (hx'.double hv one_pos).rich.integrable (by simp)
        have hk: Fault V 1 (D*(a-b)) (t*r):= hx'.double (show Fault V (2*1) (a-b) r from he) (by decide); rw [show κ2 M f g=a_ V (D*(a-b)) from by unfold κ2; rw [←hV,←hψ,mul_sub]; exact (integral_sub (hm _ hy) (hm _ hg)).symm]; exact hk.pays le_rfl
end Swear
end YM.OPE.Borealis.Galea
