import YM.OPE.Compatible.Chain.Hinge
/-!
# LId boreal sample
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Matrix Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Flume.Script
open PertExtension Series Asymptotics
variable {i:ℕ}{l:ℝ}{B:Sponsor G}{Q:Seasons B}
local notation "Lf" => Tested.germ
variable (H:Even n.val) (A:Alps B Q i l)
local notation "TK" => Libra.Keys G (Limb H)
abbrev frameD : Bid.Dir G n→ℝ:= swornV A.clip A.live
lemma dawnV (h:G.Simple): fderiv ℝ (frameD A (n:=n)) 0=0:=by
    have hk: A.word 1=0:= A.soft_word h; ext x; rw [← show iteratedFDeriv ℝ 1 (frameD A) 0 ![x]=fderiv ℝ (frameD A) 0 x from iteratedFDeriv_one_apply .. ]; -- synt
    have hh:= (A.fullK 1).wink n 1 le_rfl ![x]; rw [hk] at hh; exact (show _ = _ from hh.symm).trans (by simp [library,scribe])
include H
abbrev muralFace (T:Plot H)(x:Keys G T.Free):= mural H A (T.rollX x)
lemma mural_arc (T:Plot H): ContDiffAt ℝ ω (muralFace H A T) 0:= ((show ContDiffAt ℝ ω _ _ from (T.rollX.map_zero |>.symm ▸ muralD H A : ContDiffAt ℝ ω (mural H A) (T.rollX 0))).comp _ (LinearMap.toContinuousLinearMap T.rollX|>.contDiff|>.contDiffAt))
lemma mural_zero (T:Plot H)(hp:G.Simple): fderiv ℝ (muralFace H A T) 0=0:=by
     let f:= frameD A (n:=n); let L:= (cloak (G:=G) H) ∘L (LinearMap.toContinuousLinearMap T.rollX); let P:=f ∘ L; change fderiv ℝ (fun x=> P x/4) 0=0
     have he : fderiv ℝ P 0=0:=by
       rw [show P=f ∘ L from rfl,fderiv_comp, L.map_zero, show fderiv ℝ f 0=0 from dawnV A hp]; rfl; · rw [L.map_zero]; exact (A.fullK 1).plot n|>.differentiableAt (by simp)
       exact L.differentiableAt
     have hh :DifferentiableAt ℝ P 0:=(show DifferentiableAt ℝ f (L 0) from L.map_zero.symm ▸ ((A.fullK 1).plot n|>.differentiableAt (by simp))).comp _ L.differentiableAt
     simp_rw [div_eq_mul_inv]; rw [fderiv_mul_const hh,he]; simp
lemma delta_arc (T:Plot H)(x y:Keys G T.Free)(h:i≥4): iteratedFDeriv ℝ 2 (muralFace H A T) 0 ![x,y]=
      let v(z:Keys G T.Free):= flatten (cloak H (T.rollX z)); (dotProduct (v x) (tensor G (A.root.acts n)*ᵥ v y))/4:=by
     let f:= frameD A (n:=n); let L:= (cloak (G:=G) H) ∘L (LinearMap.toContinuousLinearMap T.rollX); let P:=f ∘ L
     have hh:= ((show ContDiffAt ℝ ω f (L 0) from L.map_zero.symm ▸ (A.fullK 1).plot n).comp _ L.contDiff.contDiffAt); rw [show muralFace H A T=(4:ℝ)⁻¹ • P from funext fun i=>by rw [Pi.smul_apply,smul_eq_mul,mul_comm]; exact div_eq_mul_inv ..,iteratedFDeriv_const_smul_apply (hh.of_le le_top)] -- names
     rw [Next.Foundations.jets_linear L (((A.fullK 1).plot n).of_le le_top)]; change (4:ℝ)⁻¹ * iteratedFDeriv ℝ 2 _ _ (L∘![x,y])=_; rw [show _∘![x,y]=![L x,L y] from funext fun i=>by fin_cases i<;>rfl,A.inkTot h n]; change _=(dotProduct _ _)/_; rw [mul_comm]; exact (div_eq_mul_inv ..).symm
-- normalized statement
lemma bears_local (h:G.Simple)(T:Plot H)(hx:4 ≤ i){f w:TK →ℝ}(b:ℝ)(hp:f=ᶠ[𝓝 0] fun i=> mural H A i-mural H A 0)(hf:Measurable f)(hw:w =ᶠ[𝓝 0] tintT H A b)(hL:Measurable w): ∃ L:Lid G T.Free,L.f=f ∘ T.rollX ∧ L.w=w ∘ T.rollX:=by
    let B: Keys G T.Free→L[ℝ] TK:= LinearMap.toContinuousLinearMap T.rollX; let u:= f∘B; let v:= w∘B; have hb:= B.continuous; have hq:Tendsto B (𝓝 0) (𝓝 0):= B.map_zero ▸ hb.tendsto 0
    have hu0 := tracksW H A b hp hw
    have hu : u =ᶠ[𝓝 0] muralFace H A T-fun _=> mural H A 0:= hp.comp_tendsto hq
    have he: (u 0)=0:=by unfold u; rw [Function.comp_apply,B.map_zero,hp.eq_of_nhds,sub_self]
    have hU:Radial.Stationary u:=⟨((B.map_zero.symm ▸ hu0.sane : ContDiffAt ℝ ∞ f (B 0)).comp _ B.contDiff.contDiffAt),he,fun i=> by unfold Radial.jet; rw [iteratedFDeriv_one_apply,hu.fderiv_eq, fderiv_sub ((mural_arc H A T).differentiableAt (by simp)) (differentiableAt_const _),mural_zero H A T h,fderiv_const_apply]; simp⟩
    have hW:0 < v 0:=by change 0<w (B 0); rw [B.map_zero,hw.eq_of_nhds]; apply Real.exp_pos
    refine ⟨⟨u,hU,hf.comp hb.measurable, Radial.quadratic_min u ?_,v,hW, (B.map_zero.symm ▸ hu0.warm : ContDiffAt ℝ ∞ w (B 0)).comp _ B.contDiff.contDiffAt,hL.comp hb.measurable⟩,rfl,rfl⟩
    intro i hi; unfold Radial.jet; rw [(hu.iteratedFDeriv ℝ 2).eq_of_nhds,iteratedFDeriv_sub_apply ((mural_arc H A T).of_le le_top) contDiffAt_const]; convert mul_pos (show 0< ((2:ℕ).factorial:ℝ)⁻¹ from by positivity) (show 0< iteratedFDeriv ℝ 2 (muralFace H A T) 0 ![i,i] from by rw [delta_arc H A T i i hx]; exact div_pos (rankcost H T i _ A hx hi (by rfl)) (by norm_num)) using 2
    · rfl
    simp [iteratedFDeriv_const_of_ne,show (fun _ :Fin 2=>i)=![i,i] from funext fun i=>by fin_cases i<;>rfl]
end YM.OPE.Cascade
