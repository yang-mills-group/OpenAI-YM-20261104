import YM.OPE.Compatible.Tony.Awn
/-! # Wt derivative support . Executive note χ.Core. Care under storied campaigns. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL Flume.Page StepsL Wool
variable {i j d k m r l b:ℕ}{n:Side}
local notation "D!"=> Bid.Dir G n
section
private lemma tagNote {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] (x:E)(d:ℕ)(g:E→ℝ) (hp:ContDiffAt ℝ ω g 0) : jet g d x= ((d.factorial:ℝ)⁻¹)*iteratedDeriv d (fun t:ℝ=>g (t • x)) 0:= by exact (WardBin.leading_tensor x g (hp.of_le le_top)).symm
-- Warp Ψ projector from Suit$cur$ and eras at exponent.H.Setup!
open Next.Rank.Spindle
lemma holds_P (G:Gauge)(d:ℕ):∃ C:ℝ,0 ≤ C∧∀ b n,∀ h:Board n b, ∀ (f:Bid.Dir G n→ℝ)(p:ℝ),ContDiffAt ℝ ω f 0→
        (∀ i,i ≤ d→ ‖iteratedFDeriv ℝ i (f ∘ (tellerT G n).toContinuousLinearMap) 0‖ ≤ p)→∀ x:Bid.Dir G n,Roster x ≤1 → ‖jet (f ∘ Λace G h) d x‖ ≤ C*(1+(b:ℝ))^(2*d)*p :=by
        choose B hB H using fun j=>pier_c G j; let V:=1+∑ i∈range (d+1),B i; have he : 1 ≤ V:=le_add_of_nonneg_right (sum_nonneg fun i _=>hB i); let a:= (d.factorial:ℝ); have ha:0<a:=(by unfold a; positivity); refine ⟨V^d,pow_nonneg (zero_le_one.trans he) _,fun b n h f p hv hx x hR=>?_⟩
        let U:=(tellerT G n).toContinuousLinearMap; let q:= f ∘ U; let T:= f∘ Λace G h; let z(y:ℝ):= (tellerT G n).symm (Λace G h (y • x)); have hz:z 0=0:=by unfold z; rw[zero_smul,eΛ,map_zero]
        have hY:Λace G h 0=0:= eΛ ..; have hl : ContDiffAt ℝ ω (Λace G h) 0:= haloStage h G; have hq: ContDiffAt ℝ ω T 0:= (hY.symm ▸ hv : ContDiffAt ℝ ω f (Λace G h 0)).comp (f:=Λace G h) 0 hl
        have hh :ContDiffAt ℝ ω z 0:=by unfold z; exact (tellerT G n).symm.contDiff.contDiffAt.comp (f:=fun t:ℝ=> Λace G h (t • x)) 0 ((show ContDiffAt ℝ ω (Λace G h) ((0:ℝ) • x) from by rw [zero_smul]; exact hl).comp (f:=fun t:ℝ=>t • x) 0 (by fun_prop))
        have hr: ContDiffAt ℝ (d:WithTop ℕ∞) q (z 0):=hz.symm ▸ (((show ContDiffAt ℝ ω f (U 0) from U.map_zero.symm ▸ hv).comp (f:=U) _ U.contDiff.contDiffAt).of_le le_top)
        let s:=1+(b:ℝ); let c:=V*s^2; let S:= strap z q 0 d (hh.of_le le_top) hr p c (by intro i hi;rw[hz]; exact hx i hi) (fun i hp hv=>?_); swap
        · apply (H i b n h x hR).trans; unfold c; rw[mul_pow,←pow_mul]; refine mul_le_mul_of_nonneg_right ?_ (by positivity); exact (single_le_sum (f:=B) (fun j _=> hB j) (s:=range (d+1)) (mem_range.mpr (by omega))).trans ((le_add_of_nonneg_left zero_le_one).trans ((pow_one V).symm.trans_le (pow_le_pow_right₀ he hp)))
        rw [tagNote x d T hq, show (fun t:ℝ=> T (t • x))=q ∘ z from funext fun i=>congr_arg f ((tellerT G n).apply_symm_apply _).symm]; rw [norm_mul,Real.norm_of_nonneg (inv_pos.mpr ha|>.le), ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]; apply (mul_le_mul_of_nonneg_left S (inv_pos.mpr ha|>.le)).trans_eq; rw[show c^d=V^d*s^(2*d) from by unfold c; rw [mul_pow,← pow_mul]]; change a⁻¹ * (a * _ * _) = _; field_simp; unfold s; ring
end
namespace Sleeve
variable {I:Type}{A:I→ Side} {φ:Filter I}{Z:I→ℝ}{b:I→ℕ}{f:GlyphQ G A}
structure Photos (φ:Filter I)(Z:I→ℝ)(a:ℝ)(x:GlyphQ G A):Prop where
       cost :∃ c:I→ℝ,RateLE φ Z c a∧∀ᶠ i in φ,∀ t:Bid.Dir G (A i),Roster t≤ 1→ ‖x i t‖ ≤ c i
variable {a:ℝ}{p q:GlyphQ G A}
lemma Photos.cone (h:Photos φ Z a p)(hv:∀ᶠ i in φ,p i=q i): Photos φ Z a q:=by obtain ⟨c,hc,H⟩:=h.cost; exact ⟨_,hc,(H.and hv).mono (fun i hi=>hi.2 ▸ hi.1)⟩
lemma Photos.green (h:Photos φ Z a p)(hv:Photos φ Z a q)(he:Tendsto Z φ atTop): Photos φ Z a (p+q):=by obtain ⟨c,hc,H⟩:=h.cost; obtain ⟨d,hd,K⟩:=hv.cost; exact ⟨_,hc.add hd he,(H.and K).mono fun i hi x hx=> (norm_add_le ..).trans (add_le_add (hi.1 x hx) (hi.2 x hx))⟩
lemma Photos.sink (h:Photos φ Z a p)(hv:Photos φ Z a q)(he:Tendsto Z φ atTop): Photos φ Z a (p-q):=by obtain ⟨c,hc,H⟩:=h.cost; obtain ⟨d,hd,K⟩:=hv.cost; exact ⟨_,hc.add hd he,(H.and K).mono fun i hi x hx=> (norm_sub_le ..).trans (add_le_add (hi.1 x hx) (hi.2 x hx))⟩
structure Rated (φ:Filter I)(Z:I→ℝ)(a:ℝ)(p:GlyphQ G A): Prop where
       beam (k:ℕ): RateLE φ Z (fun i=>‖iteratedFDeriv ℝ k (p i ∘ (tellerT G (A i)).toContinuousLinearMap) 0‖) a
noncomputable abbrev Article (p:GlyphQ G A)(k:ℕ):GlyphQ G A:= fun i=>jet (p i) k
lemma Rates.toy (hp:Rated φ Z a p)(h:∀ᶠ i in φ, ContDiffAt ℝ ω (p i) 0)(hv:Tendsto Z φ atTop): Photos φ Z a (Article p k):=by
       refine ⟨fun i=>‖(Tensor.coeff (p i ∘ (tellerT G (A i)).toContinuousLinearMap) k 0)‖,?_,?_⟩; · let v:= hp.beam k; unfold Tensor.coeff; simp_rw[norm_smul]; exact ((RateLE.const _ hv).mul v).mono (by simp)
       refine h.mono fun i hi x hx=>?_; let y:=(tellerT G (A i)).symm x; let S:= (tellerT G (A i)).toContinuousLinearMap; rw [show Article p k i x=jet (p i ∘ S) k y from ?_]; rotate_left; · exact (show jet (p i ∘ S) k y= _ from (congr_arg JetS.s (congr_fun (moldC S _ hi _) _))).symm ▸ (congr_arg (jet (p i) k) ((tellerT ..).apply_symm_apply x)).symm -- need syntax
       refine ((Tensor.coeff (p i ∘ S) k 0).le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) (prod_le_one (fun _ _=>norm_nonneg _) (fun _ _=>hx)))
end Sleeve
end YM.OPE.Merchant
