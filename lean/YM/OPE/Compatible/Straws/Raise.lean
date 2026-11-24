import YM.OPE.Compatible.Straws.Plump
/-!
# Gauged parameterized fiber integration. No borrowed hypotheses
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision Cascade Cascade.Pilot Arc Adhesion Flock Coin
open Radial ScriptJ JetS
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E] [BorelSpace E]
variable {D I:Type}[Fintype D][Fintype I]{G:Gauge}
local notation "Lf" => Tested.germ
local notation "Y!" => Keys G I
local notation "K!" => Keys G (D ⊕ I)
local notation "U!" => Keys G D
local notation "BL" => prL (Equiv.refl (D ⊕ I)) G
local notation "BR" => prR (Equiv.refl (D ⊕ I)) G
namespace Fiber
open Stranded Shift Glass
variable {F:Fiber E G I}{X Y:Path E G D}{p:Keys G D→ℝ}(Z:F.SeriesUp X p)(B:F.SeriesUp Y p) {P:ChartRatio G}(R:LocalRatio P)
namespace SeriesUp
local notation "ν0"=> camp F X
local notation "μπ"=> Chart.tangent G D
local notation "ωμ"=> Chart.tangent G I
local notation "JΘ" => crossT ωμ F.Q
local notation "μ0"=> cloth F P
-- controls unfolded fibres. no vacuum normalization ambiguity in conditional net
structure Raiser (Ω:Dimes G (D ⊕ I) (D ⊕ I)):Prop where
     coins : Ω.Mint Z.C B.C
     trim : ∀ᶠ t: Keys G (D⊕I) in 𝓝 0,BL (Ω.gradient t)=BL t
include R
variable {Ω:Dimes G (D ⊕I) (D ⊕I)}
omit [BorelSpace E] in
lemma crux (K:Raiser Z B Ω)(q w:ScriptJ K!)(hq:q.B)(hw:w.B)(h:Ω.pulse q w)(x:ScriptJ U!)(hp:x.B):
     draw (x*Z.netJet P q) Z.Z μπ= draw (x*B.netJet P w) B.Z μπ:=by
          let f:=x ∘ BL; have ht:ScriptJ.B f:=fun i=>(hp i).compLinear (BL).toLinearMap; rw [← rateN Z R q hq x hp,← rateN B R w hw x hp]; apply Ω.congr_charge K.coins.borders (ScriptJ.height ht hw) _ R; intro i
          let a(t:ℝ):= Ω.gradient (t•i); have hu:= h i; unfold Dimes.pulse at h; change Reads (fun t=> _ ) (f i*q i); let g(t:ℝ):=w (t⁻¹ • a t); -- merge: evaluate **token product** along Gael g bounded
          have hg: Gael (fun t:ℝ=> t⁻¹ • a t):= Gael.walk a ((show ContDiffAt ℝ ∞ Ω.gradient ((0:ℝ) • i) from by rw [zero_smul]; exact Ω.gradC).comp (f:=fun t:ℝ=> t • i) 0 (contDiffAt_id.smul contDiffAt_const)) (by simp [a])
          have he: Fitted g:= Fitted.arose _ _ hg hw; let s:ℝ→Token:=fun _=> f i; have hs: Fitted s:=⟨⟨_,Reads.constants (f i).s⟩,⟨_,Reads.constants (f i).l⟩,⟨_,Reads.constants (f i).h⟩⟩; rw [← show mine g= _ from he.take.equality hu,←show mine s=f i from Gael.chooses (Reads.selves _),←Fitted.slopes hs he]; apply (Fitted.duty hs he |>.take).cong
          have H:Tendsto (fun t:ℝ=>t•i) Lf (𝓝 0):=by simpa only [ContinuousWithinAt,zero_smul] using! (show Continuous (fun t:ℝ=>t•i) from continuous_id.smul continuous_const).continuousAt.continuousWithinAt (x:=0) (s:=Set.Ioi 0)
          filter_upwards [H.eventually K.trim,Tested.eventually_pos] with t hv (ht:0<t); let v:= t⁻¹ • Ω.gradient (t • i)
          change (x (BL v)*w v).atK t=(x (BL i)*w v).atK t; rw [show BL v= BL i from by unfold v;rw [map_smul,hv,map_smul,inv_smul_smul₀ ht.ne']]
omit [BorelSpace E] in
lemma optic (K:Raiser Z B Ω)(q w:ScriptJ K!)(hq:q.B)(hw:w.B)(h:Ω.pulse q w): Z.netJet P q=B.netJet P w:=by
     let π:= Chart.tangent G D
     have hp : Ω.pulse 1 1:= fun i=> Reads.selves _; let z:=Z.netJet P q;let s:=B.netJet P w
     have hu(A:Path E G D)(T:F.SeriesUp A p)(i:U!): (T.netJet P 1 i).s=1:=by unfold netJet; rw [ml_s,sp_s,T.seedBase R,inv_one,one_mul]; unfold dessert; rw [one_mul]; exact headD ωμ F.Q _ fun j=> T.C.hat_full R _
     have hr(x:U!→ℝ)(hp':Bond x) : Z.Z.average π x=B.Z.average π x:=by
          have he:= congr_arg JetS.s (crux Z B R K 1 1 (Bfray (E:=K!) _) (Bfray _) hp (low x) (lower hp')); simpa only [draw,Pi.mul_apply, JetS.ml_s,hu X Z,hu Y B, low,mul_one] using! he
     have hh:ScriptJ.B z:=nett Z R q hq; have hf:ScriptJ.B s:=nett B R w hw; apply levelJet μπ Z.Z z s hh hf; intro r hb; rw [mul_comm (low r) s,mul_comm s,show draw (low r*z) _ _= _ from crux Z B R K q w hq hw h _ (lower hb)] -- instance
     have hz:= ScriptJ.height (lower hb) hf; apply JetS.eta; exact (hr _ (hz 0)).symm; exact (hr _ (hz 1)).symm; exact (hr _ (hz 2)).symm
end SeriesUp
end Fiber
end YM.OPE.Libra
