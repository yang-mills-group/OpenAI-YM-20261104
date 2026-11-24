import YM.OPE.Compatible.Melon.Burd
/-!
# Relative hat at first order. The cubic which will be averaged kills. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Glass
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace ENNReal
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial Flock Metric
attribute [local instance] Gauge.frobInner
variable {i:ℕ}{l b:ℝ}{B:Sponsor G}{Q:Seasons B} {A:Alps B Q i l} {H: Even n.val}
local notation "Lf" => Tested.germ
local notation "TK" => Keys G (Limb H)
variable (T:Plot H) (X:Lit H A b) (R:Bor H A b)
local notation "DK" => Keys G T.Stable
local notation "FD" => Keys G T.Free
local notation "W" => Chart.tangent G T.Stable
local notation "Tμ" => Chart.tangent G T.Free
local notation "Pμ" => Chart.tangent G (Limb H)
variable {P:ChartRatio G}(V:LocalRatio P){I:Type}[Fintype I]
include V
lemma tap_jac (x:Keys G I): jet (Chart.jacobian P) 1 x=0:=by
     let U:= Keys G I; let Xx:U→ℝ:= Chart.jacobian P; have he: Xx =ᶠ[𝓝 0] fun t=>Xx (-t):=by
        filter_upwards [Metric.ball_mem_nhds (0:Keys G I) V.patch] with t ht; refine Finset.prod_congr rfl fun i _=> ?_; unfold Chart.fee; rw [Next.SectorChange.ratio_even V (show t i ∈ Metric.ball 0 P.radius from (by rw [ball_pi _ V.patch] at ht; exact ht i (Set.mem_univ _)))];rfl
     let L:= - ContinuousLinearMap.id ℝ U; have hh : ContDiffAt ℝ (↑(1:ℕ):WithTop ℕ∞) Xx 0:= (Chart.Ratio.jacobian_smooth V).of_le le_top
     have ht:= Next.Foundations.jets_linear L hh; have hp : Xx=ᶠ[𝓝 0] Xx ∘ L:= he; change jet Xx 1 x=0
     have he: jet Xx 1 x=(-1:ℝ)^1*jet Xx 1 x:=by
         rw [← jet_smul Xx 1 (-1)]; conv_lhs=> unfold jet; rw [(hp.iteratedFDeriv ℝ 1).eq_of_nhds,ht]
         change _ * iteratedFDeriv ℝ 1 Xx 0 (fun _ : Fin 1 => L x) = _; rw [show L x=(-1:ℝ) • x from by simp [L]];rfl
     linarith
lemma warmLogo (x:Keys G I)(D:Lid G I): jet (warmer P D.w) 1 x= jet D.w 1 x * Chart.jacobian P (0:Keys G I) :=by
     let L:=Chart.jacobian P (U:=I)
     have hp : Reads (fun t:ℝ=> warmer P D.w (t•x)) (Pawn.mold D.w 0 x*Pawn.mold L 0 x) := ((Pawn.calm D.coat).stale x).pile ((Pawn.calm ((Chart.Ratio.jacobian_smooth V).of_le le_top)).stale x)
     have hv : (Pawn.mold (warmer P D.w) 0 x).l= _:= congr_arg JetS.l (((Pawn.calm (D.winds P V)).stale x).equality hp); change jet (warmer P D.w) 1 x= jet D.w 0 x*jet L 1 x +jet D.w 1 x*jet L 0 x at hv; rw [hv,show jet L 1 x= _ from tap_jac V x,jet_zero,mul_zero,zero_add,jet_zero]
lemma coldPeak (x:Keys G I)(D:Lid G I): (D.hat P x).l=jet D.w 1 x / D.w 0 -jet D.f 3 x:=by
     have hp: D.w 0 ≠ 0:= D.charm.ne'; have hx: Chart.jacobian P (0:Keys G I)≠0:= (ne_of_apply_ne (f:=fun t=> D.w 0*t) (by rw [mul_zero]; exact (D.seed_pos V).ne')) -- name
     unfold Lid.hat Lid.heat; rw [JetS.ml_l,JetS.plain_l,JetS.plain_s, zero_mul,add_zero,Pi.mul_apply,JetS.ml_l]; change (warmer P D.w 0)⁻¹*(jet (warmer P D.w) 0 x*(-jet _ 3 x)+jet (warmer P D.w) 1 x*1)=_; rw [jet_zero,mul_one,warmLogo V x D,show warmer P D.w 0=_ from (show warmer P D.w 0=D.w 0*Chart.jacobian P 0 from rfl)]; field_simp;ring
lemma hotRead (x:FD)(y:DK)(h:4 ≤ i): ((ballow T X h).hat P (compass H T G (x,y))).l=((R.L T).hat P x).l -jet (tall T) 3 (compass H T G (x,y)):=by
     rw [coldPeak V,coldPeak V, wornN T X R,glowN T X R]; simp_rw [firstC]; rw [show (ballow T X h).w 0=(R.L T).w 0 from Eq.trans (path_fall T X R |>.eq_of_nhds) (by rw [_root_.Function.comp_apply,map_zero])]; ring
end YM.OPE.Cascade.Glass
