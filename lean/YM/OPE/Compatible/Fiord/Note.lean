import YM.OPE.Compatible.Fiord.Merid
import YM.OPE.Compatible.Mason.Zeal
import YM.OPE.Compatible.Camo.Hilt
import YM.OPE.Compatible.Fiord.Rein
/-!
# Marginal plans. True relative density jets, *before* normalization
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.OPE.Owl.HillZ
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG Gauge Precision
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ENNReal ContDiff
open Eyrie Push Push.AbsoluteSums Push.Mark Cascade Flume Flume.Page Flume.Script Pilot Finset
open Silt Libra Coin Rill Silt.Float Votive PertExtension Series GaussianScore Radial Next.Foundations
open Merchant Merchant.Aloof Merchant.Sleeve Merchant.SiteL
open Next.Free Next.Scheduling Stroke Spells Lass Lass.Zest Pill CardinalQ
variable {I:Type}{φ:Filter I}{G:Gauge} {K:Sponsor G}{T:Seasons K}
variable {β:I→ℝ}{n:I→Side}{S:Stage}{i j d r k:ℕ}{τ s a B:ℝ}
variable (A:∀ x:I,HillZ (T:=T) S i r d τ (β x) (n x))(U: Scaffold φ (Counters β) n (Mnd i S A) r)
variable (D:I→ Law (Merchant.Chamber G r))(hs:G.Simple)
open Merchant.SiteL
variable (h:Tendsto β φ atTop)(hD: GaugeD A U D)
open Cinders Metric Set Zeph Jargon Crown PertExtension Flock Stranded
variable {N:ChartRatio G} {s c R:ℝ} (H:StackP N s c R)(hN:LocalRatio N)
variable (x:∀ i,Bid.Dir G (n i)) (g:ℂ→L[ℝ]ℝ) (P:Pad G)
open Ibis Jargon Crown Exterior Silt.Phere Paver
variable (hz:4 ≤ i)
open Silt.Phere Jargon Crown Paver Cloud Stranded Merchant.SiteL Libra.Shift ScriptJ Drift
local notation "TC"=> Merchant.Chamber G r
open Borealis Borealis.Lav Cameo Claw Libra.Char Variance
local notation "Tc"=> Merchant.Chamber G r
-- exact whole moments. Avoid comparing Wick P product density instance. Status houses. formal atK complete
section
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
omit [FiniteDimensional ℝ E] in lemma puffP_add (p q:E→Token)(hp:Status p)(he:Status q): Status (p+q):=by intro j; fin_cases j <;>first|exact (hp 0).add (he 0)|exact (hp 1).add (he 1)|exact (hp 2).add (he 2)
omit [FiniteDimensional ℝ E] in lemma puffP_sub (p q:E→Token)(hp:Status p)(he:Status q): Status (p-q):=by intro j; fin_cases j <;>first|exact (hp 0).sub (he 0)|exact (hp 1).sub (he 1)|exact (hp 2).sub (he 2)
variable [MeasurableSpace F][BorelSpace F](A:Law F)(ν:Measure F)[ν.IsAddHaarMeasure]
omit [FiniteDimensional ℝ E] in
lemma Boν (f:E×F→Token)(hp:Status f) (x:E)(t:ℝ): tariff t (crossT ν A f) x= ∫ y, (f (x,y)).atK t ∂quart A ν:=by
        let F0(i:ℕ)(y:F):=(f (x,y)).seq i; let mes:= quart A ν; have hi(i:Fin 3):Stature (F0 i.val) 0:= stat_slice (hp i) x; have hh(i:Fin 3):Integrable (F0 i.val) mes:= Irite (Ppu A ν (hi i)); let p:= F0 0; let q:= F0 1; let z:= F0 2; have hs:Integrable (fun y=>p y+t*q y) mes:= (hh 0).add ((hh 1).const_mul _)
        have ht:Integrable z mes:=hh 2; have hp:Integrable p mes:=hh 0; have hg:Integrable q mes:=hh 1; change A.average ν p+t*A.average ν q+t^2*A.average ν z=∫ y,(p y+t*q y)+t^2*z y ∂mes; rw[integral_add hs (ht.const_mul _), integral_add hp (hg.const_mul _),integral_const_mul,integral_const_mul]; unfold mes; rw [has_p, has_p, has_p]
omit [FiniteDimensional ℝ E] in
lemma SaltShift (p q:E×F→Token)(hp:Status p)(hq:Status q): crossT ν A (p-q)=crossT ν A p-crossT ν A q:=eq_sub_of_add_eq (by rw[← Salt_add _ _ (puffP_sub p q hp hq) hq, sub_add_cancel])
omit [FiniteDimensional ℝ E] [NormedAddCommGroup E] [NormedSpace ℝ E] in
private lemma outsideB (p:E→Token)(f:E×F→Token)(x:E)(q:F→Token)(h:q=fun y=> f (x,y))(hp:ScriptJ.B q)(hz:draw q A ν=1):crossT ν A ((fun i=>p i.1)*f) x=p x:=by
        rw [crossT, show (fun y=>((fun i:E×F=>p i.1)*f) (x,y))=fun y=>p x*q y from h ▸ rfl, drips ν A q _ hp,hz,mul_one]
end
variable {τ':Phase→ℕ}{C V W:Forge G n}{H:Aware (d+6+6) τ'}
section
variable (hX:AcctΩ A U g P hz H C V W)
noncomputable abbrev Mouth (X: Forge G n)(N:ChartRatio G)(j:I):= (ΩReal A U D (Plato n) N j*wMirror A U D X j)
noncomputable abbrev marX (f:Forge G n)(N:ChartRatio G)(j:I) := crossT (Chart.tangent G (fieldP r)) (D j) (Mouth A U D f N j)
include hN hX
lemma Lodger :∀ᶠ i in φ, marX A U D W N i=W i:=by
       filter_upwards[ExtE A U D g P hz hX] with i hi; funext x; let ν:= Chart.tangent G (fieldP r); unfold marX Mouth; rw[mul_comm, show wMirror A U D W i=(fun v=> W i v.1) from funext hi]; obtain ⟨ht,hz⟩:= penJ A U D hN i x
       exact outsideB (D i) ν (W i) (ΩReal A U D (Plato n) N i) x (MonoΩ A U D N i x) rfl ht hz
omit hN hX
lemma handy (i:I)(X:Forge G n)(hp:Status (X i)): Status (Mouth A U D X N i):=by
       exact statusH (statusP (Mammon (A:=A) (U:=U) (D:=D) (N:=N) i)) (statusF hp (visor A U D i)) -- instance
end
end YM.OPE.Owl.HillZ
