import YM.OPE.Compatible.Munch.Solar
/-! # caps on all horizontal costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type}{i j k m n M:ℕ}{ε v t c r z u s e a β C R A D:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals
variable {K:Sponsor G}{T:Seasons K}
section
variable {L:Host K T}
lemma Seat_V (v:Train i)(h:4 ≤ i): 0≤ (terra_money K.K h).choose+1 ∧ PerSeat (L:=L) (Vessel K.K v G L.c h) ((terra_money K.K h).choose+1):=by
       let V:= Vessel K.K v G L.c h; let q:= flats G L.c; refine ⟨(rentV G v h K.K L.c).positive,fun j=>?_⟩; let a:= castAt (JetB G L.c) j; have hp: a=coQ q.toContinuousLinearMap (j.1.1,(j.1.2,j.2)):=by
             apply LinearMap.ext; intro x; change cash (Limn.Tip G _) x j= (flats G L.c x) (j.1.1,(j.1.2,j.2)); rw [flatX,Tip_ψ]; rfl
       change V.wick a a≤ _; rw [hp]; exact (Real.le_norm_self _).trans (cupV K.K v h _ _)
variable (x:Site L.f){q:Sender L}{B: Law (Bid.Dir G L.c)} (μ:Measure (Bid.Dir G L.c))[μ.IsAddHaarMeasure]
variable {N:ChartRatio G}(hN:LocalRatio N)(H:StackP N r R β)(η:Phase)(hs:G.Simple)(hw:L.b=0)(h:L.Rich s c e v u C)(ht:0<s)(hc:0≤c)(he:0<e)(hu:0≤ v) {X:Seats L.ForestQ}(hx:(X.card:ℝ)≤ z)(hX:Training L x X M)(hp:Funded L X q a k)(hφ:PerSeat (L:=L) B A)(hA:0 ≤ A)(hS:∀ J z a t:ℝ, Caver G k s c v u C t z a J β ≤ D*(1+(‖J‖+‖z‖+‖a‖))^n*(1+‖t‖)^n)(hD:0≤ D)
include h ht hc he hx hX hp hD hφ hA hN H hu hs hw hS
abbrev Ūfee (s:ℝ)(n M:ℕ)(z a:ℝ):= s*(1+(‖RtM M‖+‖z‖+‖a‖))^n
lemma Parad (i:ℕ): Cane (quart B μ) (Censor L q N η x i) (Ūfee D n M z a • hikeP (J1+crownG G i A) n):=by
       let P:= powerQ ((Cane.constant (μ:=quart B μ) (1:ℝ) (show ‖(1:ℝ)‖≤1 by norm_num)).add ((mac x B μ hφ hA i).normVal)) n; let E:=Ūfee D n M z a; have he':0≤E:=by unfold E Ūfee; positivity
       refine (of_K (P.scal E) (Continuous.aestronglyMeasurable ((R_status hN hp η).smooth.continuous.comp (Qspot L x i).continuous)) (fun w=>?_)).grow fun j _=>?_ ; · unfold Function.comp skry; let T:=Qspot L x i w; rw [tradeV hN L q h hw hs]; have hv : Scale (worldA L T) ‖T‖:= grantW le_rfl; have hh:= (SΔ x η h ht hc he hv hx hX hp hN H hu).trans (hS (RtM M) z a ‖T‖); rw [norm_norm] at hh; exact hh.trans (Real.le_norm_self _)
       rw [Real.norm_eq_abs E, abs_of_nonneg he']
end
end YM.OPE.Borealis.Galea
