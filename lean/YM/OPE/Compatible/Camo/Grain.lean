import YM.OPE.Compatible.Camo.Lore
/-! # homogeneous controls leading. Δ crossing algebra. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cameo
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {V E:Type}{r s t c x C D:ℝ}{i j k:ℕ}
open Silt Cloud Tensor PertExtension Flume Flume.Page Flume.Script Jargon Score Drift GaussianScore Series Libra Shell Char Spells Radial Stranded Ibis Borealis Borealis.Galea Borealis.Lav
variable [NormedAddCommGroup E][NormedSpace ℝ E] [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]{μ:Measure E}[μ.IsAddHaarMeasure]{A:Law E}{p q W:E→Token}
-- explicit.W.δ
abbrev tariff (t:ℝ) (p:E→Token): E→ℝ:= fun i=>(p i).atK t
private lemma γTar (x:Token)(t:ℝ) : x.atK t = x.seq (0:Phase).val + t*x.seq (1:Phase).val+t^2*x.seq (2:Phase).val :=rfl
abbrev priceW (w:ℝ):= (1+‖w‖+‖w^2‖)
lemma Bouquet (w:ℝ)(he:∀ i:Phase, Spectre A μ (skry p i) k t): Spectre A μ (tariff w p) k (priceW w*t):=by
       let f(i):= skry p i; have hv:= ((he 0).scored ((he 1).weight w)).scored ((he 2).weight (w^2)); rw [show tariff w p=f 0+w • f 1+w^2 • f 2 from funext fun _=> γTar ..]; apply hv.widen; exact le_of_eq (by unfold priceW; ring)
omit [MeasurableSpace E][FiniteDimensional ℝ E][BorelSpace E] [NormedSpace ℝ E][NormedAddCommGroup E] in lemma TarSub (w:ℝ): tariff w (p-q)=tariff w p-tariff w q:=funext fun _=> BetaN ..
where BetaN (x y:Token)(w:ℝ):(x-y).atK w=x.atK w-y.atK w:=by rcases x with ⟨a,b,c⟩; rcases y with ⟨d,e,h⟩; change a-d+w*(b-e)+w^2*(c-h)=a+w*b+w^2*c-(d+w*e+w^2*h); ring
lemma SWeld (w:ℝ)(f q p s b:E→ℝ)(h:Spectre A μ (p-s) k 0)(hp:Spectre A μ (q-f) k 0)(hq:Spectre A μ (f-b) k t)(he:Spectre A μ (p-w • q) k r): Spectre A μ (s-w • b) k (r+‖w‖*t):=by
       let g:=w • p; have hs : Spectre A μ (q-b) k t:=by rw[show q-b=q-f+(f-b) from by abel]; exact (hp.scored hq).widen (le_of_eq (zero_add _))
       rw [show s-w • b=p - w • q-(p-s)+w • (q-b) from (by rw[smul_sub];abel), sub_eq_add_neg (p- w • q)]; exact ((he.scored h.minus).scored (hs.weight w)).widen (by rw [add_zero]); -- name minus simp
omit [MeasurableSpace E][BorelSpace E] in lemma Ŝm {p:E→ℝ}(h:Stature p 0)(w:ℝ):Stature (w • p) 0:= (Stature.poly (Bond.keep w) 0).mul h
omit [MeasurableSpace E][BorelSpace E] in
lemma freightS (w:ℝ)(h:Status p): Stature (tariff w p) 0:=by
       let f(i):= skry p i; rw [show tariff w p=f 0+w • f 1+w^2 • f 2 from funext fun _=> γTar ..]; exact ((h 0).add (Ŝm (h 1) _)).add (Ŝm (h 2) _) -- name
end YM.OPE.Cameo
