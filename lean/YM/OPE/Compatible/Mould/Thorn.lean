import YM.OPE.Compatible.Mould.Tray
/-!
# Suppressed ideal.Debug radical all rays. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
local notation "Λ"=> Variance.SailSap
abbrev OmegaPhi (A:Alps K T i v)(hp:4 ≤ i)(hX:0≤v):Submodule ℝ (Tracts G d τ):=
     (Λ A H hp hs hX P a l).comap (Fallix G D₀.aware K A.gear hp).toLinearEquiv.toLinearMap
variable {u ν:M→ℝ}{hp:4 ≤ i}{V:(j:M)→Alps K T i (u j)}
namespace Topic
local notation "O!"=> Quoin hs D₀ B H
local notation "X!"=>Mint Z e
lemma tallη (v':Even n.val)(x y:Site n)(t:Phase) : Sky ((lapPrice P.L e)*(lapPrice P.L e)) 6 (fun i=>Por Hp Z e t v' x y a i (0:Mint Z e) 0) := sunV H hs X Z.station D₀ (spose a G d τ) (ContinuousLinearMap.id ℝ (solar G d τ)) v' x y Hp .. -- maybe omit
noncomputable def UnitBorn (H':Even n.val)(x y:Site n)(t:Phase)(i:ℕ): X!→ₗ[ℝ] X!→ₗ[ℝ] ℝ:= (antique (E:=Tracts G d τ) Z.station (lapPrice P.L e) 3 i (K0 (e:=e) H hs X Z.station D₀ a H' x y Hp t)).choose
lemma flareP(p q:X!)(H':Even n.val)(x y:Site n)(t:Phase)(j:ℕ):Por Hp Z e t H' x y a j p q=UnitBorn Hp Z a H' x y t j p q:=((antique (E:=Tracts G d τ) Z.station (lapPrice P.L e) 3 j (K0 (e:=e) H hs X Z.station D₀ a H' x y Hp t)).choose_spec p q).symm
abbrev Kneel (p:X!):Prop:=∀ (n:Side)(H':Even n.val)(x y:Site n)(_h:barrier P ≤ n.val),Pins K P x y→∀ i t q,let f:= UnitBorn Hp Z a H' x y t i; f p q=0∧f q p=0
set_option maxHeartbeats 200000 in
noncomputable def Dross (e:ℕ):Submodule ℝ (Mint Z e):= D₀t (E:= ↥(Fruition Z.station (lapPrice P.L e))) (M:=Phase) (fun _ H' x y i t => UnitBorn (e:=e) Hp Z a H' x y t i) (barrier P) P K
lemma sapUp {t:Tracts G d τ}{A:Alps K T i v}(hp:4 ≤ i)(hx:0≤v)(h:t∈ OmegaPhi (H:=H) (hs:=hs) (D₀:=D₀) a A hp hx): Gift G D₀.aware t∈ OmegaPhi (H:=H) (hs:=hs) (D₀:=D₀) a A hp hx:=by
      refine Submodule.mem_comap.mpr ?_; let F:=Fallix G D₀.aware K A.gear hp; change F _∈ Λ A H hp hs hx P a l; unfold F;rw[Flick]; exact Variance.fuel A H hp hs hx P _ a h D₀.aware
end Topic
end YM.OPE.Stroke
