import YM.OPE.Compatible.Oasis.Ball
import YM.OPE.Compatible.Kyoto.Ploy
import YM.OPE.Compatible.Kyoto.Team
import YM.OPE.Compatible.Kyoto.Cloud
import YM.OPE.Compatible.Kyoto.Gazer
import YM.OPE.Compatible.Kyoto.Opal
import YM.OPE.Compatible.Kyoto.TreeQ
import YM.OPE.Compatible.Ice.Ares
import YM.OPE.Compatible.Nut.Hero
import YM.OPE.Compatible.Silva.Bride
import YM.OPE.Compatible.Kyoto.Room
/-!
# Fine and coarse clocks for a matched lattice step

`Uniform` fixes the target and constants for a patch. `Aud` records
the fine and coarse clock tags, their fees, the fare discrepancy,
and the pushforward of the fine evaluation. For times tending to
infinity with these conditions eventually satisfied, `vigour` gives
`Chase` and `spikeY'` gives the exact rate one for the time parameter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J :Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}

variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full GlowPack Yolk Pipes Dial Raucous Zeph Zeph.Dew Borealis Flume.Script 
open Next.Free
section
variable {L:PriceBook H T}{a:Axis}
namespace MatchZ

section
open Lass.Zest Lass PhysicalNext.Repeat.Aroma Pressure ConnectedActivityE6 Shell Channel
variable {Ξ:Medal P' G K.K P'.J} {P₀:Teller G}
variable {E:ConnectedActivityE6.Target G P₀} {Q:Side}{W C κ:ℝ}{o:ConnectedActivityE6.Target.Order G W}
variable (F:I→Mug P' p p' T j R Ξ)
variable {Q:ℕ}
open Limn CardinalQ Labels Source Cameo Spells Yolk Pill

structure Uniform (G:Gauge)(B:Patch) where
        TellerQ: Teller G
        E : ConnectedActivityE6.Target G TellerQ
        κ : ℝ
        o :Σ W:ℝ, ConnectedActivityE6.Target.Order G W 
        C :ℝ
        n:ℕ
        (Δ σ0 σ1 γ M0 : ℝ)
        predB : B.Branches TellerQ.bind G 
        fro : PhysicalNext.Repeat.Daisy.foam E B.L
        e' : 0 < E.exp
        e0:0<κ
variable (F':Uniform G P')
abbrev now (b:ℝ)(G:Gauge)(Q:Patch):= b+Δfare G Q.L
variable (M : Mug P' p p' T j R Ξ)
abbrev Pillar (_x:ℝ):= Wall P' F'.E P'.L F'.o.2 F'.κ F'.C F'.n M.hostS 
local notation "PS"=>Stage
-- The two stage tags apply at the shifted fine time and the unshifted coarse time.
structure Aud (T1 T2:Stage)(x:ℝ) (t:Pillar F' M x) : Prop where
        montage : (t.model).Ready
        moment : t.time=x
        clock : CardinalQ.Tag T1 (now x G P') M.pW.p M.pW.beta ∧ CardinalQ.Tag T2 x M.pV.p M.pV.beta
        core : M.row.fine.fees=capL F'.σ0 (now x G P') ∧ M.row.coarse.fees= capL F'.σ1 x
        flare : |M.row.fare| ≤ F'.γ
        tall: θj x^2*|M.pV.beta - M.pW.beta - M.row.fare| ≤ F'.Δ * ℰb x
        scope : M.pV.eval=M.hostS.Z.push M.pW.beta M.pW.eval
variable {Y Wσ:I→ℝ} {l₀:Filter I}{T1 T2:Stage}
variable (t:∀ i, Pillar F' (F i) (Y i))(h:Tendsto Y l₀ atTop)(hx:∀ᶠ i in l₀,Aud F' (F i) T1 T2 (Y i) (t i))
include h hx
lemma vigour: Chase (Eve t) l₀:=by
       exact ⟨F'.predB,F'.fro,F'.e',F'.e0,h.congr' (hx.mono fun i hi=>hi.moment.symm),hx.mono fun _ hi=> hi.montage⟩
omit h in lemma tickX :βM (Eve t)=ᶠ[l₀] (fun i=> now (Y i) G P'):=hx.mono fun _ hi=> congr_arg (fun x=> now x G P') hi.moment
lemma spikeY' : RateIs l₀ (fate (Eve t)) Y 1:=by
       apply Pill.Shell.Ray _ (vigour _ _ _ h hx).high; refine ⟨1/2,2,(by norm_num),(by norm_num),?_⟩ ; let v:=Δfare G P'.L; filter_upwards [tickX _ _ _ hx, h.eventually_ge_atTop |v|,h.eventually_ge_atTop (2*|v|)] with i hi hh hk; rw [hi]; change 1/2*(Y i+v) ≤ _ ∧ _ ≤2*(Y i+v); exact ⟨by linarith only [hh,le_abs_self v],by linarith only [hk,neg_le_abs v]⟩
end
end MatchZ
end
end YM.OPE.Stroke
