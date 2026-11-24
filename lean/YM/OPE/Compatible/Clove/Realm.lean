import YM.OPE.Compatible.Waft.Dale
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.PriceZ
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
structure Scape (K:Sponsor G)(T: Seasons K)(P:Patch)(n f: Side) (i j:ℕ)(R:ChartRatio G) where
     A :ℝ
     B :ℝ
     b :ℝ
     b' :ℝ
     x:Alps K T i A
     y:Alps K T j B
     U:Boxes G P K.K
     α :ℝ
     joins : b'=b+α
     fee : TEX U x.clip y.clip x.live y.live α R
     dims:f.val=n.val*P.L.val
     t : (StepData.mk P K.K dims).Choices
     tH:Even n.val
     L : Matrix (Body 1 f) (Body 1 n) ℝ
     g: Bid.Dir G n→ AxisChart G (forest (StepData.mk P K.K dims).ratio P.odd_side)
     ok:ReadyV ⟨P,K.K,dims⟩ P.odd_side U x y L g
     E:Plot tH
     γ:Law (Keys G (Blocx (StepData.mk P K.K dims) P.odd_side tH))
     hx:Roomy ⟨P,K.K,dims⟩ P.odd_side tH U γ
     hv: Era U x
     Y : Elm x ⟨P,K.K,dims⟩ tH t b
     V : Bor tH y b'
namespace Scape
variable (x:Scape K T P n f i j R)
abbrev rungS := StepData.mk P K.K x.dims
abbrev VC:= Keys G (Stand.Free x.E)
abbrev power(x:Scape K T P n f i j R) (y:x.VC):= peakX x.rungS P.odd_side x.tH x.E x.g y
abbrev BootZ : Measure x.VC:=Chart.tangent G (Stand.Free x.E)
def vault (hs:G.Simple)(hr:LocalRatio R)(h:Aware d τ):Tower (Shade G) d τ→L[ℝ] Tower (Shade G) d τ:= actor x.x x.U R x.b ⟨hs,hr,x.hv⟩ h
local notation "L!"=> solar G d τ
abbrev upL (hs:G.Simple)(hr:LocalRatio R)(h:Aware d τ)(p:L!) : L! := ⟨x.vault hs hr h p.val,actors _ _ _ _ _ _ _ p.property⟩
def slot (p: L!)(a:Site n):= vic x.rungS P.odd_side x.tH x.E a p
lemma blotS (p:L!)(a:Site n):(x.slot p a).B:= vicB x.rungS P.odd_side x.tH x.E p a
abbrev EraL (Γ:ScriptJ (Keys G (Stand.Free (stroll x.rungS P.odd_side x.tH x.E)))): ScriptJ x.VC:=gatedB x.rungS P.odd_side x.tH x.E x.t x.Y x.g R x.γ Γ
abbrev storm':= Thunder x.rungS P.odd_side x.tH x.E x.t R x.V x.U x.g x.x
lemma poolB (hp: LocalRatio R){y}(hy:ScriptJ.B y): ScriptJ.B (x.EraL y):= Gates_B _ _ _ _ _ _ hp _ hy
lemma sunStorm (hp:LocalRatio R)(hs:G.Simple): ScriptJ.B x.storm':= ThunderB x.rungS P.odd_side x.tH x.E x.U x.t x.ok x.V x.Y hp x.hx _ x.fee x.joins.symm hs
abbrev campP:=actLight x.rungS P.odd_side x.tH G
abbrev cupsP (a:Site n)(u:L!)(y:x.VC):= cups (branchOut P G (spread G d τ u.val)) d a (x.power y) x.campP
abbrev castS (y:x.VC):= Stell (Char.Sketch (mintR x.rungS x.x R x.b) (1/4) (x.power y) x.campP)
abbrev ζ (y:x.VC):= fair (Chart.tangent G (Blocx x.rungS P.odd_side x.tH)) x.γ (x.castS y)
lemma gateZ (p:LocalRatio R)(hs:G.Simple)(y:x.VC)(a:Site n)(u:L!): x.EraL (x.slot u a) y=x.ζ y (x.cupsP a u y):=by
    unfold EraL; rw [strap x.rungS _ _ _ x.U x.t x.ok x.Y (C:=x.γ) p _ hs (blotS x u a)]; unfold ζ ; congr 1; funext v; exact parish x.rungS P.odd_side x.tH x.E x.U x.t x.ok ..
lemma gateL (p:LocalRatio R)(hs:G.Simple)(u v:L!)(i j:Site n)(y:x.VC): x.EraL (x.slot u i * x.slot v j) y=x.ζ y (x.cupsP i u y * x.cupsP j v y):=by
    unfold EraL; rw [strap x.rungS _ _ _ x.U x.t x.ok x.Y (C:=x.γ) p _ hs (height (blotS x u i) (blotS x v j))]; unfold ζ; congr 1; ext1 z; exact congrArg₂ (·*·) (parish x.rungS P.odd_side x.tH x.E x.U x.t x.ok ..) (parish x.rungS P.odd_side x.tH x.E x.U x.t x.ok ..)
lemma chartVal (u v:L!)(i j:Site n)(V':Bor (even_both x.rungS.ratio x.tH) x.x x.b)(Z:Plot (even_both x.rungS.ratio x.tH))(hp:LocalRatio R)(hs:G.Simple):
    RGram _ Z V' u v (x.rungS.ratio.embed i) (x.rungS.ratio.embed j) R= fair x.BootZ (penon (x.V.L x.E)) x.storm' (x.EraL (x.slot u i * x.slot v j)):=by
        let S:=x.rungS; let b:= cutφ (even_both S.ratio x.tH) u.val (S.ratio.embed i)*cutφ (even_both S.ratio x.tH) v.val (S.ratio.embed j); have hB: (Pond _).Marbles b:=prodMar _ (CloudH _ u _) (CloudH ..)
        change (V'.L Z).pay R (Z.charted b)= _; rw [← Elm.stank V' x.t _ x.Y hB Z (stroll S P.odd_side x.tH x.E) hp]; rotate_left
        · exact x.ok.1.1.cover
        let q:= x.slot u i*x.slot v j; exact rainy x.rungS P.odd_side x.tH x.E x.U x.t x.ok _ _ hp x.hx q (ScriptJ.height (blotS x u i) (blotS x v j)) _ x.fee x.joins.symm hs
end Scape
end YM.OPE.Quit.PriceZ
