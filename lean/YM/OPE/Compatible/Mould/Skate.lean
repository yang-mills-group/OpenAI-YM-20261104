import YM.OPE.Compatible.Mould.Gain
/-!
# Visibility criterion. polynomial Ward.Measure. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic JetS
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {u ν:M→ℝ}{hp:4 ≤ i}{V:(j:M)→Alps K T i (u j)}
namespace Topic
local notation "Q*"=> Mint Z e
-- Rank marker. scorcher.T cost pressure.
lemma WingS (V:Even n.val)(x y:Site n)(p q:Mint Z e)(k:ℕ)(i:Phase):(WingP Hp Z a V x y p q k).seq i.val=UnitBorn Hp Z a V x y i k p q:=by fin_cases i<;>rfl
lemma skep (V:Even n.val)(x y:Site n)(p q:Mint Z e)(i:ℕ)(h:p∈ Dross Hp Z a e)(hv:barrier P≤ n.val)(hT:Pins K P x y): WingP Hp Z a V x y p q i=0 ∧ WingP Hp Z a V x y q p i=0:=by
      have he(j:Phase): UnitBorn Hp Z a V x y j i p q=0∧ UnitBorn Hp Z a V x y j i q p=0:= h n V x y hv hT i j q; exact ⟨JetS.eta _ _ ((he 0).1) ((he 1).1) ((he 2).1),JetS.eta _ _ ((he 0).2) ((he 1).2) ((he 2).2)⟩
lemma budgetRide (h:l+l<k) (ht:∀ i,τ i≤m)(hp:∀ i,Rise.stamp' d G k+44 ≤ τ i)(he:e<l+1)(p:Mint Z e)(hZ:p∈ Dross Hp Z a e): WaneZ Z e he p∈ Dross Hp Z a e:=by
      intro n h' x y hb hx i j q
      let F:= WingP (e:=e) Hp Z a h' x y; have hL:=Attest.mk (e':=e) hb ht hp h; have he':F (WaneZ Z e he p) q i=0:=(Polygon0 Hp Z a h' x y hx hL i he p q).1.trans (by rw [(skep Hp Z a _ _ _ _ _ _ hZ hb hx).1,mul_zero]); have hh:F q (WaneZ Z e he p) i=0:=(Polygon0 Hp Z a h' x y hx hL i he q p).2.trans (by rw [(skep Hp Z a _ _ _ _ _ _ hZ hb hx).2,mul_zero]); have hp(Ω:Fruition Z.station (lapPrice P.L e))(A:Fruition Z.station (lapPrice P.L e))(hK:F Ω A i=0): UnitBorn Hp Z a h' x y j i Ω A=0:=(WingS Hp Z a _ _ _ _ _ _ _).symm.trans ((congr_arg (fun p:Token=>p.seq j.val) hK).trans (by fin_cases j <;> rfl)); exact ⟨hp _ _ he',hp _ _ hh⟩
end Topic
end YM.OPE.Stroke
