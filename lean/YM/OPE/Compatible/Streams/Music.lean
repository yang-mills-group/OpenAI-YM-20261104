import YM.OPE.Compatible.Streams.Dug
/-!
# Trans.S.Spectral covariance. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark
variable {n c f:Side}{I J M E Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {v v' b:ℝ} {U:Boxes G P K.K}
local notation "Y!"=>solar G d τ
local notation "T!"=> Tracts G d τ
open JetS
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)
namespace Topic
variable (Z:Topic H hs X B D₀)
local notation "μ"=> lapPrice (Patch.L P)
variable {u z vν ξ:M→ℝ}{hv:4 ≤ i}{hn:4 ≤ j}{hp:0 ≤ u}{hx:0 ≤ z} {P':(m:M)→Alps K T i (u m)}{Q':(m:M)→Alps K T j (z m)}{Y:M→ Tracts G d τ→L[ℝ] Tracts G d τ}
variable {a:Axis}
section
variable (F:Sprint H hs D₀ u z a P' Q' hv hn hp hx r Y) (Ψ:1≤ ξ)(Ja:Z.Ω M vν)(Γ: Wealth vν ξ 1)(hz:Wealth Y ξ 1)(D:Z.Floss Q' Ja hn hx k Hp a)
include F D Ψ Γ hz
local notation "C!"=>Topic.Ext Z Ja Ψ Γ hz (Sprint.march F)
omit D in
lemma ext_lid (b:M)(he:e< l+1)(p:(Topic.Ext Z Ja Ψ Γ hz F.march).flag e b): (Topic.Ext Z Ja Ψ Γ hz F.march).read e he b p= (Fleet Z.station (μ e) 3 (EndFare P.L e)^r) (Ja.read e he b (Ja.picture e Y b p)):=rfl
lemma Extens : Z.Floss P' (Topic.Ext Z Ja Ψ Γ hz F.march) hv hp k Hp a:=by
     let A':=Topic.Ext Z Ja Ψ Γ hz F.march; refine ⟨D.dimD,D.cap,D.vol,D.ward,?_,?_⟩
     · intro e he j p; exact Aeon.flavorStep Ja Z.bill (fun i _=>EndFare _ i) Ψ Γ hz F.march (Gift G D₀.aware) e (Freedom H hs X B Z.station D₀ (Z.bill e he)) he _ (D.turn e he j) p (F.mood j _)
     intro e he o n V x y ht hX L p q U
     have he': μ l≤μ e:=by by_cases h:l=e; rw [h]; exact (stairPrice _ e l (by omega) P.coarse).le
     let R(i:ℕ)(p q: Tracts G d τ):ℝ:=PhaseP (D₀:=D₀) (H:=H) (hs:=hs) (P' L) hv (hp L) a x y V o i p q; let N(i:ℕ)(p q:Tracts G d τ):ℝ:=PhaseP (D₀:=D₀) (H:=H) (hs:=hs) (Q' L) hn (hx L) a x y V o i p q
     let J: Z.Mint e→Z.Mint e→ℝ:=fun i j=> Scar Hp Z o V x y a (e:=e) i j; apply Aeon.transF Ja Z.bill (fun i _=>EndFare _ i) Ψ Γ hz F.march e he L R N J p q ; exact (F.budget n V x y ht hX o L p.val q.val).extend (mul_le_mul he' he' (EndFare ..|>.le) (EndFare ..|>.le)); exact D.corn e he o n V x y ht hX L _ _
end
end Topic
end YM.OPE.Stroke
