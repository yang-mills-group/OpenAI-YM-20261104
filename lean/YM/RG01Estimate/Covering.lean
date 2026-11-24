import YM.RG01Estimate.ParcelPick
import YM.RG01Estimate.Horoscope
/-!
 # Improve Compass to ANY common auth. Auxiliary seasons may be short. For
 kin mark comparison supply all common scaled extensions, not just homologous fields.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Board
open PhysicalNext.Repeat
open Filter Function Lattice Wilson RG RG.Supply Input Precision Org Tree Exterior Gauge
open Matrix Finset Push AbsoluteSums Gas Extra.Iteration Extra.Iteration.Calibration Bid Bloch Laurent UVNext UVNext.PricedKernels
open Pressure AnalyticBridge VerifiedReset Collection Quotes PriceCompiler Uniform RG.Shoot
open ConnectedActivityE6 Testing SectorMeasure Further.PhysicalPeriodLimitF933 Further.PhysicalPeriodLimitF933.Mural Macrame
open Sienna Token Lantern Lapis Shellac Fare Planned.JetPort Pane
open Laplace Courtyard Receipt ConnectedActivityE6.Coat Roost Boulevard
open Abacus Evoc Deck
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{U:Alloy X D}(R:Factor U)
   {c f c' f':Side}{N m d n i j r:ℕ} (Hm:m < N) (H : f.val=c.val*(U.B.a.S.block m).val) (H' : f'.val=c'.val*(U.B.a.S.block m).val)
local notation "Γ" => U.B.a
local notation "J" => U.B.a.clock.J (m+1)
local notation "I" => U.B.a.clock.J m
local notation "A₀" => U.B.a.clock.adm (m+1)
local notation "x" => U.B.a.clock.hatBeta m
local notation "L" => D.L (U.B.a.clock.J (m+1))
local notation "B" => U.B.a.budget m
local notation "B'" => U.B.a.budget (m+1)
local notation "W" => R.shape
local notation "𝕊" => Pane.panel U m H
local notation "𝕊'" => Pane.panel U m H'
local notation "Φ" => (Pane.orchestra U N H)
local notation "Φ'" => (Pane.orchestra U N H')
local notation "χ" => Chi.canonical
local notation "Z'" => R.expense J I
local notation "γ" => U.B.kin.alpha N m
local notation "σ" => X.p.profile (U.B.a.clock.J m)
set_option quotPrecheck false
local notation "P₀" => (Γ).clock.op m 0
local notation "b" => (Γ).S.block m
local notation "D₀" => (R.target J I).halo
variable {Y:Type}

-- one badge E*. all priced law at current Calendar profile. Deck path tied to T.
structure Insured (U:Alloy X D)(N m d:ℕ){c f:Side}(H:f.val=c.val*(U.B.a.S.block m).val)(β:ℝ)(Y:Type) where
   rep : RG.Rep G f
   pathU : rep.path=(Pane.orchestra U N H).up
   clip : rep.clip=(Pane.orchestra U N H).high
   β' : rep.beta=β
   point : rep.p=U.B.a.budget (m+1)
   legal : rep.activities.Valid rep.p (U.B.a.clock.allowance (m+1)) (U.B.a.clock.forcedAllowance (m+1))
   sacrifice : Set ℕ
   music : Lex Y f
   coverage : Record Y (Pane.panel U m H) rep music sacrifice
   cost : StageMask rep (Pane.panel U m H) music d

variable (β:ℝ) (F:Insured U N m d H β Y) (F': Insured U N m d H' β Y)
   {M :ℕ}
-- common Λ retrofits, hypothesis on Rep values genuine. C' panels small, cross Big product. For all Ks.
def reports (hD: c'.val=c.val*M)(he:2≤ c.val) := Evoc.Charts (P:=(P₀).patch) (h:=H) (H:=H') hD he F.rep F'.rep F.music F'.music

variable (Y₀:Finset Y)(G':Chartlet R.shape U N m H F.rep) (Z:Chartlet R.shape U N m H' F'.rep)
local notation "d₀" => (Evoc.house D₀ (radiusB x) d (Fate.steps r))
local notation "p₀" => (Evoc.optic D₀ (radiusB x) d)


-- Warped orientation period
include R Hm
lemma retros (r d':ℕ) (hD:c'.val=c.val*M)(he:2≤c.val)(hp:4*(Evoc.house (D₀) (radiusB x) d (Fate.steps r)+Evoc.optic D₀ (radiusB x) d+5)<c.val)
   (hA : reports H H' β F F' hD he) (z:Site c') (x': Config G c) (hx:flags (B).threshold x'=∅):
    Evoc.aspect Z F'.music (Fate.steps r) χ γ Y₀ d' z ((normal (Deck.divides hD) hD).links x')=Evoc.aspect G' F.music (Fate.steps r) χ γ Y₀ d' (splitter (Deck.divides hD) z) x':= by
   have hz:= R.pledging.jewels J x (U.B.valid.pays m) I (step_paid U.B.a m)
   obtain ⟨y,d,v,t,a,c,r',B₀,q,i,n,N',hr,hT⟩:= hz.2 _ _ _ Φ G'.laws.data.funds (Pane.ovation U N H Hm R.pledging.conducts.full) _ G'
   obtain ⟨y',d_,v',t',a',c'',rh,B₁,q',i',n',N'',h'⟩:=hz.2 _ _ _ Φ' Z.laws.data.funds (Pane.ovation U N H' Hm R.pledging.conducts.full) _ Z
   obtain ⟨N',Hℝ⟩:=N'; obtain ⟨N'',Hℝ'⟩:= N''
   have hh:F'.rep.path=F.rep.path:= F'.pathU.trans F.pathU.symm
   exact thrill (V:=F.music) (V':=F'.music) (hC:=hD) (P:=(P₀).patch) (h:=H) (H:=H') (he:=he) (T:=Φ) (T':=Φ') rfl (F'.point.trans F.point.symm) (F'.β'.trans F.β'.symm) hh G' Z (hA) _ F.cost F'.cost hp N' N'' x' hx Y₀ d' γ -- syntax

variable {H H'}

end YM.RG01Estimate.Board
