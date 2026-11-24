import YM.Qlocal.Skating.Ice
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Skating
open Filter Function Set Lattice RG Gauge Input Pressure Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open PhysicalNext PhysicalNext.Repeat AnalyticBridge VerifiedReset Extra.Iteration Song
open Collection Quotes Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Roost Coat ThroughLaunch
open RGComparison01 RGComparison01.Pledge RGComparison01.Pledge.Holdings BudgetPoint
open Push.Uniform Sienna
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open AllOrder Floe Step Step.PlanV Catch Transit Transit.WheelP
open Squall Squall.Lumber Squall.Skull
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A: Alloy X D} (F:Factor A)
    {R:Roots (G:=G) X.p.profile X.K X.p.kernel}{Q:R.Tab D}
    {c f:Side}{n m r q k:ℕ}
set_option quotPrecheck false
local notation "a"=> A.B.a
local notation "Y"=>(a).clock.J (m+1) -- dot notation needs () fix
local notation "E"=> (a).clock.J m
local notation "h"=> (a).clock.adm (m+1)
variable {η ζ:ℕ→ℝ}{T:ℕ→ℕ} 
local notation "Rℓ"=>Runway F m η T r q
variable (V:Runway F m η T r q)
local notation "Ω"=> costAux F V
local notation "Γ"=> needP F V
local notation "V★"=>Porch F V
local notation "P₀"=> A.B.a.budget (m+1)
local notation "P₁"=> A.B.a.budget m
local notation "z"=> (a).clock.hatBeta m
local notation "M" => radiusB z
local notation "ν"=> F.shape.μ
local notation "L"=> D.L (A.B.a.clock.J (m+1))
variable (hv:Pleased (R:=R) (ζ:=ζ) F V) (ht:Pass R Q A F)
namespace Rune
-- concrete activation.W.Label.Normalization group input.Tean.P. Revenue restoration after Paint coherence.F.Channel.
open Dredge Quipu Quipu.Sonnet Tern Versal Quipu.Eluder.Incline.Bookworm
-- Geometry on each eligible Period.Pure.LengthCut independent.
variable {β:ℝ} (l:f.val=c.val*(A.B.a.S.block m).val) {C F':Side}
local notation "S"=> (A.B.a.clock.op m 0).patch
local notation "Pk"=> Pane.panel A m l
local notation "R'"=> A.B.a.S.block m
local notation "x'"=> ((A.B.a.S.block m).val)
local notation "Y'"=> (A.B.a.clock.hatBeta (m+1))
set_option quotPrecheck false
local notation "b'"=> betaF G z L
local notation "th" => Stores.till (betaF G z L)
variable (hc:4*costAux F V+16 ≤ c.val)
open Versal Further.PhysicalPeriodLimitF933 Macrame Bloch Slide
include hv ht hc l
noncomputable abbrev horizon := Library.spread F m (2*M)
-- Lens width at `2*M` from Monitor alignment. any at most
lemma border : 2*Marines.border S Ω < f.val ∧ Marines.border S Ω+Stores.till b'< f.val := by
 let L₁:= x'; let H:= Marines.border S Ω; have hh:H=L₁*(2*Ω+2):= rfl -- syntax clash L macro; replace
 obtain ⟨hn,hS,hW,hb,hp,hT,hF⟩:= stip F V hv ht; have h1: (S).L.val>0:= (S).L.pos; change 0<(A.B.a.S.block m).val at h1; have h2:Stores.till b' ≤ 2*Ω:= (by rw [show Stores.till b'=radiusB (b')/100000 from rfl]; exact (Nat.div_le_self ..).trans (hb ▸ (hp.trans (Nat.mul_le_mul_left 2 (costs F V)))))
 have he:2*H<f.val:= by rw [hh,l]; nlinarith only [Nat.mul_le_mul_right x' hc,h1]
 constructor
 · exact he
 have hh':th ≤ H:= h2.trans ((by rw [hh]; exact le_trans (Nat.le_add_right (2*Ω) 2) (Nat.le_mul_of_pos_left (2*Ω+2) h1)))
 change H+_ < _; omega
-- std
omit hv ht hc l
local notation "w"=>2* M
lemma peak_size : Hoboken.std F m w (V.l+q) ≤ costAux F V:= by
 let U:= horizon F (m:=m); have hz: U= Deck.Mint.width (F.target Y E|>.halo) M (M+2*M):=rfl
 have hv:1≤ M:= (P₁).B_pos; exact le_trans (Nat.le_add_right (Cabinet.garage U (V.l+q)) (3*U)) (Fiord.imprint _ _ _ _ hv)
end Rune
end YM.Qlocal.Skating
