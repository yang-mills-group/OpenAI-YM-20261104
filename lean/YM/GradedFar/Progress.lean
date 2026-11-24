import YM.GradedFar.Horizon
import YM.GradedFar.Preinverse
/-!
# Preinverse version from explicit expenses, with (G.6) not needed as hypothesis

Keeping exact geometry window and price assignments. The other physical major hypotheses still
spelled out -- this result does not discharge G9 or running. The `J` engineering scale uses
`assign` and the Coat expense, assigned to **actual** `WilsonPositionHomogeneousFrame.homogeneous`
in application. Keep even the mixed test `c` using the same exterior, as in `BeforeInverse`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
open Filter Function Set Spec Table Extraction
open OPE hiding Prescription
open OPE.Orbits
open Trace.Pilot PhysMS XSpace XSpace.Normalize FVA2 FVA2.O.Enh FVA2.GradedFar
open FVA2.Scale FVA2.O.Score
open MS MS.Book MS.Fleet MS.Land FVA2.Register
open Fork (Coat)
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J:ℝ→tower S)
    {n m l h:ℕ} {d:Fin n→ℕ}{e:Fin m→ℕ}
variable (N : WilsonPrescription G){hG:G.Simple}(Z : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N hG Z σ true) (ν:ℝ)
local notation "A" => Scale.Measure.outlook N.scheme N.criterion
local notation "W" => GroupS.gaugeN N.scheme N.criterion Z ν

variable {t:ℝ→ℝ}(ht:Coupling G t) (hd:Through l d)(he:Through l e)(hh:h≤l)
    {K:Set (Points n)}{S':Set (Points m)}(hK:IsCompact K)(hx:K⊆conf n)(hS:IsCompact S')(hy:S'⊆Outside m)
include H ht hK hx hS hy
theorem before_of_prices (Ht:LogTrace F R.port)(Hh:Coat F R J h)(HA:∀ i,Coat F R J (d i))(HB:∀ i,Coat F R J (e i))
    {a Λ η:ℝ}(ha:0<a)(hb:0<Λ)(hη:η<1)
    (hW:∀ B> (0:ℝ),∀ i,FrameForecast J t W (e i) Λ B)
    (hf:∀ B>0,∀ p,RoundPoint F J t A hd he Λ B p K S')
    (hout:∀ B>0,∀ p,RoundPoint F J t A (d:=Output h) (fun _=> hh) he Λ B p {0} S')
    (p':ℕ):∀ᶠ B in atTop,∀ᶠ p in atTop,BeforeInverse F J R N Z ν t hd he hh K S' a Λ η B p' p:= by
  obtain ⟨D,hD,Ht⟩:=G6_forecast F R J d e h hG K S' hK hx hS hy Ht Hh HA HB
  exact progresses F J R N Z H ν ht hd he hh hK hx hS hy ha hb hη hD hW hf hout
    (fun B _=> G6.target F R J d e h (Ht Λ B)) p'
-- see Measured for specialized exact assets
end YM.Integration.GradedFar
