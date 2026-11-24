import YM.OPE.Compatible.Oasis.Tower
/-!
# One pulse calibration estimate. Upper.H.B only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.CardinalQ
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson
open scoped Topology BigOperators Classical
open Drift Stroke Yolk Pill Spells
open Next.Scheduling Clock
open Lass Lass.Zest Stroke.MatchZ
open Source Labels
variable {G:Gauge}{X E I:Type}{t s z V:ℝ}{k k' l j:ℕ}{T:Stage}
variable {A:Labels.Frame G l}{S:SectionData A}{H₀:Hol G}
open Precision Stationary
set_option quotPrecheck false
variable {v:I→ℝ}{f:Filter I} {K:Votive.Sponsor G}{P:Votive.Seasons K} {a:Axis}{K₀:ChartRatio G}
variable {H:LocalRatio K₀}{L:PriceBook H P} {hs:G.Simple}
open Next.Free FreeResolvent Silt Silt.Float MSbar.Tree MSbar.Tree.Resolvent Cascade Cascade.Paver
variable (N:Foyer L hs a l (k+6)){hz:highStage L hs a N≤ j}{p:Clip}
variable (Y:BankW L hs a N hz p)
local notation "χ"=> Cab P j p
local notation "ZT"=> N.pay.st
local notation "𝓔"=> Dial.BoxQ (dims N)
variable {he:highStage L hs a N ≤ j}
include he
lemma Demand (S:SectionData A)(x:ℝ):∃ m:ℕ,∀ n:Side, m ≤ n.val→let z:=N.pay.st.τ 0; let b:=4*fieldQ S x; ∀ V:χ,∀ q∈ Hoard G b (k+6) z, ‖boostS (rentV G V.ℳ.gear (hazard N he) K.K n) (1/2) z (k+6) q-boostS (atlasF G V.ℳ.gear (hazard N he) K.K) (1/2) z (k+6) q‖ ≤ ages (-1) x *‖q‖:=by
        let f : Filter Side:=Filter.comap PNat.val atTop; let z:=N.pay.st.τ 0; obtain ⟨U,hU,hV⟩:= (show ∃ s∈(atTop:Filter ℕ), _ from mem_comap.mp (Solv K.K (hazard N he) (1/2) (ages (-1) x) (4*fieldQ S x) (k+6) z G (Real.exp_pos _))); obtain ⟨b,hb⟩:= eventually_atTop.mp (show ∀ᶠ i:ℕ in atTop,i∈U from hU); exact ⟨b,fun n hn W p hq=> hV (hb _ hn) W.ℳ.gear p hq⟩ -- let
omit he
variable (R0:Pad G)
abbrev SealK (x:ℝ)(T:Stage) (S:SectionData A)(H:Hol G)(n:Side)(R:Rep G n)(P:A.Coeff → Coefficient A n)(U:Torch S H 0 R P k (salary x)) :Prop := Registered x T H R S P∧Grant (z:=x) U T
structure PhotoZ (x:ℝ)(t:ℝ)(i:Cab P j p)(S:SectionData A)(n:Side){R:Rep G n}{P1:A.Coeff → Coefficient A n}{Hh:Hol G} (U:Torch S Hh 0 R P1 k (salary x)) :Prop where
        readW : ‖ClockVal N Y i S R0 U (gap R.beta)‖≤ ages t x
        erect : ∃ P': Dial.BoxQ (dims N)→L[ℂ] A.Coeff,(ClockVal N Y i S R0 U (gap R.beta)).comp P'=ContinuousLinearMap.id .. ∧‖P'‖≤ ages t x
end YM.OPE.CardinalQ
