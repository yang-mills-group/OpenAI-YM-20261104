import YM.AllOrder.Burn.Errand
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Tir

/-!
# Bouquet and Clark valuation with all strata. Transfer within Hull by
aligned Career (identity) before the beta-read; pointwise. For applications
with Coast binding Y-axis family across β can instead follow Trio.Card via
catalog choices. Don't assert analytic matching on the indicated Budget yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Burn
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M k j m π u d: ℕ} {K : Teller G} {p a W U V g : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
local notation "B" => radiusB p
local notation "τ" => Mint.width X.halo (radiusB p) (2*radiusB p)
open Meadow (Park spin)

open High (chamber strands clusterBound sumshares)
section currency
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q: KernelChoices} {hC:C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T : Tube G (stepped Q h)} {T' : Tube G (stepped Q H)} {R:RG.Rep G f} {R':RG.Rep G F}
    {I : Cash W p a L₀ X o U T R} {I' : Cash W p a L₀ X o V T' R'}
    (hC he) (hp:R'.path=R.path) (ht:T'=Deck.re T) (hq:R'.p= R.p) (hζ:R'.beta=R.beta) (χ:Chi) (A:Config G c) (ha:RG.flags (Pressure.temp p) A=∅)
local notation "Z" => splitter (Deck.divides hC)
local notation "R₀" => radiusB p
variable {ℓ n v:ℕ} {r' r s₁ t C' w z e b₁ b₂ b₃ b₄ b₅ b₀ a₁ a₂ a₃ a₄ :ℝ}
    (N : Captain I n r s₁ t C' w z e b₀ a₁ ℓ χ) (N' : Captain I' j r' g b₅ a₂ b₁ b₂ b₃ b₄ a₃ v χ) -- tentative duplicate a expensive fix
include hC he hp hq ht hζ ha χ I I' N N'
variable {φ:Locale G}(s₁:Burn.Seed R' φ)(s₀:Burn.Seed R φ)
lemma compared (π k:ℕ) (X':Site C) (v:ℝ) (hr : clusterBound π τ π + τ ≤ m) (hm:4*m<c.val) :
    chamber (strands π (Burn.steady I' s₁ π k)) χ k v X' ((L).low.links A)= chamber (strands π (Burn.steady I s₀ π k)) χ k v ((Z) X') A := by
  let B':= (L).low.links A; have hB (A:Config G c) (ha: RG.flags (Pressure.temp p) A=∅):RG.flags (Pressure.temp p) ((L).low.links A)=∅:= by
    ext i; rw [show i∈RG.flags (Pressure.temp p) ((L).low.links A)↔_ from Deck.flagged hC A i (show c.val>4 from (by have hv:= I.laws.data.room.buys; omega)) (Pressure.temp p),ha]; simp
  let S0:= strands π (Burn.steady I s₀ π k); let S1:=strands π (Burn.steady I' s₁ π k) -- 
  have hv E (he':RG.flags (Pressure.temp p) E=∅) i: stream I χ E i= I.trainedPool χ E i:= Eq.symm ((congr_fun (N.permitAverage i).2.2.2.1 E).trans (masked_eq _ _ _ _ (by unfold Healthy; rw [he']; simp)))
  have hh i E (he':RG.flags (Pressure.temp p) E=∅): stream I' χ E i= I'.trainedPool χ E i:= Eq.symm ((congr_fun (N'.permitAverage i).2.2.2.1 E).trans (masked_eq _ _ _ _ (by unfold Healthy; rw [he']; simp)))
  let f (W : Site c) (V : Config G c) := (∑ i∈S0.filter (fun i=>W∈perf I i), -(((perf I i).card:ℝ))⁻¹*stream I χ V i)+Meadow.garner T.down T.low R.beta v B k W V
  let b (θ:Seat c):= f ((Meadow.spin θ).symm (Z X')) (θ.view A)
  unfold chamber Meadow.atlas; change _=likely b; rw [← Meadow.revolving hC b]; apply congr_arg likely; funext θ
  simp only [b,f,Pi.add_apply]; rw [show θ.view ((L).low.links A)=(L).low.links ((Meadow.pinch hC θ).view A) from Meadow.estuary hC A θ,← Meadow.inverts hC θ]; apply congr_arg₂ HAdd.hAdd
  · let V:=(Meadow.pinch hC θ).view A; have hE: RG.flags (Pressure.temp p) V=∅:= Meadow.covers_field _ _ ha; simp_rw [show (Meadow.pinch hC θ).view A=V from rfl, hh _ _ (hB V hE), hv V hE]
    let x:=(Meadow.spin θ).symm X'; let hq:= rendition (I:=I) (I':=I') hC he x hp s₁ s₀ hq ht hζ χ V hE π k hr hm
    exact sumshares (Classical.choice hq) _ _ _ check_steady check_steady (Meadow.garden hC x (by omega)) le_rfl (by omega)
  rw [hζ]; subst T'; exact Meadow.garner_pack hC ..
end currency
end YM.AllOrder.Burn
