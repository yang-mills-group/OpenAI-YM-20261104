import YM.Integration.WilsonPhysicalStationMixedWickNamedGram
import YM.Integration.WilsonPhysicalStationMixedWickCurrency
import YM.Integration.WilsonPhysicalStationMixedWickForeignPanel
import YM.Integration.WilsonOriginalPublicRelativeGramPanel

/-! The fully weighted original lower measurement on the original earned
reflected axes. Both vector slots keep their complete degree and Wick count. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickMetered
open Filter Finset Function Lattice RG Wilson Labels Source Cells Extraction Table Climb Trace
open PhysMS Spec OPE Next.UVStress Trace.Pilot PhysicalNext.Repeat.Legato
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare Next.Rank.Station
open MS MS.Land MS.Menus MS.Theater XSpace.Structure1
open Local.Physical
open WilsonPhysicalStationMixedWickNamedGram (amount electrode)
open WilsonMovingForkReporterBothArms (Filed)
open WilsonPhysicalStationGradedLowerPanel (metered frame)
open WilsonMeasuredPublicEntranceNativeLowerFrame (panel)
open WilsonPhysicalStationMixedBasisSale (Sold)
open scoped BigOperators Classical Topology Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {ℓ:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}(J₀:ℝ→tower S)(J:Scaling S)
    (V:∀m,Vane R.family m){m D:ℕ}(B:Deck G)(e:ℕ)(a:Axis)
    (K:Set (Points 2))(compact:IsCompact K)(clear:K⊆conf 2)
set_option quotPrecheck false
local notation "AX" => R.family.path.levels
local notation "I" => Glyph B e
local notation "T₀" => (AX).clock.monitor (V m).k

def total:ℝ:=∑i:I,∑j:I,amount R B e a K compact clear i j

include F in
theorem original (checked:(V m).checked f H m)(he:e < m+1)(M c:ℝ)
    (filed:Filed (f:=f) (l:=ℓ) J₀ J V e m M c)
    (simple:G.Simple)(below:(ℓ:Filter _)≤f.fuse)(hot:1≤T₀)
    (sales:∀b,Sold R (V m) (electrode R e K compact clear b) he he D checked)
    (ξ:Points 2)(member:tested AX (V m).b (V m).k ξ∈K)(fits:FitSky AX (V m).b (V m).k ξ):
    ‖metered B e T₀ (frame R (J.U m) B e a ((V m).wheel.r • tested AX (V m).b (V m).k ξ))-
        panel R B e a (tested AX (V m).b (V m).k ξ)‖ ≤ total R B e a K compact clear/((D:ℝ)+1):=by
  let y:=tested AX (V m).b (V m).k ξ
  let actual:=frame R (J.U m) B e a ((V m).wheel.r • y)
  let target:=panel R B e a y
  have cash (i j:I):
      ‖(metered B e T₀ actual-target) i j‖ ≤ amount R B e a K compact clear i j/((D:ℝ)+1):=by
    have issued:=WilsonPhysicalStationMixedWickNamedGram.original R F J₀ J V B e a K compact clear
      he checked filed simple below sales ξ member fits i j
    have response:=WilsonPhysicalStationMixedWickCurrency.restored hot (by positivity : 0≤(D:ℝ)+1)
      j.2.1.val i.2.1.val (actual i j) (target i j)
      (fun diff=>WilsonPhysicalStationMixedWickForeignPanel.original R B e a y i j diff) issued
    apply (le_div_iff₀ (by positivity)).mpr
    rw [mul_comm _ ((D:ℝ)+1)]
    exact response
  have entire:=WilsonOriginalPublicRelativeGramPanel.entry_bound
    (E:=metered B e T₀ actual-target) _ cash
  simpa only [total,Finset.sum_div] using entire

end YM.Integration.WilsonPhysicalStationMixedWickMetered
end
