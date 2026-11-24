import YM.Integration.WilsonSeparatedOriginalSlabDriven
import YM.Integration.WilsonSeparatedOriginalSlabGroupedCup
import YM.Integration.WilsonCloseCaptureFinances
import YM.Integration.WilsonCloseCaptureSignedPrice

/-! The genuine grouped three-slot Wilson coefficient is measured on one chart and signed door with its true joint centre. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabUnary
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open Ribbons Ribbons.ManyCopies WilsonReportHarvestSlabLabels WilsonSeparatedOriginalSlabDriven
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {m p N d k b:ℕ} {D:Address.Rail C} {Q:ℝ}
local notation "Y"=>C.path.rep N p (b+1)
local notation "σ"=>Many.crust C m (b+1) d k Q
local notation "ζ"=>Many.fee C m (b+1) d k 3 Q
local notation "A"=>C.S.oneStep b p

abbrev sale (C:Family G)(b H:ℕ)(income:ℝ):ℝ:=publicCost H (Copper.ld C.path.levels b)*(bling C.path.levels b*(4*(1/income)))

theorem original (made:C.Makes)(tiers:Cater C D){H:ℕ}{B B':ℝ}(nN:b+1≤N)
    (paid:Copper.SignedPrice C b p H N (D N p b nN) B B') (admit:H+3≤C.path.levels.clock.J b)
    {o:Fin 3→Site (C.side (b+1) p)} (home:(A).parent (o 0)=0)
    {rows:Fin 3→Three G (C.side (b+1) p)}{F:Config G (C.side (b+1) p)→Poly (Stock.census (Fin 3))}
    (occ:Occupancy o (C.path.levels.clock.J (b+1)))(positive:0<σ)
    (live:Integrable F (prior G (C.side (b+1) p))){spend:ℝ}(furls:Furls C.path.levels (b+1) spend)
    (bill:Alcove Y rows F o (fun _=>σ) spend (Bandage.renal C.path.levels (b+1)) (1/2))
    (reach:∀i:Fin 3,coverNumber (C.path.levels.budget (b+1)).B ({o 0,o i}:Support (C.side (b+1) p))
      ≤peepers C.path.levels (b+1)):
    0<ζ ∧ ∃x:Three G (C.side (b+1) p), Useful Y x ∧ (∀U,x.1 U=(F U).part entire) ∧
      ∀v:Fin 3→Axis→ℝ, (∀φ:Body,∀U,(tariff:ℂ)*(glyph (filed v) x φ).1 U=raw v φ*(F U).part entire) ∧
      ∃ (T:Tape G (C.side b p)) (g j:Palette C H),
        Course (D:=D N p b nN) (d:=H) (o 0) (glyph (filed v) x) T g j (sale C b H ζ) (sale C b H ζ) ∧
        size g ≤ sale C b H ζ:=by
  obtain ⟨hp,x,hx,measured,blade⟩:=WilsonReportHarvestSlabSingle.original made tiers (Nat.zero_lt_succ b)
    nN occ positive live furls bill reach
  refine ⟨hp,x,hx,measured,fun v=>⟨?_,?_⟩⟩
  · intro φ U
    change (tariff:ℂ)*(filed v φ*x.1 U)=_
    rw [←mul_assoc,measured]
    exact congrArg (fun q:ℂ=>q*(F U).part entire) (restored v φ)
  · have one:1≤bling C.path.levels b:=Real.one_le_exp (Real.sqrt_nonneg _)
    exact cooled made nN (tiers.throve H b N p nN admit) one paid (priced v H) home hx blade (by positivity)

end YM.Integration.WilsonSeparatedOriginalSlabUnary
