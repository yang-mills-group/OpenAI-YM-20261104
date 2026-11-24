import YM.Integration.WilsonAddressedWeakFixedRank
import YM.Integration.WilsonThermometerWeakPanelBorn

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakSingletonRoot
open PhysicalNext PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Filter RG.Supply Next.Rank.Ship Next.Rank.Station Next.Rank.Spindle
open Function Filter Set Metric Source RG12 Extra.Histories RG05Readout Native Address Many Records Harvest Push.GridApprox Cells Extraction
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Tapes.West Configuration Normal Rise
open Paint Thirst Relation Perch Glimmer LiftMark Beamer Station Atlas Tariffs Ribbon
open Edition Peak Value Marker Corona Alarm Next.Rank.Glyph
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonAddressedWeakCalibration WilsonAddressedWeakReflectedHearing WilsonThermometerReflectedTrajectory
open FVA2 FVA2.ColorCode Pert.Position MS MS.Land MS.Menus MS.Rake MS.Tone PhysMS
open Trace Trace.Pilot WilsonAddressedWeakCorrectedCylinder WilsonAddressedWeakPointCells WilsonAddressedWeakMaxwellPositions
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} (R:Run G) {d H:ℕ}
local notation "Rf" => R.family
local notation "Lev" => R.family.path.levels
local notation "cash" => WilsonThermometerOffsetLedger.cash R

open Next.Rank Read Cells

/-- Undo only the genuine singleton subtraction inside the original positive reflection price. -/
theorem restored {N k p:ℕ} (u:ℝ) (hk:k≤N) (x:Points 2)
    (fit:Fit (Lev) u k x) (tag:Fin 2→(standard Rf).Tag)
    (field:Fin 2→ Config G ((Rf).side N p)→ℂ) (i:Fin 2)
    (hf:Interior ((Ship.yard Rf u hk p).chamber 0) (field i)):
    let T:=Ship.yard Rf u hk p;let β:=(Rf).beta N p
    let a:=(maxProfile Rf (tested (Lev) u k x) tag).part (slot i)
    T.rootTest β (field i)≤T.rootTest β (fun U=>(Read.cylinder (Ship.targets Rf tag fit) field U).part (slot i))+‖a‖:=by
  intro T β a
  let c:Config G ((Rf).side N p)→ℂ:=fun _=>a
  have split:(fun U=>(Read.cylinder (Ship.targets Rf tag fit) field U).part (slot i))=field i-c:=by
    funext U
    exact Read.cylinder_single (Read.cumulative Rf (tested (Lev) u k x) tag (Ship.fitting fit)) field i U
  have hc:Interior (T.chamber 0) c:=Interior.constant _ _
  have const:c=a • (1:Config G ((Rf).side N p)→ℂ):=by funext U;change a=a*1;rw [mul_one]
  rw [split]
  have rooted:=(Cells.laws G _ β (Overlay.beta_positive R.makes.wilson le_rfl).le).semi T
    (field i-c) c (Next.UVStress.minus hf hc) hc
  rw [sub_add_cancel] at rooted
  have eq:T.rootTest β c=‖a‖:=by rw [const,Next.UVStress.root_smul,T.root_one,mul_one]
  simpa only [eq] using rooted

/-- At a separated original reporting shape the finitely many genuine one-field Maxwell
counterterms are bounded before the ultraviolet and period parameters are read. -/
theorem axes {d:ℕ} (x₀:Points 2) (admit:x₀∈conf 2):
    ∃ C c:ℝ,0<C ∧ 0<c ∧ ∀x:Points 2,dist x x₀<c → ∀ j:((Rf).labels.level d).Index,
      let tag:=Atlas.jointX (C:=Rf) (d0:=fun _:Fin 2=>d) (fun _=>Size.axis ((Rf).labels.level d) j)
      ‖(maxProfile Rf x tag).part (slot (0:Fin 2))‖≤C:=by
  let F:=(Rf).labels.level d
  let tag (j:F.Index):=Atlas.jointX (C:=Rf) (d0:=fun _:Fin 2=>d) (fun _=>Size.axis F j)
  let Val (x:Points 2) (j:F.Index):=(maxProfile Rf x (tag j)).part (slot (0:Fin 2))
  let bound:=∑j:F.Index,‖Val x₀ j‖
  have bpos:0≤bound:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  have all:∀ᶠ x in 𝓝 x₀,∀ j:F.Index,‖Val x j-Val x₀ j‖<1:=by
    apply eventually_all.mpr;intro j
    have con:ContinuousAt (fun x=>Val x j) x₀:=
      (Read.profile_part_cont (standard Rf) (Maxwell.table_smooth (Rf).labels) (tag j) (slot (0:Fin 2))).continuousAt
        ((conf_open 2).mem_nhds admit)
    have loc:∀ᶠ x in 𝓝 x₀,Val x j∈Metric.ball (Val x₀ j) 1:=con.tendsto (Metric.ball_mem_nhds _ zero_lt_one)
    filter_upwards [loc] with x hx;simpa only [Metric.mem_ball,dist_eq_norm] using hx
  obtain ⟨c,hc,good⟩:=Metric.mem_nhds_iff.mp all
  refine ⟨1+bound,c,by linarith only [bpos],hc,?_⟩;intro x hx j
  have price:=good (Metric.mem_ball.mpr hx) j
  have one:‖Val x₀ j‖≤bound:=Finset.single_le_sum (fun j _=>norm_nonneg (Val x₀ j)) (Finset.mem_univ j)
  calc ‖Val x j‖=‖(Val x j-Val x₀ j)+Val x₀ j‖:=by rw [sub_add_cancel]
       _≤_:= (norm_add_le _ _).trans (add_le_add price.le one)
end YM.Integration.WilsonAddressedWeakSingletonRoot
end
