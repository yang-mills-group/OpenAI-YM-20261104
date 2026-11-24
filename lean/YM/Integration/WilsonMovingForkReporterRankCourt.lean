import YM.Integration.WilsonMovingForkReporterHeatedAperture
import YM.Integration.WilsonMovingForkReporterWallHeight

/-! Both original windows are paid at one date. Only the two tested fields enter the order of the genuine Wick calculation. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterRankCourt
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open PhysicalNext.Repeat.Legato
open Next.Rank.Ribbon

open Next.Rank.Configuration
open WilsonMovingForkReporterHeatedAperture (Ready spread)
variable {G:Gauge} {C:Family G} (B:Binding C) (H:C.Makes) (O:HaarBudget G) (J:ChartRatio G)
local notation "A" => C.path.levels

def Signed (E:WilsonMovingForkReporterHeatedAperture.Test C) {D:ℕ} (pan:Tapes.Panel D) (k n:ℕ) (z:ℝ) : Prop :=
  let α := pan.bag (C.path.levels.clock.J k)
  ∀ N p (fine:k<N) (l r:ℝ) (L:LegacyCostSky B J (-3) z α k n D O l r)
    (V:Rep G (C.side k p)) (_:ActumSky B H O J pan L V fine)
    (x:Points 2) (_:Station.tested A α.band k x∈E.support) (fit:FitSky A α.band k x)
    (F:(i:Fin 2)→StampDuty C k N p (E.deg i) α.taylor V α.era.coast.Q (stamp A N p))
    (u:(i:Fin 2)→C.label (E.deg i)),
    (∀i,Price.Solves C (mag A α.band k) (E.deg i) k N p (F i).T (E.raw i) (u i)) →
    let a := WilsonPhysicalThermalWickStretched.rates ((Perch.bill 1 (clim A k))^spread E)
    ∀ (P:(i:ℕ)→Rep G (C.side i p)) (eq:P k=V),
    WilsonReporterWeightedReturn.Signed (P:=P) (ξ:=α) (WilsonReporterWeightedOrdinary.stretch C a E.raw)
      (WilsonReporterWeightedOrdinary.stretch C a u) fit (eq.symm ▸ F)

theorem original (simple:G.Simple) (E:WilsonMovingForkReporterHeatedAperture.Test C) {D:ℕ}
    (room:E.height≤D) (θ:ℕ) (deep:100*(E.height+1)≤θ) (lo hi:ℝ) (six:6≤lo)
    (wide:lo≤hi) (poles:∀i,saves C (E.deg i)+(spread E:ℝ)+3≤lo) :
    ∀ᶠ k:ℕ in atTop,∀ pan:Tapes.Panel D,pan.θ=θ → pan.arc∈Icc lo hi →
      WallsSky pan.arc (fun i=>(E.elevated i).trans room) E.raw E.support θ k ∧
      ∀ n:ℕ,2≤n→∀z,Signed B H O J E pan k n z := by
  classical
  let predicate := fun k (s:Icc lo hi) =>
    WallsSky s.1 (fun i=>(E.elevated i).trans room) E.raw E.support θ k
  let ballot (k:ℕ):Icc lo hi := if h:∃ s,¬predicate k s then h.choose else ⟨lo,le_rfl,wide⟩
  have walls := mural_castSky (fun i=>(E.elevated i).trans room) E.raw E.compact E.clear H simple lo six
    (fun i=>by linarith only [poles i,Nat.cast_nonneg (α:=ℝ) (spread E)]) θ
    (fun k=>(ballot k).1) (fun k=>(ballot k).2.1) hi (fun k=>(ballot k).2.2)
  have heating := WilsonMovingForkReporterHeatedAperture.original simple H E θ deep lo hi six wide poles
  filter_upwards [walls,heating,WilsonMovingForkReporterWallHeight.original B H O J simple D]
    with k issued ready physical pan clock band
  refine ⟨?_,?_⟩
  · change predicate k ⟨pan.arc,band⟩
    by_contra refused
    have no : ∃ s,¬predicate k s := ⟨_,refused⟩
    exact no.choose_spec (by change predicate k (ballot k) at issued; simpa only [ballot,dif_pos no] using issued)
  · intro n two z N p fine l r L V actual x member fit F u solved a P eq
    subst V
    let α := pan.bag (C.path.levels.clock.J k)
    have ht : α.taylor=θ := (pan.stable _).trans clock
    have hb : α.band∈Icc lo hi := (pan.factor _).symm ▸ band
    obtain ⟨V',hV,whip⟩ := actual.acts
    have positive : 0≤α.band := (by linarith only [six] : 0≤lo).trans hb.1
    have original := embroideredSky B J (isohypse H fine.le p) α H L.hours L.token L.moves V' whip positive
    have window := ready.1 _ hb
    rw [←ht] at window
    have land := physical L two N p E.height room
    have bell := (window.replies x member fit L.age.allot.permitted).2 p (stamp A N p) land
    exact ready.2 fine.le ht hb member fit F bell original.invariant u solved

end YM.Integration.WilsonMovingForkReporterRankCourt
end
