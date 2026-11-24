import YM.Integration.WilsonMovingForkReporterBasisRows
import YM.Integration.WilsonPhysicalStationObservedEntry
import YM.Integration.WilsonMeasuredPublicEntranceThermalRankPair

/-! The entire original reflected row bought at the elected reporter horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationBasisIncome
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent
open Next.Rank.Ribbon Table Trace.Pilot Trace PhysicalNext.Repeat.Legato
open WilsonPhysicalStationThermalVotes (votes offered)
open WilsonPhysicalStationThermalPair (cell)
open scoped Topology BigOperators Classical

open WilsonMovingForkReporterFixedRanks (Axes test)
open WilsonMovingForkReporterRankCourse (reached surplus)
open WilsonPhysicalStationThermalRanks (probe)
open WilsonPhysicalStationObservedEntry (born)
open WilsonMovingForkReporterBasisRows (Sold fare)
open WilsonPhysicalStationThermalBasisOffice (rank)
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:(Bel R.family.book).Hierarchy}{h D:ℕ}
local notation "C"=>R.family
local notation "AX"=>R.family.path.levels
def budget (A:Axes C):ℝ:=∑a,|fare R A a|
def price (A:Axes C)(D:ℕ):ℝ:=budget R A/((D:ℝ)+1)
lemma nonnegative (A:Axes C)(D:ℕ):0≤price R A D:=div_nonneg
  (Finset.sum_nonneg (fun _ _=>abs_nonneg _)) (by positivity)

lemma graded {t x c:ℝ}{q Q D:ℕ}(positive:0≤t)(order:q≤Q)
    (paid:((D:ℝ)+1)*t^((Q-q:ℕ):ℝ)*x≤c):
    x*t^Q≤c/((D:ℝ)+1)*t^q*t^(-(0:ℝ)):=by
  simp only [neg_zero,Real.rpow_zero,mul_one]
  rw [Real.rpow_natCast] at paid
  have rest:t^(Q-q)*x≤c/((D:ℝ)+1):=by
    apply (le_div_iff₀ (by positivity : 0<(D:ℝ)+1)).2
    calc _=((D:ℝ)+1)*t^(Q-q)*x:=by ring
         _≤_:=paid
  calc x*t^Q=x*(t^(Q-q)*t^q):=by rw [←pow_add,Nat.sub_add_cancel order]
       _=(t^(Q-q)*x)*t^q:=by ring
       _≤_:=mul_le_mul_of_nonneg_right rest (pow_nonneg positive _)

theorem original (V:Vane R.family h)(A:Axes C)(hs:A.weight≤h)(check:V.checked f S h)
    (warm:0≤(AX).clock.monitor V.k)(sold:Sold R V A hs D check):
    let d:Fin (h+1):=⟨A.weight,by omega⟩
    let z:=probe C A.dual A.turn A.arm
    let Q:=rank C A.weight A.dual
    let t:ℝ:=(AX).clock.monitor V.k
    ∀ᶠ N:ℕ in atTop,∀p:ℕ,∀fine:V.k<N,∀x:Points 2,tested AX V.b V.k x∈A.site→FitSky AX V.b V.k x→
      let Γ:=born R A.weight (tested AX V.b V.k x) z
      let ψ:=fun a=>(cell R V d (p:=p) check fine V.k (choose AX V.b V.k x) (Pi.single a 1) z)
      (∀a,rank C A.weight a≤Q→‖ψ a-Γ a‖*t^Q≤price R A D*t^(rank C A.weight a)*t^(-(0:ℝ)))∧
      (∀a,Q<rank C A.weight a→‖ψ a-Γ a‖≤price R A D)∧(∀a,rank C A.weight a≠Q→Γ a=0):=by
  classical
  intro d z Q t
  filter_upwards [sold] with N ear
  intro p fine x inside fit Γ ψ
  have painted (a:(R.family.labels.level A.weight).Index):
      ((D:ℝ)+1)*t^((Q-rank C A.weight a:ℕ):ℝ)*‖ψ a-Γ a‖≤budget R A:=by
    exact (ear p fine x inside fit a).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f:=fun i=>|fare R A i|) (fun _ _=>abs_nonneg _) (Finset.mem_univ a)))
  refine ⟨fun a q=>graded warm q (painted a),?_,?_⟩
  · intro a q
    apply (le_div_iff₀ (by positivity : 0<(D:ℝ)+1)).2
    have y:=painted a
    rw [Nat.sub_eq_zero_of_le q.le,Nat.cast_zero,Real.rpow_zero,mul_one] at y
    calc _=((D:ℝ)+1)*‖ψ a-Γ a‖:=by ring
         _≤_:=y
  · intro a q
    exact WilsonMeasuredPublicEntranceThermalRankPair.original C a A.dual A.turn A.arm _ q
end YM.Integration.WilsonPhysicalStationBasisIncome
end
