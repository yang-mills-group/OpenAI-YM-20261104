import YM.Integration.WilsonPhysicalStationThermalRefund

/-! The finite family of signed rows is bought before either regulator.
On each common original Wilson cutoff it can then be evaluated on any
of the inherited, cutoff-dependent linear combinations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationThermalRawMenu
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
variable {G:Gauge}(R:Run G)(B:Binding R.family)(O:HaarBudget G)(J:ChartRatio G)
    {f:Extraction.Order}{S:(Bel R.family.book).Hierarchy}{h D u:ℕ}
    (V:Vane R.family h)(d:Fin (h+1))(checked:V.checked f S h)
    {K:Set (Points 2)}{z bound:ℝ}(P:Tapes.Panel D)
local notation "C"=>R.family
local notation "AX"=>R.family.path.levels

set_option quotPrecheck false
local notation "I"=>(R.family.labels.level d).Index

def gap (a:I)(Q:ℕ):Fin 2→ℕ:=![(R.family.labels.level d).grades a |>.2,Q]

theorem clock (k:ℕ)(u:ℕ)(paid:2≤u):
    let T:=R.family.path.levels.clock.monitor k
    1≤T ∧ 1≤T*T^(-(1/(16*(u:ℝ)))):=by
  let T:=R.family.path.levels.clock.monitor k
  have warm:1≤T:=Real.one_le_exp (sq_nonneg _)
  have hot:=zero_lt_one.trans_le warm
  have small:1/(16*(u:ℝ))≤1:=by
    have two:(2:ℝ)≤u:=by exact_mod_cast paid
    exact (div_le_iff₀ (by linarith:0<16*(u:ℝ))).mpr (by linarith)
  have interval:0≤1+ -(1/(16*(u:ℝ))):=by linarith
  have goal:=Real.one_le_rpow warm interval
  rw [Real.rpow_add hot,Real.rpow_one] at goal
  exact ⟨warm,goal⟩

theorem original (y:(standard R.family).Field d)(Q:ℕ)(two:2≤u)
    (ink:WilsonMovingForkReporterNamedInk.Filed B R.makes O J P V u z)
    (L H:I→ℝ)
    (low:∀a:I,((R.family.labels.level d).grades a).2≤Q →
       WilsonReporterWeightedRankEpoch.Result B R.makes O J (u:=u) (K:=K) (d:=fun _:Fin 2=>d.val)
         (votes R d (Pi.single a 1) y) P (gap R d a Q) V.k (L a) z)
    (high:∀a:I,Q<((R.family.labels.level d).grades a).2 →
       WilsonReporterWeightedRankEpoch.Result B R.makes O J (u:=u) (K:=K) (d:=fun _:Fin 2=>d.val)
         (votes R d (Pi.single a 1) y) P (fun _=>0) V.k (H a) z):
    let A:ℝ:=∑a:I,(|L a|+|H a|)
    0≤A ∧ ∀ᶠ N:ℕ in atTop,∀ p:ℕ,∀ fine:V.k<N,∀ ξ:Points 2,
      tested AX V.b V.k ξ∈K → FitSky AX V.b V.k ξ →
      let T:=R.family.path.levels.clock.monitor V.k
      let err:=fun a:I=>cell R V d (p:=p) checked fine V.k (choose AX V.b V.k ξ) (Pi.single a 1) y -
         (standard R.family).classMoment (standard R.family) (fun _:Fin 2=>d.val)
             (tested AX V.b V.k ξ) ![(standard R.family).project d (Pi.single a 1),y]
      ∀a:I,( ((R.family.labels.level d).grades a).2≤Q →
         ‖err a‖*T^Q≤A*T^((R.family.labels.level d).grades a).2*T^(-(1/(16*(u:ℝ))))) ∧
         (Q<((R.family.labels.level d).grades a).2 → ‖err a‖≤A):=by
  let bill:ℝ:=∑a:I,(|L a|+|H a|)
  have sale (a:I):L a≤bill ∧ H a≤bill:=by
    have s:|L a|+|H a|≤bill:=Finset.single_le_sum (f:=fun c:I=>|L c|+|H c|)
      (fun c _=>add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ a)
    constructor <;> linarith only [s,abs_nonneg (L a),abs_nonneg (H a),le_abs_self (L a),le_abs_self (H a)]
  refine ⟨Finset.sum_nonneg (fun _ _=>add_nonneg (abs_nonneg _) (abs_nonneg _)),?_⟩
  let T:=R.family.path.levels.clock.monitor V.k
  have warm:1≤T:=(clock R V.k u two).1
  have hot:=zero_lt_one.trans_le warm
  let κ:ℝ:=1/(16*(u:ℝ))
  have posκ:0≤κ:=by dsimp [κ];positivity
  have moneys (a:I): ∀ᶠ N:ℕ in atTop,∀ p:ℕ,∀ fine:V.k<N,∀ ξ:Points 2,
      tested AX V.b V.k ξ∈K → FitSky AX V.b V.k ξ →
      let err:=cell R V d (p:=p) checked fine V.k (choose AX V.b V.k ξ) (Pi.single a 1) y -
         (standard R.family).classMoment (standard R.family) (fun _:Fin 2=>d.val)
             (tested AX V.b V.k ξ) ![(standard R.family).project d (Pi.single a 1),y]
      ( ((R.family.labels.level d).grades a).2≤Q →
         ‖err‖*T^Q≤bill*T^((R.family.labels.level d).grades a).2*T^(-κ)) ∧
         (Q<((R.family.labels.level d).grades a).2 → ‖err‖≤bill):=by
    by_cases leg:((R.family.labels.level d).grades a).2≤Q
    · have rank:(gap R d a Q 0)≤gap R d a Q 1:=leg
      filter_upwards [WilsonPhysicalStationThermalRefund.original R B O J V d checked P (Pi.single a 1)
        y (gap R d a Q) rank ink (low a leg)] with N hearing
      intro p fine ξ live fit
      refine ⟨fun _=>(hearing p fine ξ live fit).trans ?_,fun impossible=>(Nat.not_lt.mpr leg impossible).elim⟩
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (sale a).1 (pow_nonneg hot.le _))
        (Real.rpow_pos_of_pos hot _).le
    · have upper:=Nat.lt_of_not_ge leg
      filter_upwards [WilsonPhysicalStationThermalFiledPair.original R B O J V d checked P (Pi.single a 1)
        y (fun _=>0) ink (high a upper)] with N hearing
      intro p fine ξ live fit
      refine ⟨fun impossible=>(leg impossible).elim,fun _=>?_⟩
      have out:=hearing p fine ξ live fit
      simp only [Nat.sub_self,Nat.cast_zero,zero_add] at out
      exact (le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_rpow warm posκ)).trans (out.trans (sale a).2)
  filter_upwards [Filter.eventually_all.mpr moneys] with N hearing
  intro p fine ξ live fit
  dsimp only
  exact fun a=>hearing a p fine ξ live fit

end YM.Integration.WilsonPhysicalStationThermalRawMenu
end
