import YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogGradeMarket
import YM.Integration.WilsonMatrixTicketLanesTerminalQSeries
import YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogWeights

/-! One absolute order for all submodes. Its regulator and period admit every original
reader, independently prescribed forest and placement of the actual finite Wilson row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogCohort
open Filter Function Finset Lattice Wilson RG RG12 RG17 Precision Tree Extraction Source Labels Spec
open MS MS.Land MS.Menus MS.Rake MS.Local.Physical PhysicalNext.Repeat.Legato
open RGComparison.Core16 RGComparison.Core16.Spool FVA2 FVA2.CityHistory
open Pert.Asymptotics
open WilsonMatrixTicketLanesTerminalQWords WilsonMatrixTicketLanesReportedPrepaid
open scoped Classical BigOperators Topology
variable {G:Gauge} {B:Deck G} {V:Type} [DecidableEq V] [Fintype V]
local notation "Γ" => Stock.census V

def enumerate (s:(Γ).Mode):Fin (Fintype.card s.val)≃s.val:=(Fintype.equivFin s.val).symm
def roster (u:V→Label B) (s:(Γ).Mode):Fin (Fintype.card s.val)→Label B:=
  fun i=>u ((enumerate s) i).val

def Window (R:Run G) (Q:Prescription B) {r:ℕ} (l:Fin r→Label B)
    (K cap guard E n:ℕ) (μ C:ℝ) (b:ℕ):Prop:=
  ∀(per:ℕ)(k:Fin r→ℕ),(∀i,k i≤K)→∀reader:Fin r→ℂ,
    let D:=R.family.path.levels.clock.op b per
    let g:=regulatorRun R.family (b+1) per (b+1)
    let θ:=μ-R.family.S.scale (b+1)
    ∀(large:Bid.Larger (G:=G) D)(T:Forest D.ratio)(pin:Pins G (R.family.side b per))
      (o:Fin r→Site (R.family.side (b+1) per))(tag:D.Choices)
      (v:(Descent.nil (top:=R.family.side (b+1) per)).Tags),
      (∀i,‖pin i‖≤(cap:ℝ)+1)→
      (‖WilsonMatrixTicketLanesTerminalQReturn.measured R Q l θ k reader pin o-
        WilsonMatrixTicketLanesTerminalQGrades.stack R Q l n θ k reader large T pin o tag v‖≤
          g^guard*∏i,‖reader i‖) ∧
      ∀j≤n,g^E*‖WilsonMatrixTicketLanesTerminalQSeries.term R Q l θ k reader j large T pin o tag v‖≤
        C*∏i,‖reader i‖

theorem purchased (R:Run G) (hG:G.Simple) (paid:Paid G R.kit) (Q:Prescription B)
    (u:V→Label B) (K cap:ℕ) (μ:ℝ):
    ∃(E:ℕ)(C:ℝ),0<C ∧ ∀q:ℕ,∃n≥q+E*Fintype.card V,
      (∀(s:(Γ).Mode)(z:∀i,Piece R (roster u s i)),power (word R (roster u s) z)≤n) ∧
      ∀ᶠ b:ℕ in atTop,∀s:(Γ).Mode,
        Window R Q (roster u s) K cap (q+E*Fintype.card V+1) E n μ C b:=by
  classical
  choose es cs cspos prices using fun s:(Γ).Mode=>
    WilsonMatrixTicketLanesTerminalQSeries.purchased R Q (roster u s) hG paid K cap μ
  let E:=univ.sup es
  let C:=1+∑s,cs s
  have capital:0<C:=by
    change 0<1+∑s,cs s
    have total:0≤∑s,cs s:=Finset.sum_nonneg fun i _=>(cspos i).le
    linarith
  refine ⟨E,C,capital,fun q=>?_⟩
  let guard:=q+E*Fintype.card V+1
  choose starts costs using fun s:(Γ).Mode=>
    WilsonPositionSeparatedProfileMayerInitialLogGradeMarket.purchased R Q (roster u s) hG paid K cap guard μ
  let n:=max guard (univ.sup starts)
  have ready s:starts s≤n:=(Finset.le_sup (f:=starts) (mem_univ s)).trans (le_max_right _ _)
  refine ⟨n,(Nat.le_succ _).trans (le_max_left _ _),fun s=>(costs s n (ready s)).1,?_⟩
  have actual:∀ᶠ b:ℕ in atTop,∀s:(Γ).Mode,_:=
    Filter.eventually_all.2 fun s=>(costs s n (ready s)).2
  have written:∀ᶠ b:ℕ in atTop,∀s:(Γ).Mode,_:=Filter.eventually_all.2 fun s=>prices s n
  obtain ⟨b₀,small⟩:=eventually_atTop.1 (IterationFour.Currency.g_small hG R.makes 1 zero_lt_one)
  filter_upwards [actual,written,eventually_ge_atTop b₀] with b real ink late
  intro s per k hk reader D g θ decomp T pin o tag marks inside
  refine ⟨real s per k hk reader decomp T pin o tag marks inside,fun j hj=>?_⟩
  have gp:0<g:=IterationFour.Currency.g_pos R.makes _ _ _ le_rfl
  have gl:g≤1:=(small (b+1) (by omega) (b+1) per le_rfl).le
  have exponent:es s≤E:=Finset.le_sup (f:=es) (mem_univ s)
  have cash:cs s≤C:=by
    have:=Finset.single_le_sum (s:=univ) (f:=cs) (fun i _=>(cspos i).le) (mem_univ s)
    change cs s≤1+∑i,cs i
    exact this.trans (le_add_of_nonneg_left zero_le_one)
  have signed:=ink s per k hk reader decomp T pin o tag marks inside j hj
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one gp.le gl exponent)
    (norm_nonneg _)).trans (signed.trans (mul_le_mul_of_nonneg_right cash
      (Finset.prod_nonneg fun _ _=>norm_nonneg _)))

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogCohort
