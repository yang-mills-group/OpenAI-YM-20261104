import YM.Integration.WilsonOriginalObservedRoseMeshPurse

/-! Independent fractional mesh losses on the precise rotated, shifted and
filed native votes, before dates, panels, directions and both regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterFiledIncome
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open PhysicalNext.Repeat.Legato Marker Motion
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonReceivedCanonicalVersePortfolio (Selection wallet weight)
open WilsonOriginalObservedRoseMeshPurse (quote)
open WilsonOriginalMicroscopicGuardedReporters (stretch)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n→ℕ)
local notation "C" => R.family
local notation "reg" => Stock.census (Fin n)

def Purchased (η:Fin n→ℝ)(L:ℕ):Prop:=
  ∀N per f K:ℕ,∀fk:f≤K,∀cut:K≤N,∀requested power t:ℕ,∀B:ℝ,
    ∀A:Panel R d N per f K fk cut requested power t B,∀file:Filed R d K,
    A.slot=file.station→A.axis=file.A N per→(∀i,L≤A.slot i)→f<N→
    let w:=votes R d (N:=N) (per:=per) file A.names A.turn
    let wage:=fun i=>quote R d (η i) (A.slot i) K N per i (A.names i)
    (∀i,((C).labels.level (d i)).coeffSize (w i)≤wage i) ∧
      ∀s:(reg).Mode,(∑q:Selection R d s.val,‖weight R d N per K w s.val q‖)≤wallet R d wage s.val

theorem earned (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (wide:∀j,1≤((C).path.levels.budget j).supportExponent)(η:Fin n→ℝ)(positive:∀i,0<η i):
    ∃L:ℕ,Purchased R d η L:=by
  choose first issue using fun i=>WilsonOriginalObservedRoseMeshPurse.original R d simple shop wide (positive i)
  refine ⟨univ.sup first,?_⟩
  intro N per f K fk cut requested power t B A file station axes late deep w wage
  have billed (i:Fin n):((C).labels.level (d i)).coeffSize (w i)≤wage i:=
    (issue i N per f K fk cut requested power t B A file station axes
      (fun j=>(le_sup (f:=first) (mem_univ i)).trans (late j)) deep).1 i
  exact ⟨billed,fun s=>WilsonReceivedCanonicalVersePortfolio.priced R d N per K cut w s.val wage
    (fun i _=>billed i)⟩

theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (wide:∀j,1≤((C).path.levels.budget j).supportExponent)(σ:ℝ)(sp:0<σ):
    ∃η:Fin n→ℝ,(∀i,0<η i) ∧ (∑i,η i)<σ ∧ ∃L:ℕ,Purchased R d η L:=by
  let η:Fin n→ℝ:=fun _=>σ/((n:ℝ)+1)
  have pos:∀i,0<η i:=fun _=>div_pos sp (by positivity)
  have sum:(∑i,η i)<σ:=by
    simp only [η,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [←mul_div_assoc,div_lt_iff₀ (by positivity:0<(n:ℝ)+1)]
    nlinarith only [sp]
  exact ⟨η,pos,sum,earned R d simple shop wide η pos⟩

theorem stretches (η:Fin n→ℝ)(positive:∀i,0≤η i)(s:Finset (Fin n))(K:ℕ)(j:Fin n→ℕ)
    (L σ:ℝ)(lp:0≤L)(all:(∑i,η i)≤σ)(span:∀i∈s,(C).S.scale K-(C).S.scale (j i)≤L):
    (∏i∈s,stretch R (η i) (j i) K)≤2^s.card*Real.exp (σ*L):=by
  have bounded:(∑i∈s,η i*((C).S.scale K-(C).S.scale (j i)))≤σ*L:=calc
    _≤∑i∈s,η i*L:=sum_le_sum fun i hi=>mul_le_mul_of_nonneg_left (span i hi) (positive i)
    _=(∑i∈s,η i)*L:=(sum_mul ..).symm
    _≤σ*L:=mul_le_mul_of_nonneg_right
      ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun i _ _=>positive i)).trans all) lp
  simp only [WilsonOriginalMicroscopicGuardedReporters.stretch,prod_mul_distrib,prod_const,←Real.exp_sum]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr bounded) (by positivity)

end YM.Integration.WilsonOriginalGeneralRosterFiledIncome
end
