import YM.Integration.WilsonVacuumPreResetTorusClassicalReset
import YM.Integration.WilsonVacuumPreResetTorusDepositRows

/-! The complete deposited Wilson expression in the original finite-course
mass solver agrees on every coarse field with the independently regraded
classical, loop and interaction action, through the stated retained cap. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusRegradedAction
open Function Finset Lattice RG Gauge Pressure Precision Tree Stationary
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open AllOrder AllOrder.Ker AllOrder.Floe AllOrder.Floe.Step AllOrder.Haiku
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open PertExtension.Series PowerSeries
open WilsonVacuumPreResetTorusGrade (evaluated)
open WilsonVacuumPreResetTorusDeposit (address coordinates)
open WilsonVacuumPreResetTorusDepositRows (subtotal)
open scoped BigOperators Classical
variable {G:Gauge}{n:Side}

private def slot (p:Cost)(s:Age)(t:ℕ)(z:rule (Coarse G) n):SeriesA G→ℝ
  | []=>0
  | a::Z=> (if address a=s then evaluated (mix (pace p) (Mosaic.surf a n)) t z else 0)+slot p s t z Z

private theorem weighted (p:Cost)(unit:constantCoeff p=1)(s:Age)(t:ℕ)(z:rule (Coarse G) n)
    (Z:SeriesA G)(legal:∀a∈Z,3≤a.grade):
    (∑ i∈range (t+1),Pace.ladder (Pace.elapsed s) (Tested.term (p-1)) (t-i)*
      subtotal s i z Z)=slot p s t z Z:=by
  induction Z with
  | nil=>simp [subtotal,slot]
  | cons a Z ih=>
    have tail:=ih (fun v hv=>legal v (List.mem_cons_of_mem _ hv))
    by_cases hit:address a=s
    · subst s
      have position:=coordinates a (legal _ (List.mem_cons_self ..))
      rw [slot,if_pos rfl]
      simp only [subtotal,if_true,mul_add,sum_add_distrib,tail]
      congr 1
      rw [WilsonVacuumPreResetHomogeneousRows.deposited p unit]
      apply sum_congr rfl
      intro i hi
      simp only [Pace.elapsed,position.1,position.2,
        WilsonVacuumPreResetCoin.deposited p unit a.rankA,
        WilsonVacuumPreResetTorusDepositJet.original]
    · simpa only [slot,if_neg hit,subtotal,zero_add] using tail

private theorem roster (p:Cost)(unit:constantCoeff p=1){cap t:ℕ}(ht:t≤cap)(z:rule (Coarse G) n)
    (Z:SeriesA G)(legal:∀a∈Z,3≤a.grade):
    ∑s∈Age.scope cap,slot p s t z Z=evaluated (mix (pace p) (sands Z n)) t z:=by
  induction Z with
  | nil => simp [slot,sands,mix,WilsonVacuumPreResetTorusGrade.evaluated,Blue.flash,Blue.totalR]
  | cons a Z ih =>
    have tail:=ih (fun v hv=>legal v (List.mem_cons_of_mem _ hv))
    have head:shellK 2 (Mosaic.surf a n):=by simpa [sands] using sand_span [a] n
    rw [show sands (a::Z) n=Mosaic.surf a n+sands Z n from by simp [sands],
      WilsonVacuumPreResetTorusClassicalReset.combined _ head (sand_span Z n)]
    simp only [slot,sum_add_distrib,tail,Finset.sum_ite_eq]
    by_cases keep:address a∈Age.scope cap
    · rw [if_pos keep]
    · have stage:=coordinates a (legal _ (List.mem_cons_self ..))
      have late:t<a.grade:=by rw [Age.in_scope,stage.1] at keep; omega
      have unissued:evaluated (mix (pace p) (Mosaic.surf a n)) t z=0:=by
        rw [WilsonVacuumPreResetHomogeneousRows.deposited p unit]
        apply sum_eq_zero
        intro i hi
        have missed:¬ (a.grade ≤ i):=by rw [mem_range] at hi;omega
        simp [Haiku.Coat.trade,missed]
      rw [if_neg keep,unissued]

theorem original (p:Cost)(unit:constantCoeff p=1)(K:PathData G)(B:Clip)(Z:SeriesA G)
    {σ C:ℝ}(hs:0<σ)(price:Draw Z σ C)(legal:∀a∈Z,3≤a.grade){cap t:ℕ}(ht:t≤cap)
    (z:rule (Coarse G) n):
    Pace.grouping (Tested.term (p-1)) (WilsonVacuumPreResetTorusDeposit.bank Z) (Step.tape cap) B K t n z=
      evaluated (mix (pace p) (front K B n+sands Z n)) t z:=by
  have hfront:shellK 2 (front K B n):=by
    apply shell_sum (sprig_count (intended B K (m:=n)) 2)
    exact fun i a h=>sprig_count _ 0 i a (by omega)
  rw [WilsonVacuumPreResetTorusClassicalReset.combined _ hfront (sand_span Z n),
    WilsonVacuumPreResetTorusClassicalReset.original p unit,←roster p unit ht z Z legal]
  simp only [Pace.grouping,Pi.add_apply,Pace.glory,Finset.sum_apply]
  congr 1
  apply sum_congr rfl
  intro s _
  simp only [Pace.moiety,Pace.weigh_right,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  simp_rw [WilsonVacuumPreResetTorusDepositRows.original Z hs price legal]
  exact weighted p unit s t z Z legal

end YM.Integration.WilsonVacuumPreResetTorusRegradedAction
