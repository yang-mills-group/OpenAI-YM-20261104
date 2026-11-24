import YM.Integration.WilsonVacuumPreResetTorusDepositRows
import YM.AllOrder.Floe.Circle

/-! The deposited layout and the full independent action have the same
unmasked radial mass at every retained grade, before the kinetic change. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusDepositedMass
open Function Filter Finset Lattice RG Wilson Gauge Pressure Precision Tree
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Ker AllOrder.Ker.Start
open AllOrder.Haiku Haiku.Coat AllOrder.Fire AllOrder.Ink Ink.Money
open Laurent Stationary Primitives.TwoWave Primitives.TwoWave.RealSlice
open Comparison.RG02 WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Blue PowerSeries WilsonVacuumPreResetTorusGrade
open WilsonVacuumPreResetTorusDeposit WilsonVacuumPreResetTorusDepositRows
open scoped Classical BigOperators

variable {G:Gauge}{n:Side}

private theorem roster (Z:SeriesA G)(grades:∀a∈Z,3≤a.grade)
    {t cap:ℕ}(ht:t≤cap)(z:rule (Coarse G) n):
    (∑ i∈Age.scope cap,subtotal i t z Z)=
      (Z.map fun a=>evaluated (Mosaic.surf a n) t z).sum:=by
  induction Z with
  | nil => simp [subtotal]
  | cons a T ih =>
    have h:=coordinates a (grades a (List.mem_cons_self ..))
    have tail:=ih (fun b hb=>grades b (List.mem_cons_of_mem _ hb))
    let v:=evaluated (Mosaic.surf a n) t z
    have each (i:Age):subtotal i t z (a::T)=
        (if address a=i then v else 0)+subtotal i t z T:=by
      by_cases hit:address a=i <;> simp [subtotal,hit,v]
    rw [Finset.sum_congr rfl (fun i _=>each i),Finset.sum_add_distrib,tail]
    simp only [List.map_cons,List.sum_cons,Finset.sum_ite_eq]
    by_cases active:address a∈Age.scope cap
    · rw [if_pos active]
    · have late:t<a.grade:=by
        rw [Age.in_scope,h.1] at active
        omega
      have zero:v=0:=by
        rw [show v=evaluated (Mosaic.surf a n) t z from rfl,
          WilsonVacuumPreResetTorusDepositJet.original,trade,if_neg (by omega)]
        rfl
      rw [if_neg active,←zero]

private theorem add {P Q:PChart G n}(h:shellK 2 P)(q:shellK 2 Q)
    (t:ℕ)(z:rule (Coarse G) n):
    evaluated (P+Q) t z=evaluated P t z+evaluated Q t z:=by
  simp only [WilsonVacuumPreResetTorusGrade.evaluated,flash_add (finite_shell h) (finite_shell q),map_add]

private theorem sand (Z:SeriesA G)(t:ℕ)(z:rule (Coarse G) n):
    evaluated (sands Z n) t z=(Z.map fun a=>evaluated (Mosaic.surf a n) t z).sum:=by
  induction Z with
  | nil => simp [sands,WilsonVacuumPreResetTorusGrade.evaluated,Blue.flash,Blue.totalR]
  | cons a T ih =>
    have bounded:shellK 2 (Mosaic.surf a n):=by
      simpa [sands] using sand_span [a] n
    change evaluated (Mosaic.surf a n+sands T n) t z=_
    rw [add bounded (sand_span T n),ih]
    rfl

theorem original (K:PathData G)(B:Clip)(Z:SeriesA G){σ C:ℝ}(hs:0<σ)(price:Draw Z σ C)
    (grades:∀a∈Z,3≤a.grade){t cap:ℕ}(ht:t≤cap)(z:rule (Coarse G) n):
    Pace.grouping 0 (bank Z) (Step.tape cap) B K t n z=
      evaluated (front K B n+sands Z n) t z:=by
  have hmain:=sprig_count (intended B K (m:=n)) 2
  have hloop:shellK 2 (sprig (turnSeries K.loop (m:=n)) 0):=
    fun j l h=>sprig_count _ 0 j l (by omega)
  rw [front,add (shell_sum hmain hloop) (sand_span Z n),add hmain hloop,sand,
    WilsonVacuumPreResetTorusDepositJet.classical,WilsonVacuumPreResetTorusDepositJet.loop,
    ←roster Z grades ht]
  simp only [Pace.grouping,Pace.shiftB,Pace.glory,Pi.add_apply,Crest.nogo,
    add_zero,Finset.sum_apply,Pace.moiety,Crest.gone,Crest.nostep]
  congr 1
  exact Finset.sum_congr rfl fun i _=>WilsonVacuumPreResetTorusDepositRows.original Z hs price grades i t z

end YM.Integration.WilsonVacuumPreResetTorusDepositedMass
