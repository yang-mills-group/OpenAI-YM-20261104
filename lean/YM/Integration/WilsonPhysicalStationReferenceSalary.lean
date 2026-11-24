import YM.Integration.WilsonPhysicalStationDatedSalary
import YM.Integration.WilsonPhysicalStationEndpointFactor

/-! Fixed-date cutoff-uniform control of the original physical label at its
own reference, including the scalar coordinate. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationReferenceSalary
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories
open Next.Rank Next.Rank.East Next.Rank.Price MergeProof.East
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph OPE Work.G08
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress
open WilsonPhysicalStationDatedSalary (datedMass span)
open WilsonPhysicalStationRawReading (err)
open WilsonPhysicalStationThermalCoordinates (filed)
open WilsonPhysicalStationFineCorrection (measured)
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G)
local notation "C" => R.family

theorem original (h m N p:ℕ) (y:(C).label h) (start:(C).ref h ≤ m) (top:m ≤ N):
    ‖y‖ ≤ span R ((C).ref h) m^(h+1)*datedMass R h N p y m:=by
  let r:=(C).ref h
  let K:=(C).factory h N p
  have received:(WilsonPhysicalStationFactoryGerm.incoming R h N p y r).x = y:=
    (Columns.readTerminal R.makes (start.trans top) (K.terminal.symm y)).trans (K.terminal.apply_symm_apply y)
  have date:r+(m-r)=m:=by dsimp [r];omega
  have term:=WilsonPhysicalStationDatedSalary.falling R h N p y r (m-r) le_rfl (by omega : r+(m-r) ≤ N)
  rw [date] at term
  apply (Extra.Histories.Size.norm_le ((C).labels.level h) y).trans
  exact (congrArg ((C).labels.level h).coeffSize received).ge.trans term

variable {D:ℕ} (A:Vane R.family D) (d:Fin (D+1)) (e:ℕ) {N p:ℕ}
local notation "F₀" => R.family.labels.level d
local notation "μ" => (F₀).coeffSize
local notation "U" => (shrink R.family A.k N p)⁻¹
local notation "M" => Station.mag (C).path.levels A.b A.k
local notation "low" => Columns.low (F₀) e

theorem coffer (top:A.k ≤ N) (h:d.val=e+1)(y:(C).label d)
    (cleared:(low) (A.R N p d y)=0):
    μ (measured R A d N p y)=((C).S.a A.k*(M))^d.val*
       ∑i,‖filed R A d N p y i‖*(U)^((F₀).grades i).2:=by
  unfold Frame.coeffSize
  rw [mul_sum];apply sum_congr rfl
  intro i _
  have row:=congrArg norm (WilsonPhysicalStationEndpointFactor.written R A d (p:=p) top y i)
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (WilsonPhysicalStationEndpointFactor.row_pos R A d
    (p:=p) top ((F₀).grades i).1 ((F₀).grades i).2).le] at row
  apply row.trans
  by_cases ho:((F₀).grades i).1=d.val
  · rw [ho,WilsonPhysicalStationEndCurrency.row,mul_pow];ring
  · have entry:=WilsonPhysicalStationHorizontalWallet.fromLower (F₀) e _ cleared h i
      (lt_of_le_of_ne ((F₀).bound i) ho)
    have gone:filed R A d N p y i=0:=by
      change (_:ℂ)^_*((_:ℂ)*A.R N p d y i)=0
      rw [entry,mul_zero,mul_zero]
    rw [gone,norm_zero,mul_zero,zero_mul,mul_zero]

theorem bag {ι:Type*} [Fintype ι] [DecidableEq ι] {t A g J p:ℝ} (a:ι)
    (c:ι→ℂ)(χ:ℂ)(q:ι→ℕ)(gate:0 ≤ t)(pos:0 ≤ p)
    (source:t*‖χ‖*p^(q a) ≤ A*J)
    (coeff:∀i,t*‖c i-χ*(Pi.single a (1:ℂ):ι→ℂ) i‖*p^(q i) ≤ g*J):
    t*(∑i,‖c i‖*p^(q i)) ≤ ((Fintype.card ι:ℝ)*g+A)*J:=by
  classical
  let entry:=fun i=>χ*(Pi.single a (1:ℂ):ι→ℂ) i
  let rest:=fun i=>c i-entry i
  have price (i:ι):t*(‖c i‖*p^(q i)) ≤ g*J+t*‖entry i‖*p^(q i):=by
    have h:=norm_add_le (rest i) (entry i)
    rw [show rest i+entry i=c i by exact sub_add_cancel ..] at h
    have line:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h gate) (pow_nonneg pos (q i))
    calc
       _=t*‖c i‖*p^(q i):=by ring
       _ ≤ _:=line.trans (calc 
           _=t*‖rest i‖*p^(q i)+t*‖entry i‖*p^(q i):=by ring
           _ ≤ _:=add_le_add (coeff i) le_rfl)
  rw [mul_sum]
  apply (sum_le_sum (fun i _=>price i)).trans
  rw [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul]
  have one:(∑ i,t*‖entry i‖*p^(q i))=t*‖χ‖*p^(q a):=by
    rw [Finset.sum_eq_single a]
    · simp [entry]
    · intro i _ hi; simp [entry,Pi.single_eq_of_ne hi]
    · simp
  rw [one,add_mul,mul_assoc (Fintype.card ι:ℝ) g J]
  exact add_le_add le_rfl source

end YM.Integration.WilsonPhysicalStationReferenceSalary
end
