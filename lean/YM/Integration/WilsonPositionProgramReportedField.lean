import YM.Integration.WilsonPhysicalMarkedDefectStoredInterior
import YM.RG12.Canonical.Charts
import YM.Integration.WilsonPositionProgramSourceCalibration
import YM.Integration.ActualRunKernelPackets

/-! A prescribed numerical column on the true normalized reporting row. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramReportedField
open Function Finset Lattice Wilson Labels RG Source Spec RG12
open PhysicalNext.Repeat.Legato Extra.Histories Pert.Asymptotics RG16 RG16.Literal
open Trace.Physical.GermGraph PertExtension PertExtension.LatticePT
open FVA2 FVAAlt2 WilsonPhysicalMarkedDefect
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) (d k : ℕ) (j : UVIndex)
local notation "E" => R.family.labels.level d
local notation "A" => R.family.path.rep j.1 j.2 k
local notation "g" => regulatorRun R.family j.1 j.2 k
local notation "τ" => (A).p.threshold

def row (v:R.family.label d) :=
  (R.family.factory d j.1 j.2).entries k ((R.family.factory d j.1 j.2).terminal.symm
    (atK R.family R.makes d k j v))

private theorem row_head (ref:R.family.ref d≤k) (live:k≤j.1) (v:R.family.label d) :
    (row R d k j v).x=v := by
  have sold := (RG12.charts R.family R.makes d k j).apply_symm_apply v
  rw [RG12.charts,dif_pos ⟨ref,live⟩] at sold
  change ((R.family.factory d j.1 j.2).entries k ((R.family.factory d j.1 j.2).terminal.symm
    ((RG12.charts R.family R.makes d k j).symm v))).x=v
  rw [RG12.charts,dif_pos (show R.family.ref d ≤ k ∧ k ≤ j.1 from ⟨ref,live⟩)]
  exact sold

def rest (v:R.family.label d) (U:Config G (R.family.side k j.2)) : ℂ :=
  StoredInterior.failed R.family j.1 j.2 d k (row R d k j v) U +
  (∑' i,(row R d k j v).maskedTerm A i U) +
  StoredInterior.hard R.family j.1 j.2 d k (row R d k j v) U

def price (v:R.family.label d) := gMap R.family j.1 j.2 d k ((E).core v)
abbrev atom := StoredInterior.basis R.family j.1 j.2 d k
def boxed (v:R.family.label d) (U:Config G (R.family.side k j.2)) : ℂ :=
  ∑ i, price R d k j v i * atom R d k j i U

def coordinate (c : (E).Coeff) : R.family.label d := (E).scaled (τ/g) c

theorem price_return (live : k ≤ j.1) (c : (E).Coeff) :
    price R d k j (coordinate R d k j c) = (E).core c := by
  have hg : 0<g := ActualRunKernelPackets.regulator_pos R j.1 j.2 k live
  have ht : 0<τ := (A).p.threshold_pos
  have ratio : g/τ * (τ/g) = 1 := by field_simp
  funext i
  by_cases zero : i=0
  · subst i
    simp [price,gMap,Frame.scaled_apply,Frame.core]
  · simp only [price,gMap,Frame.scaled_apply,Frame.core,LinearMap.coe_mk,AddHom.coe_mk,
      Function.update_of_ne zero,coordinate,←mul_assoc,←Complex.ofReal_mul,←mul_pow,ratio,
      one_pow,Complex.ofReal_one,one_mul]

theorem unit (U : Config G (R.family.side k j.2)) : atom R d k j 0 U = 1 := by
  have hu : (R.family.localSection d).places (Pi.single 0 1) 0 U = 1 :=
    congrFun (R.makes.sections d).unit (expandAt 0 U)
  simp [atom,StoredInterior.basis,Frame.zero_degree,hu]

theorem head (live:k≤j.1) (c:(E).Coeff) (U:Config G (R.family.side k j.2)) :
    coordinate R d k j c 0 + boxed R d k j (coordinate R d k j c) U =
      ∑ i, c i * atom R d k j i U := by
  have split (i:(E).Index) :
      c i * atom R d k j i U =
      (if i=0 then c 0 else 0) + ((E).core c) i * atom R d k j i U := by
    by_cases h:i=0
    · subst i
      simp [unit,Frame.core]
    · simp [h,Frame.core]
  simp_rw [split,Finset.sum_add_distrib]
  unfold boxed
  rw [price_return R d k j live c]
  simp [coordinate,Frame.zero_degree]

theorem field (ref : R.family.ref d ≤ k) (live:k≤j.1) (c:(E).Coeff)
    (U:Config G (R.family.side k j.2)) :
    (row R d k j (coordinate R d k j c)).density 0 (R.family.localSection d) A U /
      ((A).eval U:ℂ) = (∑ i, c i * atom R d k j i U) +
      rest R d k j (coordinate R d k j c) U := by
  let v:=coordinate R d k j c
  have fix:=row_head R d k j ref live v
  have fitted : ∀ U, StoredInterior.fitted R.family j.1 j.2 d k (row R d k j v) U =
      boxed R d k j v U := fun U=>by
    simp only [StoredInterior.fitted,StoredInterior.amplitude,fix,boxed,price,atom]
  change (row R d k j v).density 0 (R.family.localSection d) A U / ((A).eval U:ℂ) = _
  rw [StoredInterior.resolved R.family j.1 j.2 d k R.makes live,fix,fitted,
    head R d k j live]
  unfold rest
  abel

def entire (v:R.family.label d) := gMap R.family j.1 j.2 d k v

theorem recovered (live:k≤j.1) (v:R.family.label d) :
    coordinate R d k j (entire R d k j v)=v := by
  have hg : 0<g := ActualRunKernelPackets.regulator_pos R j.1 j.2 k live
  have ht : 0<τ := (A).p.threshold_pos
  have ratio : τ/g * (g/τ) = 1 := by field_simp
  funext i
  simp only [coordinate,entire,gMap,Frame.scaled_apply,←mul_assoc,
    ←Complex.ofReal_mul,←mul_pow,ratio,one_pow,Complex.ofReal_one,one_mul]

theorem original (ref:R.family.ref d≤k) (live:k≤j.1) (v:R.family.label d)
    (U:Config G (R.family.side k j.2)) :
    (row R d k j v).density 0 (R.family.localSection d) A U / ((A).eval U:ℂ) =
      (∑ i, entire R d k j v i * atom R d k j i U) + rest R d k j v U := by
  simpa only [recovered R d k j live] using field R d k j ref live (entire R d k j v) U

theorem purchased (live:k≤j.1) (v:R.family.label d) :
    (E).coeffSize (entire R d k j v) ≤ 2^(Finset.univ.sup (fun i : (E).Index => ((E).grades i).2)) *
      RG12.mass R.family d v :=
  WilsonMasterCoordinatePrice.positive_grade R.makes j.1 j.2 d k live v

variable {B : MS.Local.Physical.Deck G}
theorem registered (v:MS.Rake.Label B) (ref : R.family.ref v.h ≤ k) (live:k≤j.1)
    (U:Config G (R.family.side k j.2)) :
    let c:=YM.FVAAlt2.Lobby.γ (RegulatorIR.FVAAlt2.Lodge.basisR R) v
    let x:=coordinate R v.h k j c
    (row R v.h k j x).density 0 (R.family.localSection v.h) A U / ((A).eval U:ℂ) =
      ((g:ℂ)^v.item.1.val)⁻¹ * WilsonRichPrimitiveRows.incoming R v g 0 U +
      rest R v.h k j x U := by
  dsimp only
  rw [field R v.h k j ref live,
    WilsonRichPrimitiveRows.scale R v (ActualRunKernelPackets.regulator_pos R j.1 j.2 k live).ne']
  congr 1
  refine sum_congr rfl fun i _=>?_
  rw [WilsonRichPrimitiveRows.price R v i,atom,StoredInterior.basis,Complex.real_smul,
    Complex.ofReal_inv,Complex.ofReal_pow,mul_assoc]

end YM.Integration.WilsonPositionProgramReportedField
