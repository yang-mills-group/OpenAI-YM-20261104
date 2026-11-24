import YM.Integration.WilsonFactoryReportedChart
import YM.Integration.WilsonPhysicalMarkedDefectStoredInterior

/-! On the actual normalized reporting coefficient, the fitted part uses the
true independently boxed graded atoms. All remaining signed material stays
on this same coefficient and with its paid original support. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFactoryReportingBox
open Function Finset Lattice Wilson Labels RG Source Spec RG12
open PhysicalNext.Repeat.Legato Extra.Histories Pert.Asymptotics RG16 RG16.Literal
open Trace.Physical.GermGraph PertExtension PertExtension.LatticePT
open FVA2 FVAAlt2 WilsonPhysicalMarkedDefect
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
  (F : Final R.family f S) (d k : ℕ) (j : UVIndex)
local notation "E" => R.family.labels.level d
local notation "A" => R.family.path.rep (Prod.fst j) (Prod.snd j) k
local notation "g" => regulatorRun R.family (Prod.fst j) (Prod.snd j) k
variable (v : R.family.label d)

def row :=
  (R.family.factory d j.1 j.2).entries k ((R.family.factory d j.1 j.2).terminal.symm
    (WilsonFactoryReportedChart.pulled R F d k j v))

def price : (E).Coeff := gMap R.family j.1 j.2 d k ((E).core v)

def stamp := WilsonFactoryBoxedFields.label R d (price R d k j v)

theorem booked : (R.family.labels.level d).coords (stamp R d k j v) =
    (topMatrix (R.family.localSection d) R.family.params (R.makes.sections d) (Block.clothes R d)).conversion
      (covarianceSymbol G) (price R d k j v) := by
  exact (E).coords.apply_symm_apply _

def atom (i : (E).Index) (U : Config G (R.family.side k j.2)) : ℂ :=
  ((g : ℂ)^((E).grades i).2)⁻¹ * ((FVA2.Source.put (Plate.bare (R.family.localSection d) i) 0 U : ℝ) : ℂ)

def boxed (U : Config G (R.family.side k j.2)) : ℂ :=
  ∑ i : (E).Index, price R d k j v i * atom R d k j i U

def rest (U : Config G (R.family.side k j.2)) : ℂ :=
  StoredInterior.failed R.family j.1 j.2 d k (row R F d k j v) U +
    (∑' i, (row R F d k j v).maskedTerm A i U) +
    StoredInterior.hard R.family j.1 j.2 d k (row R F d k j v) U

theorem fitted (h : R.family.ref d ≤ k) (hj : k ≤ j.1) (U : Config G (R.family.side k j.2)) :
    StoredInterior.fitted R.family j.1 j.2 d k (row R F d k j v) U = boxed R d k j v U := by
  have hx : (row R F d k j v).x = v := WilsonFactoryReportedChart.head R F d k h j hj v
  unfold StoredInterior.fitted boxed
  apply Finset.sum_congr rfl
  intro i _
  rw [StoredInterior.amplitude,hx]
  unfold price StoredInterior.basis atom
  rw [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow,Plate.bare_put]
  have physical : (↑(PertExtension.Orb.SlotEvaluation.fieldAt (R.family.localSection d) i 0 U) : ℂ) =
      (R.family.localSection d).places (Pi.single i 1) 0 U :=
    PertExtension.Orb.SlotEvaluation.scalar_real (R.makes.sections d)
  rw [physical]

/-- The complete original all-field comparison, not an estimate replacing
the failed fit or the original hard numerator by its unconditioned activity. -/
structure Receipt : Prop where
  input : (row R F d k j v).x = v
  format : (row R F d k j v).Format 0 R.family.params A
  remainder : (row R F d k j v).remBound 0 A (Real.sqrt (R.family.path.levels.clock.forcedAllowance k))
    ((R.family.path.levels.params k).columns * (E).coeffSize ((E).core v))
  purchased : ∑ i : (E).Index, ‖price R d k j v i‖ ≤
    (2:ℝ)^(Finset.univ.sup (fun i : (E).Index => ((E).grades i).2))*mass R.family d v
  field : ∀ U, (row R F d k j v).density 0 (R.family.localSection d) A U / ((A).eval U:ℂ) =
    v 0 + boxed R d k j v U + rest R F d k j v U

theorem issued (h : R.family.ref d ≤ k) (hj : k ≤ j.1) : Receipt R F d k j v := by
  let y := (R.family.factory d j.1 j.2).terminal.symm (WilsonFactoryReportedChart.pulled R F d k j v)
  have hx : (row R F d k j v).x = v := WilsonFactoryReportedChart.head R F d k h j hj v
  have sale := R.makes.calibrated d j.1 j.2 (h.trans hj)
  have hc := sale.cap k h hj y
  change (row R F d k j v).remBound _ _ _ (_ * (E).coeffSize ((E).core (row R F d k j v).x)) at hc
  rw [hx] at hc
  refine ⟨hx,sale.format k h hj y,hc,?_,?_⟩
  · have ha : (E).coeffSize (row R F d k j v).x ≤ mass R.family d v := by rw [hx]; rfl
    have result := StoredInterior.price R.family j.1 j.2 d k R.makes hj (row R F d k j v) ha
    simpa only [StoredInterior.amplitude,price,hx] using result
  · intro U
    rw [StoredInterior.resolved R.family j.1 j.2 d k R.makes hj,hx,fitted R F d k j v h hj]
    unfold rest
    abel

end YM.Integration.WilsonFactoryReportingBox
