import YM.Integration.WilsonPhysicalStationFullVote
import YM.Integration.WilsonPhysicalVaneBasis

/-! Restricting a compensated physical voter's coefficients by engineering degree and Wick rank gives another original voter on the same field chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationGradedVoter
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS Cells
open Trace.Terrace Trace.Over FVA2 FVA2.Register Trace.Physical.GermGraph Further.CorrectedLift
open Labels Next.Rank Next.Rank.East Next.Rank.Price MeasureTheory Trace MergeProof.East
open WilsonPhysicalVaneBasis (field)
open WilsonPhysicalStationThermalPair (raw)
open WilsonPhysicalStationThermalCoordinates (word)
open scoped Topology Classical BigOperators Matrix
variable {G:Gauge}(C:Family G)(h:ℕ)
local notation "F₀" => C.labels.level h

abbrev Bank (P:ℕ×ℕ→Prop):={a:(F₀).Index // P ((F₀).grades a)}

def portion (P:ℕ×ℕ→Prop)(u:(standard C).Field h):(standard C).Field h:=
  ∑i:Bank C h P,(ladder C h u i.val) • field C h i.val

theorem whole (P:ℕ×ℕ→Prop)(u:(standard C).Field h):
    portion C h P u+portion C h (fun g=>¬P g) u=u:=by
  let term:=(fun i=>(ladder C h u i) • field C h i)
  have split:=Fintype.sum_subtype_add_sum_subtype (fun i=>P ((F₀).grades i)) term
  refine Eq.trans ?_ (split.trans (WilsonPhysicalVaneBasis.resolve C h u))
  unfold portion
  apply congrArg₂ (·+·) <;> apply Finset.sum_congr (Finset.ext fun i=>by simp) <;> intro i _ <;> rfl

theorem outside (P:ℕ×ℕ→Prop)(u:(standard C).Field h)(j:(F₀).Index)(off:¬P ((F₀).grades j)):
    ladder C h (portion C h P u) j=0:=by
  unfold portion
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  have blank:ladder C h (field C h i.val) j=0:=by
    by_contra nz
    exact off ((WilsonPhysicalVaneBasis.pure C h i.val j nz).symm ▸ i.property)
  simp only [blank,mul_zero]

theorem tally (P:ℕ×ℕ→Prop)(u:(standard C).Field h)(j:(F₀).Index):
    ladder C h (portion C h P u) j=if P ((F₀).grades j) then ladder C h u j else 0:=by
  by_cases yes:P ((F₀).grades j)
  · rw [if_pos yes]
    have joined:=congrArg (fun v=>(ladder C h v) j) (whole C h P u)
    simpa only [map_add,Pi.add_apply,outside C h (fun g=>¬P g) u j (not_not.mpr yes),add_zero] using joined
  · rw [if_neg yes]
    exact outside C h P u j yes

variable (R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}{D:ℕ}(B:Vane R.family D)
    {h:ℕ}(db:h<D+1)(cb:B.checked f H D){N per:ℕ}(top:B.k<N)
set_option quotPrecheck false
local notation "axes" => (R.family.labels.level h).Index
theorem original (P:ℕ×ℕ→Prop)(u:(standard R.family).Field h):
    B.wheel.atCut (N,per) ⟨h,db⟩ (portion R.family h P u)=
      ∑i:Bank R.family h P,ladder R.family h u i.val • raw R B ⟨h,db⟩ (p:=per) cb top (Pi.single i.val 1):=by
  let W:=word R B ⟨h,db⟩ (p:=per) cb top
  let v:=ladder R.family h (portion R.family h P u)
  have decompose:(∑a:axes,v a • (Pi.single a 1:R.family.label h))=v:=by
    ext i
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
  have all:W v=∑a:axes,v a • W (Pi.single a 1):=by
    calc
      W v=W (∑a:axes,v a • Pi.single a 1):=congrArg W decompose.symm
      _=_:=by rw [map_sum];simp only [map_smul]
  rw [←WilsonPhysicalStationThermalPair.lifted R B ⟨h,db⟩ cb top]
  change W v=_
  rw [all,←Fintype.sum_subtype_add_sum_subtype (fun a:axes=>P ((R.family.labels.level h).grades a))
    (fun a:axes=>v a • W (Pi.single a 1))]
  rw [←add_zero (∑i:Bank R.family h P,ladder R.family h u i.val • raw R B ⟨h,db⟩ (p:=per) cb top (Pi.single i.val 1))]
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr (Finset.ext fun i=>by simp)
    intro i _
    have ep:v i.val=ladder R.family h u i.val:=(tally R.family h P u i.val).trans (if_pos i.property)
    rw [ep]
    rfl
  · apply Finset.sum_eq_zero
    intro i _
    have vacant:v i.val=0:=outside R.family h P u i.val i.property
    rw [vacant,zero_smul]

end YM.Integration.WilsonPhysicalStationGradedVoter
end
