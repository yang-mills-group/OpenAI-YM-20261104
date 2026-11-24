import YM.Integration.WilsonReportingMeasuredWardSourceGerm
import YM.Planned.ATOM_GUARDED_LAYOUT.Guards

/-! A fresh unmasked source on the actual occupied addresses of the earlier Wilson measure. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingGuardedSource
open Lattice Wilson RG Source Labels Extra.Histories Next.Foundations
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open Planned.GuardedAtom.Guard Progress.DirectedRecipe
open private plate lawful demo from YM.Planned.ATOM_GUARDED_LAYOUT.Guards
open scoped Classical BigOperators

variable {G:Gauge} {R:Run G} {T:Campaign R} (W:Campaign.Pillars R T) {m N per:ℕ}
local notation "F" => R.family.labels.level 4
local notation "S" => R.family.localSection 4
local notation "P" => R.family.path.rep N per m

def field (life:m ≤ N) (o:Site (R.family.side m per)) (q:ℕ) (x:R.family.label 4):
    Coefficient F (R.family.side m per):=
  let slots:=(W.yields N per).slots m (Nat.zero_le _) life
  born S (plate P) o (demo (Keeper.blank slots)) q x

/-- The seed includes the actual signed rough supplement on the same old forced layout. -/
theorem purchased (life:m ≤ N) (age:R.family.ref 4 ≤ m) (o:Site (R.family.side m per))
    (q:ℕ) (x:R.family.label 4):
    let h:=field W life o q x
    h.Format o R.family.params P ∧
    h.remBound o P (Trace.Physical.GermGraph.safety R.family m) ((F).coeffSize ((F).core x)) ∧
    h.x=x ∧ h.regular=0 ∧
    ∀ U,h.density o S P U=((P).eval U:ℂ)*(S).places ((F).scaled (P).p.threshold⁻¹ x) o U := by
  let slots:=(W.yields N per).slots m (Nat.zero_le _) life
  let H:=Keeper.sufficient slots
  let D:=demo (Keeper.blank slots)
  let y:=born S (plate P) o D q x
  let stage:=R.makes.wilson.represents N per m life
  have hm:4 ≤ R.alloy.B.a.clock.J m:=((Nat.le_add_right 4 3).trans (R.accepts 4)).trans (R.alloy.B.a.fits.mono age)
  have bill:= (R.b.clock.sequences m 4 hm).receipts per o
  have pay:= (launched S (plate P) o D (sound G 4) (lawful stage.good)
    (forcedPos R.family.path.levels m) (Doors.cameras_ge G 4)
    (fun i U=>Doors.cameras_holds G 4 _ i o U) (stage.vac.symm ▸ bill) q).2 x
  have form:y.Format o R.family.params (plate P):=pay.1
  have guard (i:ℕ) (U:Config G (R.family.side m per)) (taken:y.forced i U≠0):
      ((P).activities.forced i).eligible (P).p.threshold U:=by
    have spot:= (form.forcing i U taken).1
    change ((P).activities.forced i).support ∩ flags (P).p.threshold U=((P).activities.forced i).inventory at spot
    refine ⟨spot,?_⟩
    obtain ⟨s,rfl⟩:∃ s,H.code s=i:=by
      by_contra no
      apply taken
      change Attach.line (plate P) ((S).footprint o) D q _ i U=0
      rw [Attach.line_empty]
      · rfl
      rintro ⟨s,hs⟩
      exact no ⟨_,hs⟩
    exact H.pass _ U spot
  refine ⟨⟨form.smooth,form.origin,form.identity_null,form.projects,guard,form.carried,
    form.invariant,form.supported,form.borel⟩,pay.2.1,rfl,rfl,?_⟩
  intro U
  change y.density o S P U=_
  have change_rep:y.density o S P U=y.density o S (plate P) U:=by unfold Coefficient.density; congr 2
  exact change_rep.trans (pay.2.2 U)

end YM.Integration.WilsonReportingGuardedSource
