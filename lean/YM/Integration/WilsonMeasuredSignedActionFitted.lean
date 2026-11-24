import YM.Integration.WilsonMeasuredSignedActionCourse
import YM.Integration.WilsonOriginalMicroscopicGuardedReporters

/-! The actual K-born group word, its push on the inherited Wilson vacuum, and
the signed finite-torus measured page registered by the addressed inverse. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionFitted
open Function Filter Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato MergeProof Campaign
open WilsonOriginalNullPlacedGermMap WilsonOriginalMicroscopicGuardedReporters
open WilsonMeasuredSignedActionCourse WilsonPositionProgramBlockedTrialVoice
open scoped Classical Topology
variable {G:Gauge}(R:Run G){T:Campaign R}(L:Pillars R T)
local notation "F₀" => R.family.labels.level 4
local notation "C₀" => R.family
local notation "B₀" => R.family.localSection 4
local notation "H₀" => R.family.path
local notation "P₀" => R.family.params

include L in
theorem original (simple:G.Simple):∀ᶠ j:ℕ in atTop,∀{N per n:ℕ}(live:j+n≤N),
    let I:=denomination F₀ H₀ N (j+n)
    ∃Z:Voice F₀ H₀ per j,Heard B₀ H₀ N per P₀ j Z ∧ Chorus H₀ N per j Z ∧
    (∀ w,(Z.plays (I.symm w)).density 0 B₀ ((H₀).rep N per j)=
      WilsonPositionProgramOriginalBlockedTrial.carried R 4 live 0 w) ∧
    (∀ y w,Motion.patch F₀ y (Z.index (I.symm w))=Z.index (I.symm (Motion.patch F₀ y w))) ∧
    ∀ w,fixed F₀ w→positive F₀ w→positive F₀ (Z.index (I.symm w)):=by
  filter_upwards [WilsonMeasuredSignedActionCourse.original R L simple] with j issued
  intro N per n live I
  let V:=trial F₀ H₀ N per (j+n)
  have hv:Heard B₀ H₀ N per P₀ (j+n) V:=enrolled R.makes.wilson (R.makes.sections 4) live
  have quiet:Chorus H₀ N per (j+n) V:=by
    constructor;intro x s;funext X U
    simp [V,trial,primary,floatUp,stepUp,profile,cram,Motion.scalar]
  obtain ⟨Z,hz,cz,fields,sign⟩:=issued live V hv quiet
  have initial (w):V.index (I.symm w)=w:=I.apply_symm_apply w
  have motion (s w):Motion.patch F₀ s (I.symm w)=I.symm (Motion.patch F₀ s w):=by
    apply V.index.injective
    rw [initial,←hv.moves,initial]
  refine ⟨Z,hz,cz,?_,?_,?_⟩
  · intro w
    have h:=fields (I.symm w)
    have exactBorn:V.plays (I.symm w)=primary 0 w:=submitted N per (j+n) w
    rw [exactBorn] at h
    exact h.symm
  · intro y w
    rw [hz.moves,motion]
  · intro w hw pos
    exact sign _ (fun y=>by rw [motion,hw y]) (by rw [initial];exact pos)

theorem measured {j K N per target:ℕ}(before:j≤K)(live:K≤N){η:ℝ}
    {A:(C₀).label 4 ≃ₗ[ℂ] (C₀).label 4}{e:(C₀).label 4}
    (incoming:Arrived R 4 j K N per target before live η A e)
    (home:Opened C₀ 4 j per){Z:Voice F₀ H₀ per j}
    (heard:Heard B₀ H₀ N per P₀ j Z)(v:(C₀).label 4)
    (same:(Z.plays v).density 0 B₀ ((H₀).rep N per j)=
      WilsonPositionProgramOriginalBlockedTrial.carried R 4 (N:=N) (b:=j) (n:=K-j) (p:=per)
        (by omega) 0 (A.symm e)):
    (F₀).coeffSize (e-Z.index v) ≤ invoice (C:=C₀) 4 j per*Z.charge v:=by
  obtain ⟨_,q,form,paid,fields,actual,_⟩:=incoming
  have law:((H₀).rep N per j).p=plank C₀ j:=(R.makes.wilson.represents N per j (before.trans live)).vac
  have measured:=intrinsic C₀ 4 N per j 0 R.makes home (before.trans live)
    (show Printed C₀ 4 N per j 0 (Z.plays v) _ from ⟨(heard.earns v).1,⟨_,(heard.earns v).2⟩,same⟩)
    (show Printed C₀ 4 N per j 0 q _ from ⟨form,⟨_,paid⟩,fields⟩)
  have eqPage:page (C:=C₀) 4 per j (Z.plays v)=e:=by
    change projection F₀ P₀ (plank C₀ j).threshold 0 (Z.plays v)=e
    rw [←law];exact measured.trans actual
  have bound:=measured_diff (C:=C₀) 4 N per j R.makes home.post (before.trans live) (heard.earns v)
  rwa [eqPage,heard.currents] at bound

end YM.Integration.WilsonMeasuredSignedActionFitted
end
