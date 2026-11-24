import YM.Integration.WilsonOriginalPublicReflectedTrace
import YM.Integration.WilsonOriginalPublicReflectedSlide
import YM.Integration.WilsonRegisteredSealedRoot
import YM.Integration.WilsonMeasuredPublicEntranceLicensedNHead

/-! Center an actual trial planted at an interior date on the original history.
All copies contain the scalar selected by the fixed older Wilson field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseTrace
open Function Filter Set MeasureTheory Lattice RG Wilson Source Labels Cells Extra.Histories
open PhysicalNext.Repeat.Legato Push.GridApprox OPE.Strobe OPE.Therm
open OPE.Therm.ReplicaChessboard Next.Rank MergeProof Accent Work.G08 RG16 RG16.Literal Overlay
open WilsonPositionProgramBlockedTrialAddBack WilsonOriginalPublicReflectedTrace
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {K N p u : ℕ} {I : Type} [Fintype I]
local notation "C" => R.family
local notation "H" => (C).path
local notation "X" k:max => Config G ((C).side k p)

def word (d:I→ℕ) (z:I→Site ((C).side K p)) (v:∀i,(C).label (d i)) : X K → ℂ :=
  fun U => ∏ i, uncut R (d i) N p K (z i) (v i) U

theorem local_word (d:I→ℕ) (z:I→Site ((C).side K p)) (v:∀i,(C).label (d i))
    (o:Site ((C).side K p)) (r:ℕ)
    (fits:∀i,window (z i) (stencilRadius (C) (d i))⊆window o r) (a:ℂ) :
    Interior (window o r) (fun U=>word R (N:=N) d z v U-a) :=by
  have loc:Interior (window o r) (word R (N:=N) d z v):=by
    apply Interior.combines
    exact fun i _=>(local_trial R (N:=N) (d i) (v i) (z i)).enlarges (fits i)
  exact loc.plus (Interior.constant _ (-a))

theorem original (d:I→ℕ) (z:I→Site ((C).side K p)) (v:∀i,(C).label (d i))
    {station:ℕ}(jk:station≤K)(live:K≤N)(uk:u≤K)(r:ℕ)
    (fits:∀i,window (z i) (stencilRadius (C) (d i))⊆window 0 r)
    (space:room (H).levels station K r):
    let M:=word R (N:=N) d z v
    let a:=actualTransport (C) (N:=N) M uk 1
    let X₀:=fun U=>M U-a
    let T:=tilesAt (C).S p jk
    ‖(∫ U,M U ∂scene (H) N p K)-a‖≤
      ‖∫U,T.fullAt (fun _=>X₀) U ∂scene (H) N p K‖^((Fintype.card T.Cell:ℝ)⁻¹):=by
  intro M a X₀ T
  letI : IsProbabilityMeasure (scene (H) N p K) := probability R.makes.wilson live
  have loc:=local_word R (N:=N) d z v 0 r fits a
  let Y:=backTo (H) N p live X₀
  let S:=center (C).S p (jk.trans live) 0
  have top:Interior (S.chamber 0) Y:=by
    apply Interior.enlarges (backTo_local (H) N p jk live 0 r (F:=X₀) ?_)
      (room_fits p (H).levels r jk live space 0)
    rw [anchor,←Ratio.root_embed,map_zero];exact loc
  have buy:=S.planted (seamless R.makes N p) (fun _ : Fin 1=>0)
    (fun _ _ _=>Subsingleton.elim ..) (fun _=>Y) (fun _=>top)
  have lower:‖moment ((C).beta N p) Y‖≤S.rootTest ((C).beta N p) Y:=by
    simpa [Fin.prod_univ_succ] using! buy
  have eq:=WilsonOriginalPublicReflectedSlide.heard R live X₀ (cylinder_env loc)
  have pos:Interior (window 0 r) M:=by
    apply Interior.combines
    exact fun i _=>(local_trial R (N:=N) (d i) (v i) (z i)).enlarges (fits i)
  rw [←WilsonRegisteredSealedRoot.root R jk live r space X₀ loc] at lower
  rw [←eq] at lower
  rw [show (∫U,X₀ U ∂scene (H) N p K)=(∫U,M U ∂scene (H) N p K)-a from ?_] at lower
  · exact lower
  · rw [show X₀=(fun U=>M U-a) from rfl,integral_sub ((cylinder_env pos).integrableC _) (integrable_const a),integral_const]
    simp

end YM.Integration.WilsonOriginalPublicTrialPhaseTrace
