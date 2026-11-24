import YM.Integration.WilsonOriginalPublicTrialPhaseMotion
import YM.Integration.WilsonMeasuredPublicEntrancePhysicalPair

/-! Literal reflection of the submitted pair after each arm used its
own cutoff dose and the chosen funded field inverse. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhasePair
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Cells Extra.Histories
open PhysicalNext.Repeat.Legato PertExtension PertExtension.LatticePT
open WilsonPositionProgramBlockedTrialAddBack WilsonMovingForkMixedSeed WilsonMeasuredPublicEntranceCellWords
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntrancePhysicalPair (reflected)
open WilsonOriginalPublicTrialPhaseMotion
open OPE.Therm WilsonOriginalPublicReflectedGrid
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){K j N per:ℕ}
local notation "C" => R.family
local notation "X" i:max => Config G ((C).side i per)
def arm (h:ℕ)(w:(C).label h)(x:Site ((C).side K per)):X K→ℂ:=
  uncut R h N per K x (((((C).S.a K:ℂ)^h)⁻¹) • w)

theorem field (d:Fin 2→ℕ)(file:Filed R d K)(up:j≤K)(Y:∀i,(C).label (d i))(ax:Axis)
    (seam x:Site ((C).side K per))(c:Fin 2→Site ((C).side j per))
    (left:((C).S.toDepth up per).embed (c 0)=affine (Signed.mirror ax) seam x)
    (s:(Stock.census (Fin 2)).Mode)(all:s.val=univ):
    let w:=doses R d file.station (N:=N) (per:=per) (file.A N per) Y
    submitted R d (N:=N) file up Y (reflected ax) c s =
      fun U=>arm R (N:=N) (d 1) (w 1) (((C).S.toDepth up per).embed (c 1)) U *
        star (arm R (N:=N) (d 0) (w 0) x (pull (Signed.mirror ax) seam U)):=by
  intro w;funext U
  unfold submitted
  rw [all,Fin.prod_univ_two]
  change uncut R (d 0) N per K (((C).S.toDepth up per).embed (c 0))
    (((((C).S.a K:ℂ)^(d 0))⁻¹) • Motion.patch _ (Signed.mirror ax,true) (w 0)) U*
    uncut R (d 1) N per K _ (((((C).S.a K:ℂ)^(d 1))⁻¹) • Motion.patch _ (1,false) (w 1)) U=_
  rw [left,WilsonOriginalPublicTrialPhaseMotion.square,plain]
  exact mul_comm _ _

theorem original (d:Fin 2→ℕ)(file:Filed R d K)(up:j≤K)(Y:∀i,(C).label (d i))(ax:Axis)
    (seam x:Site ((C).side K per))(c:Fin 2→Site ((C).side j per))
    (left:((C).S.toDepth up per).embed (c 0)=affine (Signed.mirror ax) seam x)
    (s:(Stock.census (Fin 2)).Mode)(all:s.val=univ):
    let w:=doses R d file.station (N:=N) (per:=per) (file.A N per) Y
    (∫U,submitted R d (N:=N) file up Y (reflected ax) c s U ∂scene (C).path N per K)=
      pairing R K N per (Signed.mirror ax) seam
        (arm R (N:=N) (d 1) (w 1) (((C).S.toDepth up per).embed (c 1)))
        (arm R (N:=N) (d 0) (w 0) x):=by
  rw [field R d file up Y ax seam x c left s all]
  rfl
end YM.Integration.WilsonOriginalPublicTrialPhasePair
