import YM.Integration.WilsonPhysicalNodalFigureTrials
import YM.Integration.WilsonReceivedCanonicalVersePosterior

/-! Test the authentic original uncut K density and the inversion figure
on a single finite set of canonical inputs, with the same signed doses. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalNodalPrimitiveEntrance
open Function Filter Finset Lattice Wilson RG Labels Source Pert.Asymptotics Laurent
open XSpace XSpace.Cirrus PhysicalNext.Repeat.Legato RegulatorIR.FVAAlt2
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMovingForkMixedSeed (doses units product)
open WilsonMovingForkSeededPoint (seats)
open WilsonOriginalPublicPivotReflected (board evaluated)
open WilsonOriginalPublicNodalSeed (vector signed)
open WilsonOriginalPublicNodalIndependent (forecast)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonReceivedCanonicalVersePosterior (word)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)(W:Initialize G){n N per K u f:ℕ}(d:Fin n→ℕ)
  (file:Filed R d K)(Y:∀a,R.family.label (d a))(kn:K≤N)(node:Sample n)
  {h:Fin n→ℕ}(κ:(a:Fin n)→Knob (h a))(pt:Fin n→Chamber)(S:Finset (Fin n))
local notation "w" => units R d K (doses R d file.station (N:=N) (per:=per) (file.A N per) Y)
local notation "g" => regulatorRun R.family N per K
local notation "seen" => actualTransport R.family (N:=N) (p:=per)
local notation "cash" S:max q:max c:max => forecast R d κ pt S node.layout node.F.p (W.tree node.F.p) q g c
local notation "figure" S:max q:max => evaluated q g (board R W d (vector R d (N:=N) (per:=per) file Y) node S)
variable (uk:u≤K)(o:Fin n→Site (R.family.side K per))
local notation "cut" S:max => (fun U=>∏a:S,WilsonPositionProgramBlockedTrialAddBack.uncut R (d a) N per K (o a) ((w) a) U)
local notation "row" o:max S:max c:max => word R d κ pt g o S c
local notation "α" S:max c:max => weight R d N per K (w) S c

include kn
theorem original (q:ℕ)(U:Config G (R.family.side u per)):
    seen (cut S) uk U-figure S q=
      ∑c:Selection R d S,α S c*(seen (row o S c) uk U-cash S q c):=by
  rw [WilsonReceivedCanonicalVersePosterior.original R d κ pt N per K kn (w) o S u uk U]
  exact WilsonPhysicalNodalFigureTrials.signed R W d file Y kn node κ pt S q
    (fun c=>seen (row o S c) uk U)

theorem enrolled (fk:f≤K)(site:Fin n → Cover)
    (placed:∀i,wrap (R.family.side K per) (node.layout i)=seats (R:=R) fk per site i)(q:ℕ):
    signed R W d (N:=N) (per:=per) file Y uk node q=
      ∑c:Selection R d univ,α univ c*(seen (row (seats (R:=R) fk per site) univ c) uk 1-cash univ q c):=by
  rw [←WilsonOriginalPublicNodalSeed.field R W d file Y fk kn uk site node placed q]
  have all:=original (per:=per) R W d file Y kn node κ pt univ uk (seats (R:=R) fk per site) q 1
  have regroup (U:Config G (R.family.side K per)):
      (∏a:(univ:Finset (Fin n)),WilsonPositionProgramBlockedTrialAddBack.uncut R (d a) N per K
        (seats (R:=R) fk per site a) ((w) a) U)=∏a:Fin n,WilsonPositionProgramBlockedTrialAddBack.uncut R
        (d a) N per K (seats (R:=R) fk per site a) ((w) a) U:=
    Finset.prod_coe_sort (univ:Finset (Fin n)) (fun a=>WilsonPositionProgramBlockedTrialAddBack.uncut R
      (d a) N per K (seats (R:=R) fk per site a) ((w) a) U)
  have sameWord:WilsonMovingForkMixedSeed.product R d (N:=N) (seats (R:=R) fk per site)
      (doses R d file.station (N:=N) (per:=per) (file.A N per) Y)=
        fun U=>∏a:(univ:Finset (Fin n)),WilsonPositionProgramBlockedTrialAddBack.uncut R (d a)
          N per K (seats (R:=R) fk per site a) ((w) a) U:=funext fun U=>(regroup U).symm
  rw [sameWord]
  exact all

end YM.Integration.WilsonPhysicalNodalPrimitiveEntrance
end
