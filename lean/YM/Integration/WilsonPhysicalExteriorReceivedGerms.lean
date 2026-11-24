import YM.Integration.WilsonPhysicalExteriorPairedLimit
import YM.Integration.WilsonPhysicalExteriorRunningControl
import YM.Integration.MSMeasuredGermSeries

/-! The two measured nondegenerate matrices for the same registered
two-point experiment, with the genuine change of the Wilson bulk already
applied on the source side. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorReceivedGerms
open Filter Matrix MS MS.Land MS.Rake MS.Dial MS.Menus MS.Tide MS.Tone
open FVA2 FVAAlt2 Lobby Lattice PhysicalNext.Repeat.Legato
open Pert Pert.Position Pert.Scale Extra.FD OPE.Levy RG11.Fields
open WilsonPhysicalExteriorPairedLimit WilsonPhysicalExteriorRunningRows
open MSCutoffGerms MSMeasuredGermSeries
open scoped Classical Topology
variable {G:Gauge}{B:MS.Local.Physical.Deck G}{O:Booked B}
variable {R:Run G} {M:MS_Data G O} {Q:Prescription B}
variable {T:Trial ℕ (Fin 2)} {x:Fin 2→QP} (read:Read R M Q T x)
local notation "PS" => PowerSeries ℂ

def transported (R:Run G) (Q:Prescription B) (T:Trial ℕ (Fin 2)) (d h:ℕ) (μ ν:ℝ) (i:ℕ) :=
  (observed R Q T d h μ i).map (reprice Q.team (μ-T.profile.θ i) (ν-T.profile.θ i))

include read in
private theorem cash (d h:ℕ) (μ ν:ℝ) (a:Glyph B d) (b:Glyph B h) :
    WilsonPhysicalExteriorRunningControl.Admitted atTop T.profile.θ
        (fun i=>transported R Q T d h μ ν i a b) ∧
      ∀ i,PowerSeries.coeff 0 (transported R Q T d h μ ν i a b)=PowerSeries.coeff 0 (observed R Q T d h μ i a b) :=
  WilsonPhysicalExteriorRunningControl.measured read.1 Q.team μ ν _ (fun k=>convergent read.1 (read.2 μ d h k a b))

def receiver (d h:ℕ) (μ:ℝ) : Matrix (Glyph B d) (Glyph B h) (PowerSeries (MSCutoffGerms.ring read.1)) :=
  fun a b=>stored read.1 (fun i=>observed R Q T d h μ i a b) (fun k=>convergent read.1 (read.2 μ d h k a b))

def changed (d h:ℕ) (μ ν:ℝ) : Matrix (Glyph B d) (Glyph B h) (PowerSeries (MSCutoffGerms.ring read.1)) :=
  fun a b=>stored read.1 (fun i=>transported R Q T d h μ ν i a b) (cash read d h μ ν a b).1

theorem receiver_entry (d h:ℕ) (μ:ℝ) (a:Glyph B d) (b:Glyph B h) :
    PowerSeries.map (ring read.1).subtype (receiver read d h μ a b)=
      diagram atTop (fun i=>observed R Q T d h μ i a b) := exposed _ _ _

theorem changed_entry (d h:ℕ) (μ ν:ℝ) (a:Glyph B d) (b:Glyph B h) :
    PowerSeries.map (ring read.1).subtype (changed read d h μ ν a b)=
      diagram atTop (fun i=>transported R Q T d h μ ν i a b) := exposed _ _ _

variable {p q:E4} (table:Read R M Q T (Fountain.metric (couple p q)))
theorem physical (V:Warehouse G) (hp:p≠q) (d:ℕ) (μ:ℝ) :
    IsUnit (receiver table d d μ).det := by
  let Z:Matrix (Glyph B d) (Glyph B d) PS:=fun a b=>PowerSeries.mk (fun k=>
    limit M (Fountain.metric (couple p q)) d d μ k a b)
  have Hz:IsUnit ((PowerSeries.constantCoeff (R:=ℂ)).mapMatrix Z) := by
    exact head M V p q hp d μ
  apply MSMeasuredGermSeries.measured table.1 (observed R Q T d d μ) Z _ Hz
  intro a b k;simpa [Z] using table.2 μ d d k a b

theorem original (V:Warehouse G) (hp:p≠q) (d:ℕ) (μ ν:ℝ) :
    IsUnit (changed table d d μ ν).det := by
  let c:=PowerSeries.constantCoeff (R:=ring table.1)
  have heads:c.mapMatrix (changed table d d μ ν)=c.mapMatrix (receiver table d d μ) := by
    apply Matrix.ext;intro a b
    apply Subtype.ext
    exact congrArg (hom atTop) (funext (cash table d d μ ν a b).2)
  apply MSGradedReceiverRigidity.formal
  rw [heads,←c.map_det]
  exact (physical table V hp d μ).map c

end YM.Integration.WilsonPhysicalExteriorReceivedGerms
end
