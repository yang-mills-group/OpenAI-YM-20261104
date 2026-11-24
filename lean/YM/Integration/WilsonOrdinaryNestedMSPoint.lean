import YM.Integration.WilsonMSDictionaryVector

/-! The independent MS prescription at a literal vertex position.  Its
coupling substitution and both filtered field maps are made before the
coefficient is evaluated and before any test is integrated. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOrdinaryNestedMSPoint
open Function Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale FVA2.O FVA2.O.Score FVA2.O.Project
open MS MS.Land MS.Fleet MS.Theater RG17
open WilsonMSDictionaryVector WilsonMSDictionaryFarRead
open scoped Classical BigOperators
variable {G:Gauge} (Z:WilsonPrescription G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    (ν:ℝ) {n:ℕ}

def converted (x:Points n) (u:Scan G n) : Bill G :=
  let T:=Measure.Z Z.scheme Z.criterion ν M
  refund (seats T) (seats (replay T)) (Measure.f Z.criterion ν M)
    (fun v=>Canon.FarCoefficients (Equator.wave ν M) v x) u

theorem matched {simple:G.Simple} {σ:Prescription (Press.portDeck G)} {dial:Bool}
    (ms:Main.Match Z simple M σ dial) (x:Points n) (u:Scan G n) :
    converted Z M ν x u = Canon.FarCoefficients (Measure.outlook Z.scheme Z.criterion) u x := by
  let c:=ms.details.toServed.toPosted.toQuoted.toContract
  have point:=(Canon.opeeq (u:=u) (ν:=ν) c 0) x
  have bank:=ms.separatedOPE ν
  have hM (v:Scan G n) : Canon.OPECoefficients (Equator.wave ν M) v 0 x =
      Canon.FarCoefficients (Equator.wave ν M) v x := congrFun (bank.continuum.start_u v) x
  have hW : Canon.OPECoefficients (Measure.outlook Z.scheme Z.criterion) u 0 x =
      Canon.FarCoefficients (Measure.outlook Z.scheme Z.criterion) u x := congrFun (bank.wilson.start_u u) x
  change credit (seats (Measure.Z Z.scheme Z.criterion ν M)) (Measure.f Z.criterion ν M)
    (fun v=>Canon.OPECoefficients (Equator.wave ν M) v 0 x) u =
      receipt (seats (Measure.Z Z.scheme Z.criterion ν M))
        (Canon.OPECoefficients (Measure.outlook Z.scheme Z.criterion) u 0 x) at point
  simp_rw [hM,hW] at point
  unfold converted refund
  dsimp only
  rw [point,timely,spin_v (Canon.office c),receipt_K]

def field (C:Family G) (d:Fin n→ℕ) (h:ℕ) (v:(i:Fin n)→Free C (d i)) (x:Points n) (q:ℕ) (t:ℝ) :=
  assemble C d h v (fun j b=>cutoff q t (converted Z M ν x (fun i=>Dframe.flash (j i)) (Dframe.flash b)))

theorem issued {simple:G.Simple} {σ:Prescription (Press.portDeck G)} {dial:Bool}
    (ms:Main.Match Z simple M σ dial) (C:Family G) (d:Fin n→ℕ) (h:ℕ)
    (v:(i:Fin n)→Free C (d i)) (x:Points n) (q:ℕ) (t:ℝ) :
    field Z M ν C d h v x q t = assemble C d h v (fun j b=>cutoff q t
      (Canon.FarCoefficients (Measure.outlook Z.scheme Z.criterion) (fun i=>Dframe.flash (j i)) x (Dframe.flash b))) := by
  simp only [field,matched Z M ν ms]

theorem multi (C:Family G) (d:Fin n→ℕ) (h:ℕ) (v:(i:Fin n)→Free C (d i))
    (z:Fin n→ℂ) (x:Points n) (q:ℕ) (t:ℝ) :
    field Z M ν C d h (fun i=>z i • v i) x q t =
      (∏i,z i) • field Z M ν C d h v x q t := by
  unfold field assemble
  simp only [map_smul,Finsupp.smul_apply,smul_eq_mul,Finset.prod_mul_distrib,mul_smul,Finset.smul_sum]

end YM.Integration.WilsonOrdinaryNestedMSPoint
