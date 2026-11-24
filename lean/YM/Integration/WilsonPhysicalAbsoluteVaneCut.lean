import YM.Integration.WilsonPhysicalAbsoluteVaneHome
import YM.Integration.WilsonPhysicalOrientedStencilPin
import YM.Integration.WilsonReflectedMixedMasterSchool

/-! The actual rested canonical inverse used by the public source, on the enrolled
weak inputs. The deposited turn is undone on its own tensor before applying the named inverse. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalAbsoluteVaneCut
open Function Filter Spec Table Climb PhysMS PhysMS.Frame Trace.Pilot Trace.Target
open PhysicalNext.Repeat.Legato Next.Rank Next.Rank.East Further.CorrectedLift
open OPE Next.Extract RG.Supply MS MS.Land FVA2 FVA2.Register
open Extra.Histories
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonPhysicalAllGradeWeakElection WilsonPhysicalWeakWallStaff WilsonPhysicalWeakSameStation WilsonPhysicalWeakWallBooks
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonPhysicalElectedVaneHead (recorded)
open WilsonPhysicalAbsoluteVaneDirections (column)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
variable (F:Final R.family f S){H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}
  {D T K n:ℕ}(d:Fin n→Fin (D+1)){ρ:Fin n→ℝ}
  (B:(i:Fin n)→Book F (l:=l) H arch D T (ρ i))
  (glyph:(i:Fin n)→(R.family.labels.level (d i)).Index)
  (file:Filed R (fun i=>(d i).val) K)(turn:Fin n→Motion)

def names (N p:ℕ)(i:Fin n):R.family.label (d i):=
  (((B i).rows (d i)).arm true ((B i).V (d i) (WilsonPhysicalVaneBasis.field R.family (d i) (glyph i)))).source (N,p)

def debit (N p:ℕ)(i:Fin n):R.family.label (d i):=
  let F':=R.family.labels.level (d i)
  let k:=(B i).W.k
  let g:=F'.grades (glyph i)
  let filed:=WilsonPhysicalOrientedStencilPin.dosesAt R (fun i=>(d i).val) (N:=N) (per:=p) file (names F d B glyph N p) turn i
  (WilsonPhysicalStationSignedBlock.scale R (B i).W N p g.1 g.2)⁻¹ •
    (((R.family.S.a k:ℂ)^(d i).val)⁻¹ • (((R.family.S.a K:ℂ)^(d i).val) •
      (file.A N p i) (Motion.patch F' (Motion.backward (turn i)) filed)))

private theorem undo {d':ℕ}(q:Labels.Frame G d')(τ:Motion)(x:q.Coeff):
    Motion.patch q (Motion.backward τ) (Motion.patch q τ x)=x:=by
  have twice:Motion.backward (Motion.backward τ)=τ:=by cases τ;simp [Motion.backward]
  simpa only [twice] using Motion.round q (Motion.backward τ) x

theorem posted (N p:ℕ)(i:Fin n)(same:file.station i=(B i).W.k):
    debit F d B glyph file turn N p i=column F (B i) (d i) N p (glyph i):=by
  let k:=(B i).W.k
  let s:=(R.family.S.a K:ℂ)^(d i).val
  have nz:s≠0:=pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos K).ne')
  have angle:Motion.scalar (Motion.backward (turn i)) s⁻¹=s⁻¹:=by
    have real:s⁻¹=Complex.ofReal (((R.family.S.a K)^(d i).val)⁻¹):=by simp [s]
    rw [real,Motion.scalar_real]
  unfold debit WilsonPhysicalAbsoluteVaneDirections.column recorded WilsonPhysicalOrientedStencilPin.dosesAt WilsonMovingForkMixedSeed.units WilsonMovingForkMixedSeed.doses
  dsimp only
  rw [Motion.patch_smul,angle,undo,map_smul,LinearEquiv.apply_symm_apply,smul_smul s s⁻¹,mul_inv_cancel₀ nz,one_smul,same]
  rfl

theorem selected {I:Type}[Fintype I][DecidableEq I][Nonempty I](J:ℝ→tower S)(Z:WilsonPrescription G)
    (h:I→Fin (D+1))(loc:(i:I)→(R.family.labels.level (h i)).Index)(x:∀i,RG17.Free R.family (h i).val)
    {δ:ℝ}(books:(r:{r:ℝ//0<r ∧ r<δ})→Book F (l:=l) H arch D T r.val)(i:I)(r:{r:ℝ//0<r ∧ r<δ}):
    WilsonReflectedMixedMasterSchool.field F J Z D T h (fun t=>WilsonPhysicalVaneBasis.field R.family (h t) (loc t)) x books i r false true=
      (books r).V (h i) (WilsonPhysicalVaneBasis.field R.family (h i) (loc i)):=rfl

end YM.Integration.WilsonPhysicalAbsoluteVaneCut
