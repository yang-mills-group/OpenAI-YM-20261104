import YM.Integration.WilsonMaxwellThermometerPublicCollege
/-! Complete finite graded receiver on the actual moving station, with
the solved numerical columns still fixed on the whole joint cell test. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerSignedWallet
open Function Set Filter Finset Spec Extraction Table RG Lattice Labels Source OPE OPE.Orbits Climb
open Trace Trace.Pilot Next.UVStress Cells PhysicalNext.Repeat.Legato Next.Rank Next.Rank.Atlas
open Further.CorrectedLift PhysMS PhysMS.Frame Maxwell Maxwell.Free XSpace XSpace.Cirrus XSpace.Rose
open XSpace.Graph3 XSpace.Structure1 XSpace.Photo XSpace.Normalize
open WilsonPositionCapTransport WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonMaxwellThermometerPublicStation WilsonMaxwellThermometerChargedHeads WilsonMaxwellThermometerPublicEvenSlope
open WilsonMaxwellThermometerShiftedPanel WilsonMaxwellThermometerPublicGalop WilsonSeparatedOriginalThermometerDetectorMesh
open WilsonMaxwellThermometerPositionCurrency WilsonMaxwellThermometerVotedCurrency
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G)(W:Initialize G){V:Normalize.Store G}(K:Rose.Pick V)

abbrev Axes (i:Fin 3):= (R.family.labels.level (grade i)).Coeff
def store (v:∀i,Axes R i):Tags G 6 3:=fun i=>
  up (Nat.le_of_lt_succ (grade i).isLt) (sector (R.family.labels.level (grade i)) (v i))
def maxpart (v:∀i,Axes R i):∀i,Axes R i:=fun i=>head (R.family.labels.level (grade i)) (v i)
def target:∀i,Axes R i:=fun i=>ladder R.family (grade i) (source R.family univ i)
def board (k:ℕ)(r:ℝ)(p:ℕ):Mesh:=
  chart R k p (aperture R (fun _=>k) r) (granted R (fun _=>k) r)
def deposited (k:ℕ)(r:ℝ)(p:ℕ)(v:∀i,Axes R i):Tags G 6 3:=
  let x:=translated (board R k r p) (fun _ : Fin 3=>0)
  fun i=>up (Nat.le_of_lt_succ (grade i).isLt)
    (received x (R.family.S.a k) (sector (R.family.labels.level (grade i)) (v i)))
def maximalPaid (r:ℝ)(v:∀i,Axes R i):∀i,Axes R i:=maxpart R fun i=>((r:ℂ)^(grade i).val)⁻¹ • v i

theorem oriented:store R (target R)=Rose.tag G:=by
  have read (j:ℕ)(w:(Bel R.family.book).Field j):sector (R.family.labels.level j)
      (ladder R.family j w)=Maxwell.Free.fields R.family.labels j w:=by
    change Maxwell.Free.fields R.family.labels j ((Cells.standard R.family).project j (ladder R.family j w))=_
    rw [ladder_reads]
  funext i
  simp only [store,target,read,WilsonPositionThermometerGradedSource.source,Finset.mem_univ,if_true,LinearEquiv.apply_symm_apply]
  fin_cases i <;> rfl

theorem trim (x:Sample 3)(simple:G.Simple)(stage:V.Meets W x.F 6)(v:∀i,Axes R i):
    node W (V:=V) x (store R v)=node W (V:=V) x (store R (maxpart R v)):=by
  have eq (w:∀i,Axes R i):store R w=entered (sector _ (w 0)) (sector _ (w 1)) (sector _ (w 2)):=by
    funext i;fin_cases i <;>rfl
  rw [eq,eq]
  exact WilsonMaxwellThermometerPublicHeads.original W x simple stage _ _ _ _ _ 

theorem changed (k:ℕ)(r:ℝ)(p:ℕ)(hr:0<r)(simple:G.Simple)
    (stage:V.Meets W (board R k r p) 6)(q:Fin 3→Lattice.Cover)(v:∀i,Axes R i):
    let x:=translated (board R k r p) q
    node W (V:=V) x (deposited R k r p v)=node W (V:=V) x (store R (maximalPaid R r v)):=by
  let x:=translated (board R k r p) q
  have same (i:Fin 3):(x.F.spacing:ℂ)^(grade i).val/(R.family.S.a k:ℂ)^(grade i).val=
      ((r:ℂ)^(grade i).val)⁻¹:=by
    simpa [x,translated,board,aperture,hr] using WilsonMaxwellThermometerPositionCurrency.top R (grade i).val k p r hr
  have income:deposited R k r p v=entered
      (received x (R.family.S.a k) (sector _ (v 0)))
      (received x (R.family.S.a k) (sector _ (v 1)))
      (received x (R.family.S.a k) (sector _ (v 2))):=by
    funext i;fin_cases i <;>rfl
  have output:store R (maximalPaid R r v)=entered
      (sector _ (head _ (((x.F.spacing:ℂ)^6/(R.family.S.a k:ℂ)^6) • v 0)))
      (sector _ (head _ (((x.F.spacing:ℂ)^4/(R.family.S.a k:ℂ)^4) • v 1)))
      (sector _ (head _ (((x.F.spacing:ℂ)^4/(R.family.S.a k:ℂ)^4) • v 2))):=by
    have s0:=same 0
    have s1:=same 1
    change (x.F.spacing:ℂ)^6/(R.family.S.a k:ℂ)^6=((r:ℂ)^6)⁻¹ at s0
    change (x.F.spacing:ℂ)^4/(R.family.S.a k:ℂ)^4=((r:ℂ)^4)⁻¹ at s1
    rw [s0,s1]
    funext i;fin_cases i <;>rfl
  rw [income,output]
  exact WilsonMaxwellThermometerVotedCurrency.original W x _ simple stage _ _ _ _ _

end YM.Integration.WilsonMaxwellThermometerSignedWallet
end
