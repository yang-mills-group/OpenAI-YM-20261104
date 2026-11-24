import YM.Integration.WilsonPhysicalActualWeakNames
import YM.Integration.WilsonMeasuredPublicEntranceCellWords

/-! The finite menu expands the original microscopic Wilson moment itself. The same
semi-linear physical turn acts on the coefficient and the original named cylinder. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalActualWeakCylinders
open Function Filter Finset MeasureTheory Lattice RG Wilson Extra.Histories
open Table Climb Spec PhysicalNext.Repeat.Legato Trace.Target Trace.Pilot
open OPE Next.Extract RG.Supply MS MS.Land FVA2 FVA2.Register
open WilsonReflectedPublicOrientedFaces (displayed)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonPhysicalActualWeakNames (name coefficient seed)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
variable (F:Final R.family f S)(J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G)
  {H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}{D T:ℕ}
local notation "C" => R.family

private theorem moved (d:ℕ)(x:(C).label d)(t:Motion):
    displayed R d x t=Motion.patch ((C).labels.level d) t x:=by
  unfold displayed Motion.patch
  split
  · exact Motion.act_conj _ _ _
  · rfl

theorem cylinder {r:ℝ}(B:Book F (l:=l) H arch D T r)(d:Fin (D+1))(v:(Bel R.family.book).Field d)
    (N p:ℕ)(turn:Motion)(site:Site ((C).side N p))(U:Config G ((C).side N p)):
    (C).O N p (displayed R d (name F J Z d B v N p) turn) site U =
    ∑e,Motion.scalar turn (coefficient F J Z d B v e) *
      (C).O N p (displayed R d (seed F d B e N p) turn) site U:=by
  let L:=((C).linearO N p d site).mk' (fun x=>(C).O N p x site)
  have rotated:displayed R d (name F J Z d B v N p) turn=
      ∑e,Motion.scalar turn (coefficient F J Z d B v e) • displayed R d (seed F d B e N p) turn:=by
    rw [←WilsonPhysicalActualWeakNames.entered F J Z d B v N p,moved,Motion.patch_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [Motion.patch_smul,moved]
  rw [rotated]
  change L _ U=_
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rfl

variable {I:Type}[Fintype I]{ρ:I→ℝ}(books:(i:I)→Book F (l:=l) H arch D T (ρ i))
  (d:I→Fin (D+1))(v:(i:I)→(Bel R.family.book).Field (d i))(turn:I→Motion)

abbrev Choice:=∀i:I,((C).labels.level (d i)).Index

def amount (e:Choice (R:=R) d):ℂ:=∏i,Motion.scalar (turn i) (coefficient F J Z (d i) (books i) (v i) (e i))

def product (N p:ℕ)(site:I→Site ((C).side N p))(Y:(i:I)→(C).label (d i))(U:Config G ((C).side N p)):ℂ:=
  ∏i,(C).O N p (displayed R (d i) (Y i) (turn i)) (site i) U

theorem group (N p:ℕ)(site:I→Site ((C).side N p))(U:Config G ((C).side N p)):
    product d turn N p site (fun i=>name F J Z (d i) (books i) (v i) N p) U=
      ∑e:Choice (R:=R) d,amount F J Z books d v turn e *
        product d turn N p site (fun i=>seed F (d i) (books i) (e i) N p) U:=by
  unfold product amount
  simp_rw [cylinder F J Z,Fintype.prod_sum,Finset.prod_mul_distrib]

theorem original (N p:ℕ)(site:I→Site ((C).side N p)):
    (C).omega N p (product d turn N p site (fun i=>name F J Z (d i) (books i) (v i) N p))=
      ∑e:Choice (R:=R) d,amount F J Z books d v turn e *
        (C).omega N p (product d turn N p site (fun i=>seed F (d i) (books i) (e i) N p)):=by
  let funs:=fun (e:Choice (R:=R) d)=>product d turn N p site (fun i=>seed F (d i) (books i) (e i) N p)
  let a:=amount F J Z books d v turn
  have cont (e):Continuous (funs e):=continuous_finsetProd _ fun i _=>(C).continuousO _ _ _ _ _
  have ok (e):Integrable (fun U=>a e*funs e U) (law G _ ((C).beta N p)):=
    (continuous_const.mul (cont e)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have actual:=funext (group F J Z books d v turn N p site)
  rw [actual]
  change (∫ U,∑e,a e*funs e U ∂law G _ ((C).beta N p))=_
  rw [integral_finsetSum _ (fun e _=>ok e)]
  apply Finset.sum_congr rfl
  intro e _
  exact integral_const_mul _ _

theorem variation:(∑e:Choice (R:=R) d,‖amount F J Z books d v turn e‖)=
    ∏i,∑k,‖coefficient F J Z (d i) (books i) (v i) k‖:=by
  simp only [amount,norm_prod,Motion.norm_scalar,Fintype.prod_sum]

theorem charged (N p:ℕ)(site:I→Site ((C).side N p))(reading:Choice (R:=R) d→ℂ)(Δ:ℝ)
    (bills:∀e:Choice (R:=R) d,‖(C).omega N p (product d turn N p site (fun i=>seed F (d i) (books i) (e i) N p))-
        reading e‖≤Δ):
    ‖(C).omega N p (product d turn N p site (fun i=>name F J Z (d i) (books i) (v i) N p))-
       ∑e:Choice (R:=R) d,amount F J Z books d v turn e*reading e‖≤
      (∏i,∑k,‖coefficient F J Z (d i) (books i) (v i) k‖)*Δ:=by
  rw [original,←Finset.sum_sub_distrib,←variation F J Z books d v turn,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro e _
  rw [←mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left (bills e) (norm_nonneg _)

end YM.Integration.WilsonPhysicalActualWeakCylinders
