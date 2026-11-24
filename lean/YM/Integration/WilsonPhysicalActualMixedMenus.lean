import YM.Integration.WilsonPhysicalActualWeakCylinders

/-! Independent weak/pooled choices on the original N law. The enrolled pooled field
has one representative even when its production by the pool depends on the vector. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalActualMixedMenus
open Function Filter Finset MeasureTheory Lattice RG Wilson Extra.Histories
open Table Climb Spec PhysicalNext.Repeat.Legato Trace.Target Trace.Pilot
open OPE Next.Extract RG.Supply MS MS.Land FVA2 FVA2.Register
open WilsonReflectedPublicOrientedFaces (displayed)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonPhysicalActualWeakNames (coefficient seed)
open WilsonPhysicalActualWeakCylinders (product)
open scoped Classical BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
variable (F:Final R.family f S)(J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G)
  {H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}{D T:ℕ}
local notation "C" => R.family

abbrev Port (R:Run G)(d:ℕ)(weak:Bool):Type:=Fin (if weak then ((R.family.labels.level d).extra+1) else 1)

section Slot
variable (d:Fin (D+1)){r:ℝ}(B:Book F (l:=l) H arch D T r)(v:(Bel R.family.book).Field d)

def name (weak:Bool)(N p:ℕ):(C).label d:=
  ((B.rows d).arm weak (WilsonPositionHomogeneousFrame.homogeneous F J Z r d v)).source (N,p)

def weight:(weak:Bool)→Port R d weak→ℂ
  | false,_=>1
  | true,e=>coefficient F J Z d B v e

def source:(weak:Bool)→Port R d weak→ℕ→ℕ→(C).label d
  | false,_=>name F J Z d B v false
  | true,e=>seed F d B e

def fee (weak:Bool):ℝ:=if weak then ∑e,‖coefficient F J Z d B v e‖ else 1

theorem restored (weak:Bool): (∑e:Port R d weak,‖weight F J Z d B v weak e‖)=fee F J Z d B v weak:=by
  cases weak
  · simp [Port,fee,weight]
  · rfl

theorem cylinder (weak:Bool)(N p:ℕ)(turn:Motion)(site:Site ((C).side N p))(U:Config G ((C).side N p)):
    (C).O N p (displayed R d (name F J Z d B v weak N p) turn) site U=
      ∑e:Port R d weak,Motion.scalar turn (weight F J Z d B v weak e) *
        (C).O N p (displayed R d (source F J Z d B v weak e N p) turn) site U:=by
  cases weak
  · simp [Port,source,weight,Motion.scalar]
  · exact WilsonPhysicalActualWeakCylinders.cylinder F J Z B d v N p turn site U
end Slot

variable {I:Type}[Fintype I]{ρ:I→ℝ}(books:(i:I)→Book F (l:=l) H arch D T (ρ i))
  (d:I→Fin (D+1))(v:(i:I)→(Bel R.family.book).Field (d i))(weak:I→Bool)(turn:I→Motion)

abbrev Choices:=∀i:I,Port R (d i) (weak i)

def multiplier (e:Choices (R:=R) d weak):ℂ:=
  ∏i,Motion.scalar (turn i) (weight F J Z (d i) (books i) (v i) (weak i) (e i))

theorem group (N p:ℕ)(site:I→Site ((C).side N p))(U:Config G ((C).side N p)):
    product d turn N p site (fun i=>name F J Z (d i) (books i) (v i) (weak i) N p) U=
      ∑e:Choices (R:=R) d weak,multiplier F J Z books d v weak turn e *
        product d turn N p site (fun i=>source F J Z (d i) (books i) (v i) (weak i) (e i) N p) U:=by
  unfold product multiplier
  simp_rw [cylinder F J Z]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

theorem original (N p:ℕ)(site:I→Site ((C).side N p)):
    (C).omega N p (product d turn N p site (fun i=>name F J Z (d i) (books i) (v i) (weak i) N p))=
      ∑e:Choices (R:=R) d weak,multiplier F J Z books d v weak turn e *
        (C).omega N p (product d turn N p site (fun i=>source F J Z (d i) (books i) (v i) (weak i) (e i) N p)):=by
  let fields:=fun (e:Choices (R:=R) d weak)=>product d turn N p site (fun i=>source F J Z (d i) (books i) (v i) (weak i) (e i) N p)
  let a:=multiplier F J Z books d v weak turn
  have cont (e):Continuous (fields e):=continuous_finsetProd _ fun i _=>(C).continuousO _ _ _ _ _
  have ok (e):Integrable (fun U=>a e*fields e U) (law G _ ((C).beta N p)):=
    (continuous_const.mul (cont e)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [funext (group F J Z books d v weak turn N p site)]
  change (∫ U,∑e,a e*fields e U ∂law G _ ((C).beta N p))=_
  rw [integral_finsetSum _ (fun e _=>ok e)]
  exact Finset.sum_congr rfl fun _ _=>integral_const_mul _ _

theorem variation:
    (∑e:Choices (R:=R) d weak,‖multiplier F J Z books d v weak turn e‖)=
      ∏i,fee F J Z (d i) (books i) (v i) (weak i):=by
  simp only [←restored,multiplier,norm_prod,Motion.norm_scalar,Fintype.prod_sum]

theorem charged (N p:ℕ)(site:I→Site ((C).side N p))(forecast:Choices (R:=R) d weak→ℂ)
    (bill:Choices (R:=R) d weak→ℝ)
    (read:∀e:Choices (R:=R) d weak,‖(C).omega N p
        (product d turn N p site (fun i=>source F J Z (d i) (books i) (v i) (weak i) (e i) N p))-forecast e‖≤bill e):
    ‖(C).omega N p (product d turn N p site (fun i=>name F J Z (d i) (books i) (v i) (weak i) N p))-
      ∑e:Choices (R:=R) d weak,multiplier F J Z books d v weak turn e*forecast e‖≤
        ∑e:Choices (R:=R) d weak,‖multiplier F J Z books d v weak turn e‖*bill e:=by
  rw [original,←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro e _
  rw [←mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left (read e) (norm_nonneg _)

end YM.Integration.WilsonPhysicalActualMixedMenus
