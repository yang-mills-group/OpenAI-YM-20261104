import YM.Integration.WilsonPhysicalAbsoluteVaneRecovery
import YM.Integration.WilsonPhysicalStationMenuSalary

/-! The paid signed inverse acts on the real weak fields filed at their original station. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalSignedWeakSource
open Function Filter Spec Table Climb PhysMS PhysMS.Frame Trace.Pilot Trace.Target
open PhysicalNext.Repeat.Legato Further.CorrectedLift
open OPE Next.Extract RG.Supply MS MS.Land FVA2 FVA2.Register
open WilsonPhysicalAllGradeWeakElection WilsonPhysicalWeakWallStaff WilsonPhysicalWeakSameStation WilsonPhysicalWeakWallBooks
open WilsonPhysicalWeakWallBounded (cost)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonPhysicalAbsoluteVaneDirections (native variation)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
variable (F:Final R.family f S)(J:ℝ→tower S){H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}
  (simple:G.Simple)(a:Assignment F J H l simple){D T:ℕ}{δ:ℝ}
  (books:(r:{r:ℝ//0<r ∧ r<δ})→ Book F (l:=l) H arch D T r.val)
  (shared:∀r,∃cap:D≤(a.day r.val).1,Shared F (books r) (trim cap (a.day r.val).2))

variable (Z:WilsonPrescription G)(lead:PhysMS.Leading F J)(obeys:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)
variable {ι:Type*}(u:Filter ι)(age:ι→{r:ℝ//0<r ∧ r<δ})(near:Tendsto (fun i=>(age i).val) u trail)

open WilsonPhysicalAbsoluteVaneMatrix (cuts)
open WilsonPhysicalAbsoluteVaneRecovery (coefficients)
open WilsonPhysicalStationMenuSalary (weight height)
open WilsonPhysicalElectedVaneHead (recorded)
variable {I:Type}[Fintype I][DecidableEq I](d:Fin (D+1))(basis:Module.Basis I ℂ ((Bel R.family.book).Field d))

def input {r:ℝ}(B:Book F (l:=l) H arch D T r)(y:(Bel R.family.book).Field d):(Bel R.family.book).Field d:=
  (B.V d).symm (WilsonPositionHomogeneousFrame.homogeneous F J Z r d y)

def dose {r:ℝ}(B:Book F (l:=l) H arch D T r)(N p:ℕ)(x:(Bel R.family.book).Field d)
    (j:I)(e:(R.family.labels.level d).Index):ℂ:=
  coefficients F J Z d basis B N p x j * weight F B d (input F J Z d B (basis j)) N p e

theorem marked {r:ℝ}(B:Book F (l:=l) H arch D T r)(N p:ℕ)(x:(Bel R.family.book).Field d):
    (∑j,∑e,dose F J Z d basis B N p x j e •
      recorded F B d ((B.V d) (WilsonPhysicalVaneBasis.field R.family d e)) N p)=
    ∑j,coefficients F J Z d basis B N p x j • WilsonPhysicalAbsoluteVaneHome.read F J Z B d N p (basis j):=by
  apply Finset.sum_congr rfl
  intro j _
  change _=coefficients F J Z d basis B N p x j • ∑e,(ladder R.family d (input F J Z d B (basis j))) e •
    WilsonPhysicalAbsoluteVaneDirections.column F B d N p e
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [dose,weight,WilsonPhysicalAbsoluteVaneDirections.column,smul_smul]

include shared near lead obeys in
theorem original:
    ∃C:ℝ,0≤C ∧ ∀ᶠz:ι×ℕ×ℕ in cuts F books u age,∀x:(Bel R.family.book).Field d,
      let B:=books (age z.1)
      ((Cells.standard R.family).project d) (∑j,∑e,dose F J Z d basis B z.2.1 z.2.2 x j e •
        recorded F B d ((B.V d) (WilsonPhysicalVaneBasis.field R.family d e)) z.2.1 z.2.2)=x ∧
      (∑j,∑e,‖dose F J Z d basis B z.2.1 z.2.2 x j e‖)≤C*∑j,‖(basis.repr x) j‖:=by
  let V:=fun x:(Bel R.family.book).Field d=>(R.family.labels.level d).coeffSize (ladder R.family d x)
  have positive (x):0≤V x:=Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  have cv:Continuous V:=by
    change Continuous (fun x=>∑i,‖(ladder R.family d x) i‖)
    fun_prop
  let W:=∑j, (V (basis j)+1)
  have cap (j:I):V (basis j)+1≤W:=Finset.single_le_sum (f:=fun k=>V (basis k)+1)
    (fun k _=>by have:=positive (basis k);linarith) (Finset.mem_univ j)
  have Wp:0≤W:=Finset.sum_nonneg (fun j _=>by have:=positive (basis j);linarith)
  let T0:=(2:ℝ)^height (R:=R) d * W
  have tp:0≤T0:=mul_nonneg (by positivity) Wp
  refine ⟨(Fintype.card I:ℝ)*2*T0,by positivity,?_⟩
  have proj:Tendsto Prod.fst (cuts F books u age) u:=tendsto_comap.mono_left inf_le_left
  have live:∀ᶠz:ι×ℕ×ℕ in cuts F books u age,(books (age z.1)).W.k<z.2.1:=
    Filter.Eventually.filter_mono inf_le_right (by simp)
  have bounded:∀ᶠi in u,∀j:I,V (input F J Z d (books (age i)) (basis j))≤W:=by
    apply Filter.eventually_all.mpr
    intro j
    have h:=WilsonPhysicalWeakHomogeneousHome.direction F J simple a books shared Z lead obeys u age near d (basis j)
    have q:=cv.continuousAt.tendsto.comp h
    exact (q.eventually (eventually_lt_nhds (lt_add_one (V (basis j))))).mono fun _ w=>w.le.trans (cap j)
  filter_upwards [WilsonPhysicalAbsoluteVaneRecovery.original F J simple a books shared Z lead obeys u age near d basis,
    proj.eventually bounded,live] with z paid budget stamp
  intro x
  let B:=books (age z.1)
  change _=x ∧ _≤_
  constructor
  · exact (congrArg ((Cells.standard R.family).project d)
      (marked F J Z d basis B z.2.1 z.2.2 x)).trans (paid x).1
  · let cost:=coefficients F J Z d basis B z.2.1 z.2.2 x
    have each (j:I):∑e,‖dose F J Z d basis B z.2.1 z.2.2 x j e‖≤‖cost j‖*T0:=by
      simp only [dose,norm_mul,←Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (WilsonPhysicalStationMenuSalary.original F B stamp.le d _).trans
        (mul_le_mul_of_nonneg_left (budget j) (by positivity))
    calc
      _≤∑j,‖cost j‖*T0:=Finset.sum_le_sum fun j _=>each j
      _=(∑j,‖cost j‖)*T0:=by rw [Finset.sum_mul]
      _≤((Fintype.card I:ℝ)*2*∑j,‖(basis.repr x) j‖)*T0:=mul_le_mul_of_nonneg_right (paid x).2 tp
      _=_:=by ring

end YM.Integration.WilsonPhysicalSignedWeakSource
