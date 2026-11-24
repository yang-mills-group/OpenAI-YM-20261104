import YM.Integration.WilsonPhysicalAbsoluteVaneMatrix

/-! Recover every target in the complete original physical quotient using the
already enrolled signed weak sources, with a single finite-regulator charge. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalAbsoluteVaneRecovery
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

open WilsonPhysicalAbsoluteVaneMatrix (cuts filed)
variable {I:Type}[Fintype I][DecidableEq I](d:Fin (D+1))(basis:Module.Basis I ℂ ((Bel R.family.book).Field d))

def coefficients {r:ℝ}(B:Book F (l:=l) H arch D T r)(N p:ℕ)(x:(Bel R.family.book).Field d):I→ℂ:=
  ((filed F J Z d basis B N p)⁻¹).mulVec (basis.repr x)

theorem recovered {r:ℝ}(B:Book F (l:=l) H arch D T r){N p:ℕ}
    (unit:IsUnit (filed F J Z d basis B N p).det)(x:(Bel R.family.book).Field d):
    ((Cells.standard R.family).project d) (∑j,coefficients F J Z d basis B N p x j •
      WilsonPhysicalAbsoluteVaneHome.read F J Z B d N p (basis j))=x:=by
  let M:=filed F J Z d basis B N p
  let L:=((Cells.standard R.family).project d).comp (WilsonPhysicalAbsoluteVaneHome.read F J Z B d N p)
  have idn:L.comp (Matrix.toLin basis basis M⁻¹)=LinearMap.id:=by
    apply (LinearMap.toMatrix basis basis).injective
    rw [LinearMap.toMatrix_comp basis basis basis,LinearMap.toMatrix_toLin,LinearMap.toMatrix_id]
    exact Matrix.mul_nonsing_inv M unit
  have applied:=congrArg (fun z:(Bel R.family.book).Field d→ₗ[ℂ](Bel R.family.book).Field d=>z x) idn
  rw [LinearMap.comp_apply,LinearMap.id_apply,Matrix.toLin_apply,map_sum] at applied
  calc
    _ = ∑j,coefficients F J Z d basis B N p x j • ((Cells.standard R.family).project d)
        (WilsonPhysicalAbsoluteVaneHome.read F J Z B d N p (basis j)):=by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact ((Cells.standard R.family).project d).map_smul _ _
    _ = x:=by
      simp only [map_smul,LinearMap.comp_apply,L,coefficients,M] at applied ⊢
      exact applied

omit [DecidableEq I] in
private theorem salary (A:Matrix I I ℂ)(bounded:∀i j,‖A i j‖≤2)(x:I→ℂ):
    ∑i,‖A.mulVec x i‖≤(Fintype.card I:ℝ)*2*∑j,‖x j‖:=by
  have point (i:I):‖A.mulVec x i‖≤2*∑j,‖x j‖:=by
    rw [Finset.mul_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _=>by
      rw [norm_mul];exact mul_le_mul_of_nonneg_right (bounded i j) (norm_nonneg _))
  calc
    _≤∑_i:I,2*∑j,‖x j‖:=Finset.sum_le_sum fun i _=>point i
    _=_:=by simp [mul_assoc]

include shared near lead obeys in
theorem original:
    ∀ᶠz:ι×ℕ×ℕ in cuts F books u age,∀x:(Bel R.family.book).Field d,
      ((Cells.standard R.family).project d) (∑j,coefficients F J Z d basis (books (age z.1)) z.2.1 z.2.2 x j •
          WilsonPhysicalAbsoluteVaneHome.read F J Z (books (age z.1)) d z.2.1 z.2.2 (basis j))=x ∧
      (∑j,‖coefficients F J Z d basis (books (age z.1)) z.2.1 z.2.2 x j‖)≤
        (Fintype.card I:ℝ)*2*∑j,‖(basis.repr x) j‖:=by
  let M:=fun z:ι×ℕ×ℕ=>filed F J Z d basis (books (age z.1)) z.2.1 z.2.2
  obtain ⟨rank,inverse⟩:=WilsonPhysicalAbsoluteVaneMatrix.reversible F J simple a books shared Z lead obeys u age near d basis
  have entries:∀ᶠz in cuts F books u age,∀i j:I,‖(M z)⁻¹ i j‖≤2:=by
    refine Filter.eventually_all.mpr (fun i=>Filter.eventually_all.mpr (fun j=>?_))
    have cv:=tendsto_pi_nhds.mp (tendsto_pi_nhds.mp inverse i) j
    have lim:‖(1:Matrix I I ℂ) i j‖<(2:ℝ):=by
      by_cases eq:i=j <;> simp [Matrix.one_apply,eq]
    exact (cv.norm.eventually (eventually_lt_nhds lim)).mono (fun z g=>g.le)
  filter_upwards [rank,entries] with z regular prices
  intro x
  exact ⟨recovered F J Z d basis (books (age z.1)) regular.2 x,
    salary (M z)⁻¹ prices (basis.repr x)⟩

end YM.Integration.WilsonPhysicalAbsoluteVaneRecovery
