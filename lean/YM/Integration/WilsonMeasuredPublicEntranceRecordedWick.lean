import YM.FVAAlt2.Home.Gram
import YM.Integration.WilsonMeasuredPublicEntranceRecordedQuotient

/-! Recover the coordinates of an original physical field from its signed two-point readings
against reflected physical fields of the same Wick rank. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceRecordedWick
open Function Extra.FD Maxwell Maxwell.Wick Labels MvPolynomial
open scoped Classical BigOperators ComplexOrder Matrix
variable {G:Gauge}{F:Frames G}{d q:ℕ}

theorem turned (s:Ortho) (P:WickPol G) (h:Length P q):Length (pullSol s P) q:=by
  apply gradeMove letterCount letterCount (pullSol s) _ P q h
  intro i
  rw [pullSol,aeval_X,Maxwell.symbol]
  apply IsWeightedHomogeneous.sum
  intro a _
  exact (isWeightedHomogeneous_X ℂ letterCount _).C_mul _

theorem barred (P:WickPol G) (h:Length P q):Length (barPol P) q:=by
  intro m hm
  apply h
  intro z
  apply hm
  simp [barPol,coeff_map,z]

abbrev Keys (B:RStage F d)(q:ℕ):= {i:Fin (B.m+1) // (B.w i).2=q}

def read (x y:E4) (u:(freeTable F).Field d): (freeTable F).Field d→ₗ[ℂ]ℂ:=
  (readsTwo F d x y).flip (faceTest F d x y u)

theorem foreign (B:RStage F d)(x y:E4)(i j:Fin (B.m+1))(apart:(B.w j).2≠(B.w i).2):
    read x y (B.b i) (B.b j)=0:=by
  change readsTwo F d x y (B.b j) (faceTest F d x y (B.b i))=0
  rw [faceTest_eq,duplex,aligned_apply]
  exact FVAAlt2.Home.Report.stepNone _ _ _ (B.length j) (turned _ _ (barred _ (B.length i))) apart

def gram (B:RStage F d)(x y:E4)(q:ℕ):Matrix (Keys B q) (Keys B q) ℂ:=
  Matrix.of fun i j=>read x y (B.b i.val) (B.b j.val)

theorem positive (B:RStage F d)(x y:E4)(apart:x≠y)(q:ℕ):(gram B x y q).PosDef:=by
  let X (i:Keys B q):=writes F d (B.b i.val)
  have independent:LinearIndependent ℂ X:=
    (B.b.linearIndependent.comp (fun i:Keys B q=>i.val) Subtype.val_injective).map'
      (writes F d) (LinearMap.ker_eq_bot.mpr (writes_inj F d))
  have he:gram B x y q=Matrix.of (fun i j=>duplex x y (X j) (X i)):=by
    ext i j
    exact faceTest_eq F d x y _ _
  rw [he]
  exact reflected_pd apart X independent

theorem counted (B:RStage F d)(x y:E4)(q:ℕ)(v:(freeTable F).Field d):
    (gram B x y q) *ᵥ (fun i=>B.b.coord i.val v)=fun i=>read x y (B.b i.val) v:=by
  ext i
  let pay (j:Fin (B.m+1)):=B.b.coord j v * read x y (B.b i.val) (B.b j)
  have bad(j:Fin (B.m+1))(h:¬(B.w j).2=q):pay j=0:=by
    unfold pay
    rw [foreign B x y _ j (by simpa only [i.property] using h),mul_zero]
  have all:read x y (B.b i.val) v=∑j,pay j:=by
    conv_lhs=>rw [←B.b.sum_repr v]
    simp only [map_sum,map_smul,smul_eq_mul]
    rfl
  change (∑j:Keys B q,read x y (B.b i.val) (B.b j.val)*B.b.coord j.val v)=_
  rw [all,←Fintype.sum_subtype_add_sum_subtype (fun j=>(B.w j).2=q) pay]
  have zero:(∑j:{k:Fin (B.m+1)//¬(B.w k).2=q},pay j.val)=0:=
    Finset.sum_eq_zero (fun j _=>bad _ j.property)
  rw [zero,add_zero]
  exact Finset.sum_congr rfl fun j _=>mul_comm _ _

theorem coordinates (B:RStage F d)(x y:E4)(apart:x≠y)(q:ℕ)(v:(freeTable F).Field d)(i:Keys B q):
    B.b.coord i.val v=∑j:Keys B q,(gram B x y q)⁻¹ i j*read x y (B.b j.val) v:=by
  have unit:=isUnit_iff_ne_zero.mpr (positive B x y apart q).det_pos.ne'
  have he:=congr_arg (fun w=>(gram B x y q)⁻¹ *ᵥ w) (counted B x y q v)
  change _ *ᵥ (_ *ᵥ _) = _ at he
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ unit,Matrix.one_mulVec] at he
  exact congr_fun he i

theorem priced (B:RStage F d)(x y:E4)(apart:x≠y)(q:ℕ)(v:(freeTable F).Field d)
    (ε:ℝ)(he:∀j:Keys B q,‖read x y (B.b j.val) v‖≤ε)(i:Keys B q):
    ‖B.b.coord i.val v‖≤(∑j:Keys B q,‖(gram B x y q)⁻¹ i j‖)*ε:=by
  rw [coordinates B x y apart q v i,Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _=>?_))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (he j) (norm_nonneg _)
end YM.Integration.WilsonMeasuredPublicEntranceRecordedWick

