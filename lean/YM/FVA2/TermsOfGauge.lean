import YM.FVA2.MeanPlane

/-!
# Actual rooted inverse, slice and precision obtained for `PhysicalSum`
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Inversion
open Function Set Finset Filter Lattice MS MS.Koszul MS.Swirl MS.Native MS.Orbit
open PertExtension PertExtension.Orb
open Matrix Ends ArrayMap Substitute Lag
open scoped Classical
variable {G:Gauge} {n:Side}
local notation "X"=> X_ G n
local notation "Y"=> Y_ G n
local notation "x_"=> Z G (OEdge n)
local notation "y_"=> Z G (Vert n)
local notation "M"=> fullM G n
local notation "r"=> reflectX G n
local notation "c"=> reflectY G n
local notation "C"=> MasterC G n
local notation "L"=> MasterL G n
local notation "L₀"=> periodicL G n
local notation "u"=> DM G n
local notation "p"=> (2:ℂ)⁻¹
local notation "vX"=> 1+ r
local notation "vY"=> 1+ c
local notation "m"=> HarmY (G:=G) (n:=n)
local notation "J"=> Jbar G n
local notation "D"=> Jpast G n
local notation "E"=> rootP G n
local notation "S"=> fullS G n

def baseProp (G:Gauge)(n:Side): Matrix (Z G (OEdge n)) (Z G (OEdge n)) ℂ:=
    (2:ℂ)⁻¹ • ((2:ℂ)⁻¹ • ((rootP G n)ᵀ * MasterC G n * rootP G n))

def baseFix (G:Gauge)(n:Side): Matrix (Z G (Vert n)) (Z G (OEdge n)) ℂ:=
    (2:ℂ)⁻¹ • (Jpast G n * MasterL G n * rootP G n)
local notation "W"=> baseProp G n
local notation "Z0" => baseFix G n
local notation "T"=> intoC (costMatrix (priorRoot G n))
lemma master_range : J*D*L=L:= by
    let V:=vY*(1-m); have he : L=V* L₀:= by unfold MasterL V; rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, P_range,sub_zero]
    rw [he,← Matrix.mul_assoc, show J*D*V=V from norm_even]
lemma Master_sym : Cᵀ=C:= by
    unfold MasterC; rw [transpose_mul,P_C,transpose_add,transpose_one,rsym,Matrix.mul_add,Matrix.add_mul, rC_sync,mul_one,one_mul]
lemma rMA : r*C=C:= by
    unfold MasterC; rw [← Matrix.mul_assoc, mul_add, mul_one,rX,add_comm r]
lemma rMA' : C*r=C:= by apply transpose_injective; rw [transpose_mul,Master_sym,rsym,rMA]
lemma rML : L*r=L:= by unfold MasterL; rw [Matrix.mul_assoc, ← cL_sync, ← Matrix.mul_assoc,Matrix.add_mul,one_mul, rY, ← add_comm c] -- inspect
lemma levelY : vY*J=(2:ℂ) • J:= by rw [Matrix.add_mul, even_J, Matrix.one_mul, two_smul]

variable (h:Even n.val)
include h
lemma cut_prop : E*W*Eᵀ=C := by
    have hu : ∀ (f:Matrix X X ℂ), r*f=f → vX*f=(2:ℂ) • f := fun f hf=> by rw [Matrix.add_mul, hf, two_smul, one_mul]
    have hv : C*vX=(2:ℂ) • C:=by rw [Matrix.mul_add,rMA', two_smul,mul_one]
    unfold baseProp; rw [Matrix.mul_smul, Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_mul]
    rw [← Matrix.mul_assoc E (Eᵀ*C),← Matrix.mul_assoc E Eᵀ,R_wide h, hu _ rMA,
      Matrix.mul_assoc _ E, R_wide h, Matrix.smul_mul,hv]; simp [smul_smul]
lemma cut_fix : J*Z0*Eᵀ=L:= by
    unfold baseFix; rw [ Matrix.mul_smul,Matrix.smul_mul,← Matrix.mul_assoc J (D*L),← Matrix.mul_assoc J D,master_range,Matrix.mul_assoc, R_wide h, Matrix.mul_add, rML, Matrix.mul_one, ← two_smul ℂ]; simp [smul_smul]

lemma gauge_left : Z0*u=1:= by
    unfold baseFix; rw [Matrix.smul_mul,Matrix.mul_assoc _ E, J_deriv h, MasterL,
      Matrix.mul_assoc D, Matrix.mul_assoc vY, ← Matrix.mul_assoc L₀ M, P_mom,
      Matrix.sub_mul,Matrix.one_mul,null_J,sub_zero,levelY, Matrix.mul_smul,AJ]; simp [smul_smul]
omit h in
lemma gauge_sym : Wᵀ=W := by unfold baseProp; rw [transpose_smul,transpose_smul,transpose_mul,transpose_mul,Master_sym,transpose_transpose,Matrix.mul_assoc Eᵀ C]
omit h in
lemma master_M : T = p • ( Eᵀ*S*E ):= by -- h unused
    rw [ hessian_ratio,cast_scal,into_mul,into_mul,into_transpose]; simp [rootP]
lemma master_hes : W*T=1-u*Z0 := by
    let A:=periodicC G n; let P:=fullS G n
    have hu : W*T=p • (p • (Eᵀ*(C*S)*E)):= by
       rw [master_M]; unfold baseProp; simp only [ Matrix.smul_mul, Matrix.mul_smul]
       rw [Matrix.mul_assoc (Eᵀ*C) E, ← Matrix.mul_assoc E _ E, ← Matrix.mul_assoc E Eᵀ S, R_wide h,
         Matrix.mul_assoc Eᵀ C, ← Matrix.mul_assoc C, ← Matrix.mul_assoc C, Matrix.mul_add, rMA',mul_one, ← two_smul ℂ, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,← Matrix.mul_assoc Eᵀ (C*S) E]; simp only [smul_smul]; norm_num
    have hv : C*S=vX*(1-HarmX-M*L₀) := by
       unfold MasterC; rw [Matrix.mul_assoc]; refine congr_arg (vX * ·) (eq_sub_of_add_eq P_green)
    have hw : vX*(HarmX (G:=G) (n:=n))=0 := by rw [Matrix.add_mul,E_Hx, one_mul,add_neg_cancel]
    have hM : vX*M=M*vY:= by rw [Matrix.add_mul,Matrix.mul_add,Matrix.one_mul,Matrix.mul_one,gd_inter]
    rw [hu,hv,Matrix.mul_sub,Matrix.mul_sub vX,hw,sub_zero,mul_one,
      ← Matrix.mul_assoc vX,hM,Matrix.mul_assoc M,show (vY)*L₀=L from rfl]
    rw [Matrix.mul_assoc, Matrix.sub_mul,Matrix.add_mul,E_r h,
        Matrix.one_mul, ← two_smul ℂ, Matrix.mul_sub,Matrix.mul_smul,E_wide h]
    rw [← cut_fix h, Matrix.mul_assoc M _ E, Matrix.mul_assoc (J*Z0), E_wide h, Matrix.mul_smul,Matrix.mul_one,Matrix.mul_smul M,Matrix.mul_smul,← Matrix.mul_assoc M,← J_deriv h, ← Matrix.mul_assoc Eᵀ, ← Matrix.mul_assoc Eᵀ E, E_wide h]
    simp [Matrix.smul_mul,smul_sub,smul_smul]

lemma landed : ∃ V:Matrix y_ y_ ℂ, Z0ᵀ=u*V := by
    -- L'* Y in longitudinal columns since reflection. Eᵀ comm sizes
    obtain ⟨Q,hQ⟩:= P_long (G:=G) (n:=n)
    have hf : Lᵀ=M*(vY*Q):= by
       unfold MasterL; rw [Matrix.add_mul,Matrix.one_mul,cL_sync,transpose_add,transpose_mul L₀,rsym,hQ,
        ← Matrix.mul_assoc r M, gd_inter, Matrix.mul_assoc M, Matrix.add_mul, one_mul, Matrix.mul_add]
    have hg : M*(vY*Q)=M*(J*(D*(vY*(1-m)*Q))) := by
       rw [← Matrix.mul_assoc J D, ← Matrix.mul_assoc (J*D), show J*D*(vY*(1-m))=vY*(1-m) from norm_even]
       rw [ ← Matrix.mul_assoc M (vY*(1-m)), ← Matrix.mul_assoc M, ← Matrix.mul_assoc M, ← show vX*M=M*vY from ?_, Matrix.mul_assoc vX M (1-m), Matrix.mul_sub, Matrix.mul_one,no_const,sub_zero]
       rw [Matrix.mul_add,Matrix.add_mul _ _ M,Matrix.one_mul,Matrix.mul_one,gd_inter]
    refine ⟨(D*(vY*(1-m)*Q))*Dᵀ, ?_⟩
    rw [baseFix, transpose_smul,transpose_mul,transpose_mul,hf,hg, ← Matrix.mul_assoc M, ← J_deriv h]
    simp only [← Matrix.mul_assoc]; rw [E_wide h]; simp [smul_smul, Matrix.mul_assoc]

lemma transverseW : uᵀ*W=0 := by
    have he : Mᵀ*C=0:= by
      unfold MasterC; rw [Matrix.add_mul,rC_sync, Matrix.mul_add,one_mul,P_transverse, ← Matrix.mul_assoc Mᵀ,P_transverse]; simp
    have hu : uᵀ*Eᵀ = Jᵀ*Mᵀ := by rw [← transpose_mul,← transpose_mul,J_deriv h]
    unfold baseProp; rw [Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hu, Matrix.mul_assoc Jᵀ, he]; simp

end YM.FVA2.Inversion
