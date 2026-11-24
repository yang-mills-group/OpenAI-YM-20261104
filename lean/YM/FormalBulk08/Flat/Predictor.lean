import YM.FormalBulk08.Flat.Packed
import YM.Next.STATIONARY.Loops.HessianMatch

/-! Complete Markov square in absolute log coordinates. For value use
`Precision.K(pink(...))` at COARSE land in fine coupling (before reset).
No ext scalar budget/use of a continuum Gaussian has been inferred.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free Work.F08 Stationary Tree
open scoped Topology BigOperators Matrix
variable {G : Gauge} {P : Patch} {K : KernelChoices} {c f : Side} {S : StepData c f}
variable {t j : ℕ}

def rawMean (G : Gauge) (S : StepData c f) (F : Forest S.ratio) (W : Matrix (Body 1 f) (Body 1 c) ℝ) :=
    hang G S F*((butt G c f)ᵀ*patron G W)
lemma reproduced (c f : Side) :
    butt G c f*(butt G c f)ᵀ=1 ∧ brim G c f*(butt G c f)ᵀ=0 := by
  rw [helmet_brim,helmet_butt]
  let h x := show ((shardX (Lines G f 1) (Lines G c 0) ℝ)ᵀ*ᵥ x : Bodies G c f→ℝ)=Sum.elim x 0 from ?_
  · constructor <;> apply mat_confirm <;> intro v <;> rw [← Matrix.mulVec_mulVec, h]
    · rw [sliceX,Matrix.one_mulVec]; rfl
    rw [sliceY,Matrix.zero_mulVec]; rfl
  funext i; cases i <;> simp [Matrix.mulVec,Matrix.transpose_apply, shardX, dotProduct,Pi.single_apply,ite_mul]

lemma unstitch (G : Gauge) (F : Forest S.ratio) (W : Matrix (Body 1 f) (Body 1 c) ℝ) :
    let T:= rawMean G S F W
    (dropRoot G S F)ᵀ*T=patron G (extracted S F W) := by
  intro T
  let U:= (butt G c f)ᵀ*patron G W
  let I:= patron G (straighten S F W)
  have h := reproduced (G:=G) c f
  have he : butt G c f*U=patron G W ∧ brim G c f*U=0 := by unfold U; simp only [← Matrix.mul_assoc,h.1,h.2,Matrix.one_mul,Matrix.zero_mul,and_self]
  have hh : lead G S F * U=I := by
    unfold lead I
    rw [Matrix.sub_mul, Matrix.mul_assoc (patron G (trails S F)), he.1,Matrix.mul_assoc (patron G (apices S)), Matrix.add_mul,Matrix.mul_assoc (patron G (fixRoot S)), he.1, he.2, add_zero, ← patron_mul, ← patron_mul ,← patron_mul]
    apply mat_confirm; intro i; rw [Matrix.sub_mulVec]; funext ⟨x,s,k⟩
    rw [vac_only s]
    have h (w:Matrix (Body 0 f) (Body 1 c) ℝ) : (patron G w*ᵥ i) (x,vac,k) = (w*ᵥ atPaint i k) (x,vac) := congr_fun (paint_eats _ _ k) (x,vac)
    simp only [Pi.sub_apply,h, ← Matrix.mulVec_mulVec,peaks,trail_map,books]
  change (dropRoot G S F)ᵀ*(hang G S F*U)=_
  rw [← Matrix.mul_assoc, inject_out, imprint, Matrix.add_mul,he.1,Matrix.mul_assoc,hh,extracted,patron_plus,patron_mul]

/-- Actual equation solved, no bandwidth/coercivity assumption necessary
here. Integrable nonsingular quadratic separate. -/
theorem normal (G : Gauge) {K : KernelChoices} (P : Flight j t) (c : Side) (F : Forest (primary P.patch K c).ratio) (ht : 4≤t) :
    let S:=primary P.patch K c
    let A:=(Flight.duo K.penalty P).A0
    let V:= rawMean G S F (installed S.ratio A)
    let Z:= patron G (Precision.K ((pink K.penalty P.wing).acts (c*P.patch.L)))
    let z:= patron G (Precision.K ((pink K.penalty P.land).acts c))
    let U:= (dropRoot G S F)ᵀ
    let X:=U*V
    let Q:=patron G (Precision.probe S)
    let T:=1-Q*X
    testPrecision G S F P.wing*V=K.penalty • (Q*U)ᵀ ∧ Xᵀ*Z*X+K.penalty • (Tᵀ*T)=z := by
  intro S A V Z z U X Q T
  let H:=(pink K.penalty P.wing).acts (c*P.patch.L)
  let H':=(pink K.penalty P.land).acts c
  let W:= installed S.ratio A
  have hp : Inputs S W H H':= (Flight.tangent P K ht (c:=c) rfl).1
  let R:= extracted S F W; let Y:=probe S
  have hx : X=patron G R:=unstitch G F _
  let N:=1-Y*R
  have hv : T=patron G N := by unfold T N; rw [hx,patron_minus,patron_line,patron_mul]
  obtain ⟨he,hD⟩:=stationed F W H H' hp
  have hh : Q*U*V = 1-K.penalty⁻¹ • z := by
    rw [Matrix.mul_assoc,show U*V=_ from hx]; unfold Q; rw [← patron_mul,show probe S*R=_ from he,patron_minus,patron_line,patron_coeff]
  have hK : Z* (U*V)=Qᵀ*z := by rw [show U*V=_ from hx]; unfold Z Q z; rw [← patron_mul,show Precision.K _*R=_ from hD,patron_mul,patron_star]
  have hq := Precision.action F W H H' hp
  constructor
  · change (Uᵀ*Z*U+K.penalty • ((Q*U)ᵀ*(Q*U)))*V=_
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc Uᵀ Z, hK, Matrix.smul_mul, Matrix.mul_assoc (Q*U)ᵀ,hh, Matrix.mul_sub,Matrix.mul_one,Matrix.mul_smul, smul_sub, smul_smul,mul_inv_cancel₀ K.penalty_pos.ne',one_smul,Matrix.transpose_mul, Matrix.mul_assoc Uᵀ Qᵀ]; abel
  rw [hx,hv]; unfold z Z; rw [← patron_star, ← patron_star,← patron_mul,← patron_mul,← patron_mul,← patron_coeff,← patron_plus, show Rᵀ*Precision.K H*R+K.penalty • (Nᵀ*N)=_ from hq]
end YM.FormalBulk08.Flat
