import YM.RG11Proof.Scale.Portable

/-!
# Invert the engineering commutator on strict weight-lower block

Use `Constraints.position` on labels with a unit of weight zero and each H
action graded. No assuming inverse outside this sector.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Bearing
open YM.RG11.Jets YM.RG11.Scale PowerSeries
open scoped BigOperators Classical
variable {J I:Type*}

def divide (w:J→ℕ)(i j:J):ℝ:= (w i:ℝ) - (w j:ℝ)

def arch (w:J→ℕ):Square J ℝ:= Matrix.diagonal fun i=> (w i:ℝ)

def diagonalX (w:J→ℕ):Square J (PowerSeries ℝ):=(arch w).map C

def spot (w:J→ℕ)(X:Square J ℝ)(c:ℝ→ℝ):Square J ℝ:=Matrix.of fun i j=> c (divide w i j) * X i j

/-- Distinct from the position multiplication-closed filtration `vary`:
 require STRICT lowering in every nonidentity piece of N. -/
def Slopes (w:J→ℕ)(X:Square J ℝ):Prop:= ∀ i j,w i≤w j→ X i j=0

variable [Fintype J](w:J→ℕ){H:I→Square J ℝ}

 theorem segmentation (D:Square J ℝ): arch w * D-D*arch w=spot w D id:=by
   ext i j
   simp only [spot, Matrix.of_apply, Matrix.sub_apply,arch, Matrix.diagonal_mul, Matrix.mul_diagonal,id_eq,divide]; ring

 theorem graded_spot_right (X A:Square J ℝ)(h:graded w A)(c:ℝ→ℝ): spot w (X*A) c=spot w X c*A:=by
   ext i j
   simp only [spot,Matrix.of_apply,Matrix.mul_apply,Finset.mul_sum]
   apply Finset.sum_congr rfl; intro k _
   by_cases h₁:w k=w j
   · simp only [divide,h₁,mul_assoc]
   simp only [h h₁,mul_zero]

 theorem graded_spot_left (X A:Square J ℝ)(h:graded w A)(c:ℝ→ℝ): spot w (A*X) c=A*spot w X c:=by
   ext i j
   simp only [spot,Matrix.of_apply, Matrix.mul_apply,Finset.mul_sum]
   apply Finset.sum_congr rfl; intro k _
   by_cases h₁:w i=w k
   · simp only [divide,h₁]; ring
   simp only [h h₁,zero_mul,mul_zero]

 theorem spot_across (u:J)(h:∀ i,graded w (H i)){X:Square J ℝ}
     (he:X∈(Constraints.position u w H).vary)(c:ℝ→ℝ): spot w X c∈ (Constraints.position u w H).vary:=by
   obtain ⟨ha,hb,hc⟩:=Constraints.mem_position_iff.mp he
   refine Constraints.mem_position_iff.mpr ⟨fun i j ht=>by simp [spot,ha i j ht],fun i=>by simp [spot,hb],fun i=>?_⟩
   rw [←graded_spot_right w _ _ (fun e=>h i e), ←graded_spot_left w _ _ (fun e=>h i e),hc i]

 theorem on_rail {u:J}{X:Square J ℝ}(he:X∈ (Constraints.position u w H).vary)(f:ℝ→ℝ)(h:f 0=0): Slopes w (spot w X f):=by
   intro i j hJ
   obtain hd|hd:=lt_or_eq_of_le hJ
   · simp [spot,Constraints.mem_position_iff.mp he |>.1 i j hd]
   simp [spot,divide,hd,h]

omit [Fintype J] in
@[simp] theorem aim_piece (n:ℕ)(w:J→ℕ):piece n (diagonalX w)=if n=0 then arch w else 0:=Matrix.ext fun i j=>by
   split <;> rename_i he <;> simp only [piece_apply,diagonalX,Matrix.map_apply,coeff_C,he,↓reduceIte,Matrix.zero_apply]

-- simplified because constant arch
 theorem arch_piece (i:ℕ)(A:Square J (PowerSeries ℝ)):
    piece i (diagonalX w*A)=arch w * piece i A:=Matrix.ext fun j k=>by
      simp only [piece_apply, Matrix.mul_apply,diagonalX,Matrix.map_apply,map_sum,coeff_C_mul]

 theorem arch_right (i:ℕ)(A:Square J (PowerSeries ℝ)):
    piece i (A*diagonalX w)=piece i A * arch w:=Matrix.ext fun j k=>by
      simp only [piece_apply, Matrix.mul_apply,diagonalX,Matrix.map_apply,map_sum,coeff_mul_C]

omit [Fintype J] in
 theorem disperses (X:Square J ℝ):
     spot w (spot w X (fun r=> -1/r)) id+X = isolate w X:=by
   ext i j; simp only [Matrix.add_apply,spot,id_eq,isolate,Matrix.of_apply]
   by_cases he:w i=w j
   · simp [divide,he]
   have hx: divide w i j ≠ 0:=sub_ne_zero.mpr (by exact_mod_cast he)
   simp only [he,↓reduceIte]; field_simp; ring

omit [Fintype J] in
 theorem solo {X N b:Square J ℝ}(h:Slopes w N)(hh:graded w b)(he:b=spot w N id+X): N = spot w X (fun r=> -1/r) ∧ b=isolate w X:=by
   suffices hv : N=spot w X (fun r=> -1/r) from ⟨hv,by rw [he,hv,disperses]⟩
   ext i j; simp only [spot,Matrix.of_apply]
   by_cases heq:w i=w j
   · rw [h i j heq.le]; simp [divide,heq]
   have hx: divide w i j ≠ 0:=sub_ne_zero.mpr (by exact_mod_cast heq)
   have hu : b i j=divide w i j*N i j+X i j:=congrArg (fun (f:Square J ℝ)=>f i j) he
   rw [hh heq] at hu
   field_simp
   linarith
end YM.RG11.Bearing
