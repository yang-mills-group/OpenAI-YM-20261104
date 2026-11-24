import YM.Integration.WilsonOriginalPublicRelativeGramFreePanel

/-! Signed heads on each graded quotient fix the branch of a positive
reflected Gram isometry on the entire finite public field space. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramOriented
open Finset Function Matrix Wilson RG Source Labels PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose XSpace.Structure1 Maxwell Maxwell.Wick
open MS MS.Menus MS.Land MS.Theater Local.Physical
open WilsonPositionProgramPublicContrast (assay)
open WilsonPositionProgramPublicWickGram (reading nodes)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {I:Type}[Fintype I]

private theorem dot (x y:I→ℂ)(M:Matrix I I ℂ):
    assay x y M=star x ⬝ᵥ (M*ᵥy):=by
  unfold assay Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _=>by change _=star (x i)*_; ring

theorem transform (A M:Matrix I I ℂ)(x y:I→ℂ):
    assay (A*ᵥx) (A*ᵥy) M=assay x y (Aᴴ*M*A):=by
  rw [dot,dot,Matrix.star_mulVec,←Matrix.dotProduct_mulVec,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]

private theorem sub (u v x:I→ℂ)(M:Matrix I I ℂ):
    assay (u-v) x M=assay u x M-assay v x M:=by
  unfold assay
  simp only [Pi.sub_apply,star_sub,sub_mul,sum_sub_distrib]

variable [DecidableEq I]

theorem determined (grade:I→ℕ)(G A:Matrix I I ℂ)
    (positive:∀x:I→ℂ,assay x x G=0 → x=0)
    (gram:Aᴴ*G*A=G)
    (heads:∀i j,grade j≤grade i → A i j=(1:Matrix I I ℂ) i j): A=1:=by
  have column (s:ℕ)(j:I)(atGrade:grade j=s):A.col j=Pi.single j 1:=by
    induction s using Nat.strong_induction_on generalizing j with
    | h n lower =>
      let e:I→ℂ:=Pi.single j 1
      let v:I→ℂ:=A*ᵥe-e
      have basis1 (i k:I):(1:Matrix I I ℂ) i k=(Pi.single k 1:I→ℂ) i:=by
        by_cases eq:i=k <;> simp [Matrix.one_apply,eq]
      have supported (i:I)(nz:v i≠0):grade i<n:=by
        by_contra! fail
        have equal:=heads i j (atGrade.trans_le fail)
        apply nz
        change (A*ᵥPi.single j 1) i - (Pi.single j 1:I→ℂ) i=0
        rw [Matrix.mulVec_single_one]
        exact sub_eq_zero.mpr (equal.trans (basis1 i j))
      have fixed:A*ᵥv=v:=by
        ext i
        calc
          _=∑k,(1:Matrix I I ℂ) i k*v k:=by
            change (∑k,A i k*v k)=_
            apply Finset.sum_congr rfl
            intro k _
            by_cases nz:v k=0
            · simp [nz]
            · rw [show A i k=(1:Matrix I I ℂ) i k from
                (congrFun (lower (grade k) (supported k nz) k rfl) i).trans (basis1 i k).symm]
          _=v i:=congrFun (Matrix.one_mulVec v) i
      have read:=transform A G e v
      rw [gram,fixed] at read
      have null:assay v v G=0:=(sub (A*ᵥe) e v G).trans (sub_eq_zero.mpr read)
      have clean:A*ᵥe=e:=sub_eq_zero.mp (positive v null)
      simpa only [e,Matrix.mulVec_single_one] using clean
  apply Matrix.ext
  intro i j
  calc
    A i j = (Pi.single j 1:I→ℂ) i := congrFun (column (grade j) j rfl) i
    _ = _:=by by_cases eq:i=j <;> simp [Matrix.one_apply,eq]

variable {G:Gauge}(B:Local.Physical.Deck G)(d:ℕ)(a:Axis)

def maxwell:Matrix (Glyph B d) (Glyph B d) ℂ:=reading a (nodes a) id

theorem original (grade:Glyph B d→ℕ)(A:Matrix (Glyph B d) (Glyph B d) ℂ)
    (gram:Aᴴ*maxwell B d a*A=maxwell B d a)
    (heads:∀i j,grade j≤grade i → A i j=(1:Matrix (Glyph B d) (Glyph B d) ℂ) i j):A=1:=by
  let M:=maxwell B d a
  obtain ⟨k,δ,kp,dp,strict⟩:=WilsonPositionProgramPublicWickGram.original a (id:Glyph B d→Glyph B d) injective_id
  have strong:=strict M (by change ‖(reading a (nodes a) (id:Glyph B d→Glyph B d))-_‖≤δ; simpa only [sub_self,norm_zero] using dp.le)
  apply determined grade M A _ gram heads
  intro x zero
  by_contra non
  have high:0<k*‖x‖^2:=mul_pos kp (pow_pos (norm_pos_iff.mpr non) _)
  have impossible:=strong x
  rw [zero,norm_zero] at impossible
  linarith

end YM.Integration.WilsonOriginalPublicRelativeGramOriented
