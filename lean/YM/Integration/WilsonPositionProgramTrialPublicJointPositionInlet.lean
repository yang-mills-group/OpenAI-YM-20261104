import YM.Integration.WilsonOriginalPublicFigurePosition

/-! Apply the original public formal position inverse to an entire varying measured field on every retained grade. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPositionInlet
open Filter Set Function PowerSeries Finset Maxwell XSpace XSpace.Normalize XSpace.Cirrus XSpace.Structure1 XSpace.Rose
open scoped Topology Classical BigOperators
variable {G:Gauge}{d:ℕ}

def unitRead (G:Gauge)(d:ℕ):Sec G d→ₗ[ℂ]ℂ:=(MvPolynomial.lcoeff ℂ 0).comp (shellSector G d).subtype

theorem unitRead_one:unitRead G d (leaf G d)=1:=by
  change MvPolynomial.coeff 0 (1:WickPol G)=1
  simp

def column (b:ℕ→Sec G d):Guard G d:=PowerSeries.mk fun j=>(unitRead G d).smulRight (b j)
def read (F:Guard G d)(j:ℕ):Sec G d:=coeff j F (leaf G d)
def applyTo (F:Guard G d)(b:ℕ→Sec G d):ℕ→Sec G d:=read (F*column b)

theorem values (b:ℕ→Sec G d)(j:ℕ):read (column b) j=b j:=by
  simp only [read,column,coeff_mk,LinearMap.smulRight_apply,unitRead_one,one_smul]

theorem product (F H:Guard G d)(j:ℕ):
    read (F*H) j=∑i∈range (j+1),coeff i F (read H (j-i)):=by
  rw [read,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i k=>coeff i F*coeff k H) j,LinearMap.sum_apply]
  rfl

theorem restored {Z U:Guard G d}(closed:Z*U=1)(b:ℕ→Sec G d)(j:ℕ):
    ∑i∈range (j+1),coeff i Z (applyTo U b (j-i))=b j:=by
  change (∑i∈range (j+1),coeff i Z (read (U*column b) (j-i)))=_
  rw [←product,←mul_assoc,closed,one_mul,values]

theorem preserves {U:Guard G d}(legal:Formal U)(k:ℕ):
    applyTo U (fun j=>if j=0 then leaf G d else 0) k=if k=0 then leaf G d else 0:=by
  obtain ⟨T,rfl⟩:=legal.actions
  rw [applyTo,product]
  simp only [values,apply_ite _ _ _,map_zero,prime_deck]
  by_cases zero:k=0
  · subst k;simp
  · rw [if_neg zero]
    apply sum_eq_zero
    intro j hj
    have le:=Nat.lt_succ_iff.mp (mem_range.mp hj)
    by_cases same:j=k
    · subst j;simp [zero]
    · have gap:k-j≠0:=by omega
      simp [gap]

/-- A single true public section, with its own position records, serves every measured series and every determining test. -/
theorem purchased (W:Initialize G)(V:Store G)(d:ℕ):∀ᶠ M:Mesh in Front,
    let Z:=deck (V.layout W M d)
    V.Meets W M d ∧ ∃U:Guard G d,Formal U ∧ Z*U=1 ∧ U*Z=1 ∧
      (∀k,applyTo U (fun j=>if j=0 then leaf G d else 0) k=if k=0 then leaf G d else 0) ∧
      ∀(b:ℕ→Sec G d)(k:ℕ),∑i∈range (k+1),coeff i Z (applyTo U b (k-i))=b k:=by
  filter_upwards [(V.nested_solution W d frontier).2] with M paid
  obtain ⟨U,legal,uz,zu⟩:=reversal_exists paid.1.1
  exact ⟨paid.1,U,legal,zu,uz,preserves legal,restored zu⟩

end YM.Integration.WilsonPositionProgramTrialPublicJointPositionInlet
end
