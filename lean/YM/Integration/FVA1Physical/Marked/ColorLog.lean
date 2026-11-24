import YM.Integration.FVA1Physical.Marked.ColorAlgebra

/-! The finite exponential and connected logarithm commute with complex
source reconstruction at all degrees on slot-local physical inputs. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Marker Finset Extra.Trajectories
open scoped Classical BigOperators
variable {I : Type} [DecidableEq I] {B : Census I}
local notation "Colors" => Finset I→Marker.Poly B

def colorSubalgebra (B : Census I) : Subalgebra ℂ (Finset I→Marker.Poly B) where
  carrier := SlotLocal
  algebraMap_mem' := fun _ _ _ _ _=>rfl
  mul_mem' := SlotLocal.mul
  add_mem' := by
    intro a b ha hb s t t' same
    exact congrArg₂ (· + ·) (ha s t t' same) (hb s t t' same)

private theorem color_scalar (z : ℂ) : complexWallet (fun _ : Finset I=>Marker.Poly.bead B z)=Marker.Poly.bead B z := by
  apply Marker.Poly.ext
  intro s
  change (∑ t∈s.val.powerset,Complex.I^t.card*(Marker.Poly.bead B z).part s)=_
  by_cases h:s=B.quiet
  · subst s; simp [Marker.Poly.bead,Census.quiet]
  simp [Marker.Poly.bead,h]

def colorMap (B : Census I) : colorSubalgebra B →ₐ[ℂ] Marker.Poly B where
  toFun A := complexWallet A.val
  map_zero' := (coloring_apply (0 : Finset I→Marker.Poly B)).symm.trans (map_zero coloring)
  map_one' := by exact (color_scalar (B:=B) 1).trans (map_one _)
  map_add' A C := (coloring_apply (A.val+C.val)).symm.trans ((map_add coloring _ _).trans
    (congrArg₂ (· + ·) (coloring_apply _) (coloring_apply _)))
  map_mul' A C := color_product A.property C.property
  commutes' := color_scalar

variable [Fintype I]

private def expOn {R : Type*} [CommSemiring R] [Algebra ℂ R] (k : ℕ) (A : R) : R :=
  ∑ j∈Finset.range (k+1),(j.factorial:ℂ)⁻¹ • A^j

private theorem exp_mapped {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra ℂ R] [Algebra ℂ S]
    (f : R →ₐ[ℂ] S) (k : ℕ) (a : R) : f (expOn k a)=expOn k (f a) := by
  simp only [expOn,map_sum,map_smul,map_pow]

private def logOn {R : Type*} [CommRing R] [Algebra ℂ R] (k : ℕ) (A : R) : ℕ→R
  | 0 => 0
  | j+1 => logOn k A j + (A-expOn k (logOn k A j))

private theorem log_mapped {R S : Type*} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]
    (f : R →ₐ[ℂ] S) (k : ℕ) (a : R) (j : ℕ) : f (logOn k a j)=logOn k (f a) j := by
  induction j with
  | zero => exact map_zero _
  | succ j ih => simp only [logOn,map_add,map_sub,exp_mapped,ih]

private def readSlot (t : Finset I) : colorSubalgebra B →ₐ[ℂ] Marker.Poly B :=
  (Pi.evalAlgHom ℂ _ t).comp (colorSubalgebra B).val

private theorem log_eq (a : Marker.Poly B) (k : ℕ) : logOn (Fintype.card I) a k = iteration a k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [logOn,iteration,ih]; rfl

theorem color_exp_log {A : Colors} (h : SlotLocal A) :
    (SlotLocal (fun t=>(A t).pass) ∧ complexWallet (fun t=>(A t).pass)=(complexWallet A).pass) ∧
    SlotLocal (fun t=>connected (A t)) ∧ complexWallet (fun t=>connected (A t))=connected (complexWallet A) := by
  let a : colorSubalgebra B := ⟨A,h⟩
  let k := Fintype.card I
  have e : (expOn k a).val=fun t=>(A t).pass := funext (fun t=>exp_mapped (readSlot t) k a)
  have l : (logOn k a k).val=fun t=>connected (A t) := funext (fun t=>
    (log_mapped (readSlot t) k a k).trans (log_eq (A t) k))
  refine ⟨⟨e ▸ (expOn k a).property,?_⟩, l ▸ (logOn k a k).property,?_⟩
  · exact (congrArg complexWallet e.symm).trans (exp_mapped (colorMap B) k a)
  exact (congrArg complexWallet l.symm).trans ((log_mapped (colorMap B) k a k).trans (log_eq _ k))

end YM.Integration.FVA1Physical.Marked
