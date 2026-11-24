import YM.Euclid.Lift
import YM.Euclid.Null

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace YM.Answer.ContinuumLimit.OriginalTableConjugation

variable {G : Gauge} {L : Register G}

theorem graded (S : Table L) (sym : S.Symmetric) (spin : S.RealSpin)
    {n : ℕ} {x : Points n} (hx : x ∈ conf n) (v : Fin n → S.Tag) :
    S.useAt S x (fun i => ⟨(v i).1, S.conj spin (v i).1 (v i).2⟩) =
      star (S.useAt S x v) := by
  let w : Fin n → L.Token := fun i => ⟨(v i).1, S.representative _ (v i).2⟩
  have projected : S.classTokens ∘ w = v := by
    funext i
    change Sigma.mk (v i).1 (S.project _ (S.representative _ (v i).2)) = v i
    rw [S.rep]
  have conjugated : S.classTokens ∘ (L.conjugate ∘ w) =
      fun i => ⟨(v i).1, S.conj spin (v i).1 (v i).2⟩ := by
    funext i
    have h := S.conj_project spin (v i).1 (S.representative _ (v i).2)
    rw [S.rep] at h
    change Sigma.mk (v i).1 (S.project _ (star (S.representative _ (v i).2))) =
      Sigma.mk (v i).1 (S.conj spin _ (v i).2)
    exact congrArg (Sigma.mk (v i).1) h.symm
  calc
    _ = S.useAt S x (S.classTokens ∘ (L.conjugate ∘ w)) :=
      congrArg (S.useAt S x) conjugated.symm
    _ = S.read x (L.conjugate ∘ w) := S.at_project S sym (fun _ => le_rfl) hx _
    _ = star (S.read x w) := spin.real hx w
    _ = star (S.useAt S x (S.classTokens ∘ w)) :=
      congrArg star (S.at_project S sym (fun _ => le_rfl) hx w).symm
    _ = _ := congrArg (fun q => star (S.useAt S x q)) projected

theorem fieldsReal (S : Table L) (sym : S.Symmetric) (spin : S.RealSpin)
    {n : ℕ} {x : Points n} (hx : x ∈ conf n) (v : Fin n → S.Tag)
    (fixed : ∀ i, S.conj spin (v i).1 (v i).2 = (v i).2) :
    (S.useAt S x v).im = 0 := by
  have h := graded S sym spin hx v
  have e : (fun i => (⟨(v i).1, S.conj spin (v i).1 (v i).2⟩ : S.Tag)) = v := by
    funext i
    rw [fixed i]
  rw [e] at h
  exact Complex.conj_eq_iff_im.mp h.symm

end YM.Answer.ContinuumLimit.OriginalTableConjugation

