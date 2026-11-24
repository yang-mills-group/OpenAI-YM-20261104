import YM.MSbar.Dim.Plane
/-! Open tensor pullback along arbitrary orthogonal embeddings. No operations use rotations of
external flavors not represented by `S`. Will be used for dimensional analytical calculus Tr and
Mellin. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Dim
open Function Filter Set MeasureTheory Symbol
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

structure Motion (E : ℕ → Type) where
   move {m n : ℕ} : Move m n → E m → E n
   triv {m : ℕ} (a : E m) : move (LinearIsometry.id) a=a
   together {m n k : ℕ} (V:Move m n)(W:Move n k)(z:E m) : move (W.comp V) z= move W (move V z)
variable {E P : ℕ→Type} {m n : ℕ}
-- constant base (potential phases left untouched)
def constMotion (X : Type) : Motion (fun _=>X) := ⟨fun _ => id, fun _=> rfl, fun _ _ _=>rfl⟩
def vectors : Motion Hat := ⟨fun V => V, fun _=>rfl,fun _ _ _=> rfl⟩
namespace Motion

def prod (S:Motion E)(T:Motion P):Motion (fun m=> E m × P m) := {
    move := fun V a=>(S.move V a.1,T.move V a.2)
    triv := fun p=> by simp [S.triv,T.triv]
    together := fun V W p=> by simp [S.together,T.together]
}
variable (S: Motion E)
protected abbrev Natural (f:∀ m:ℕ,E m→ℂ):= ∀ ⦃i j : ℕ⦄ (L:Move i j) (x:E i), f j (S.move L x)= f i x

-- checks at each succession and rotations suffice. Useful without canonical inclusion repeated.
lemma reaches {f:∀ m:ℕ,E m→ℂ} (hv:∀ i (U: Hat i ≃ₗᵢ[ℝ] Hat i) (x:E i), f i (S.move U.toLinearIsometry x)=f i x)
   (h : ∀ m (x:E m),f (m+1) (S.move (up m) x)= f m x): S.Natural f:=by
    have he i j (L:Move i j): i ≤ j := by
       have hi := LinearMap.finrank_le_finrank_of_injective L.injective -- fix
       rw [hat_dim,hat_dim] at hi; omega
    intro i j L x
    have hp(k:ℕ)(hk:i≤k):∃ L:Move i k, f k (S.move L x)=f i x:=by
       induction k,hk using Nat.le_induction with
       | base => exact ⟨LinearIsometry.id,by rw [S.triv]⟩
       | succ k hk ih => obtain ⟨W,hw⟩:=ih; exact ⟨(up k).comp W,by rw [S.together,h,hw]⟩
    obtain ⟨K,hK⟩:=hp j (he i j L)
    obtain ⟨V,hV⟩:=aligns K L
    rw [show L=V.toLinearIsometry.comp K from DFunLike.ext _ _ (fun x=> (hV x).symm),S.together,hv,hK]
end Motion
end YM.MSbar.Dim
