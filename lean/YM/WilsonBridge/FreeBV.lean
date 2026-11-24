import YM.WilsonBridge.Letters

/-!
# Acyclic free BV scalar projection, in `MS.Swirl` itself

Prove the scalar statement from letter conditions, polynomial IBP (specialized
below in `Resolution`) and a highest-*field*-rank argument. No analyticity,
no assertion of vanishing of the residual harmonic-mode operator in the MS
removal estimates. Will apply using based gauges at a fixed cutoff.
-/

set_option autoImplicit false
noncomputable section

namespace YM.WilsonBridge
open MS MS.Koszul MS.Swirl MS.Puff MS.Cylinder
open MS.Orbit MS.Book
open Function Finset
open scoped BigOperators
variable {V I : Type} {p : Sector V}
variable {B : Bonded p I} [Fintype V] [Fintype I]

/-- A noninteracting/free BV differential, with the sign conventions of `YM.MS` (vertex
    is in the LOG DENSITY, not the energy). -/
structure FreeBV (B : Bonded p I) where
  quadratic : Raw V ℂ
  symm : MS.Koszul.Symm p quadratic
  even : Pure p false quadratic
  rank : Book.rank 2 quadratic
  classicalMaster : link B.BV true p quadratic quadratic=0
  div : B.BV quadratic=0
  Q : OddField p
  hamiltonian (F): Q.deriv F=link B.BV true p quadratic F

namespace FreeBV
variable (Z : FreeBV B)
local notation "Q" => OddField.deriv Z.Q
local notation "Δ" => B.BV (R:=ℂ)

def boundary : Op V ℂ := Q + Δ
lemma boundary_apply (F) : Z.boundary F = Q F + Δ F := rfl
lemma boundary_symm {F} (h : MS.Koszul.Symm p F) : MS.Koszul.Symm p (Z.boundary F) :=
  (Z.Q.apply_symm h).add (loop_symm h)
lemma boundary_limit {F} {n : ℤ} (h : Limit F n) : Limit (Z.boundary F) n := by
  rw [Z.boundary_apply,Z.hamiltonian]
  exact ((roofLink B (rank_limit Z.rank) h).up (by omega)).add ((roofLap B h).up (by omega))

lemma square_zero {F : Raw V ℂ} (h : MS.Koszul.Symm p F) : Z.boundary (Z.boundary F)=0 := by
  have hz : Q (Q F)=0 := by
    simp_rw [Z.hamiltonian]
    apply two_nsmul_eq_zero.mp
    have hH:= B.costs.double_j Z.even Z.symm h
    simp_rw [← show Δ = loop B.fee (⇑B.dual) (⇑B.plain) univ from rfl] at hH
    rw [Z.classicalMaster,show link Δ true p 0 F=0 by simp [link,LinearMap.zero_apply],add_zero] at hH
    exact hH
  have hK : Δ (Q F)+ Q (Δ F)=0 := by
    simp_rw [Z.hamiltonian]
    have hH:= B.costs.anti_j Z.even Z.symm h
    simp_rw [← show Δ = loop B.fee (⇑B.dual) (⇑B.plain) univ from rfl] at hH
    rw [Z.div,show link Δ true p 0 F=0 by simp [link,LinearMap.zero_apply],add_zero] at hH
    exact hH
  simp_rw [boundary_apply,map_add,hz,zero_add, show Δ (Δ F)=0 from B.costs.quits h,add_zero]
  rw [add_comm,hK]

lemma commuteMask (n : ℕ) (k : ℤ) {F} (h : Limit F n) :
    Q (mask k F) = mask k (Q F) := by
  rw [limit_eq_rankSum _ h]; simp_rw [map_sum]
  apply Finset.sum_congr rfl; intro i _
  have hr:= rankMod F (i:ℤ)
  by_cases he:(i:ℤ)=k
  · subst k; rw [(rank_hat i).mp hr,(rank_hat i).mp (Z.Q.apply_rank hr)]
  rw [rank_off hr he, rank_off (Z.Q.apply_rank hr) he,map_zero]

/-- Free resolution. In particular it is enough (on the based alphabet) to prove green
    identities on two-point matrices, not prove an analytic equality for all perturbative integrals. -/
lemma resolution (R : OddField p) (hR : ∀ x, Q (R.field x)+R.deriv (Z.Q.field x)=atLetter x)
    (n:ℕ) {F : Raw V ℂ} (h : Limit F n) (hs : MS.Koszul.Symm p F) (hF : Z.boundary F=0) :
    ∃ (S : Raw V ℂ) (c : ℂ), Limit S n ∧ MS.Koszul.Symm p S ∧ F=coin c + Z.boundary S := by
  induction n generalizing F with
  | zero =>
    exact ⟨0,F [],(fun _ _=>rfl),Symm.zero,(limit_zero_eq_coin (by simpa using h)).trans (by simp)⟩
  | succ n ih =>
    let m : ℕ:= n+1
    let Y:= mask m F
    have hY : Book.rank m Y:= rankMod F (m:ℤ)
    have hsY : MS.Koszul.Symm p Y := mask_symm hs
    have hy : Q Y=0 := by
      unfold Y; rw [Z.commuteMask (n:=m) m h]
      rw [Z.boundary_apply] at hF
      rw [eq_neg_of_add_eq_zero_left hF,map_neg,limit_mask_off (roofLap B h) (by dsimp only [m]; omega), neg_zero]
    let S:= (m:ℂ)⁻¹ • R.deriv Y
    have htr : Q S = Y := by
      have hx : Q (R.deriv Y)+R.deriv (Q Y)=(m:ℂ) • Y := Z.Q.bracket_rank R hR m hY hsY
      rw [hy,map_zero,add_zero] at hx
      unfold S; rw [map_smul,hx,inv_smul_smul₀ (by unfold m; exact_mod_cast n.succ_ne_zero)]
    have hS : Limit S m := (rank_limit (R.apply_rank hY)).smul _
    have he : MS.Koszul.Symm p S := (R.apply_symm hsY).smul _
    let W := F - Z.boundary S
    have hW : Limit W n := by
      have hh : Limit W m := h.sub (Z.boundary_limit hS)
      have hU : mask m W = 0 := by
        unfold W; rw [Z.boundary_apply,htr,map_sub,map_add,(rank_hat _).mp hY,
          limit_mask_off (roofLap B hS) (by omega), add_zero]
        exact sub_self _
      simpa [m] using limit_down hh hU
    obtain ⟨S',c,hS',h',E⟩:= ih hW (hs.sub (Z.boundary_symm he)) (by unfold W; rw [map_sub,hF,Z.square_zero he, sub_zero])
    refine ⟨S'+S,c,(hS'.up (by omega)).add hS,h'.add he, ?_⟩
    rw [map_add,← add_assoc]
    exact sub_eq_iff_eq_add.mp E

-- Both Wick functionals use the SAME full integrand. This is a strengthening of
-- a scalar vacuum-term identity: their argument may carry physical insertions.
lemma scalar_independent (R : OddField p) (hR : ∀ x, Q (R.field x)+R.deriv (Z.Q.field x)=atLetter x)
    (K L : Cog.Grain V)
    (hK : ∀ F ∈ Mini V, MS.Koszul.Symm p F → View K (Z.boundary F)=0)
    (hL : ∀ F ∈ Mini V, MS.Koszul.Symm p F → View L (Z.boundary F)=0)
    (F : Raw V ℂ) (h : F∈ Mini V) (h₁ : MS.Koszul.Symm p F) (h₂ : Z.boundary F=0) :
    View K F = View L F := by
  obtain ⟨m,h⟩:= h
  obtain ⟨S,c,hS,hS',rfl⟩:= Z.resolution R hR m h h₁ h₂
  simp only [map_add,minView,hK S (minH hS) hS',hL S (minH hS) hS']
end FreeBV
end YM.WilsonBridge
