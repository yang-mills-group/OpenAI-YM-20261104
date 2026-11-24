import YM.WilsonBridge.FreeBV

/-!
# The finite based-gauge complex. Matrix identities required on a gauge fixing

Condition is a *generalized inverse*, with the missing longitudinal projection
provided by the ghost line. Uses literally the graded Wick rule of `Endμ`.
All coordinates independent (quotient sites and link orbits later); antifields
are canonically dual, no redundant constant-ghost directions.
-/

set_option autoImplicit false
noncomputable section

namespace YM.WilsonBridge.Based
open MS MS.Koszul MS.Book MS.Swirl MS.Cylinder MS.Orbit
open Function Finset
open scoped BigOperators Matrix

variable {J I : Type}
abbrev Letters (J I : Type) := (J ⊕ I) ⊕ (J ⊕ I)
abbrev a (i:J) : Letters J I:=.inl (.inl i)
abbrev k (i:J) : Letters J I:=.inr (.inl i)
abbrev c (x:I) : Letters J I:=.inl (.inr x)
abbrev b (x:I) : Letters J I:=.inr (.inr x)

def parity (J I : Type) : Sector (Letters J I) :=
  Sum.elim (Sum.elim (fun _=>false) (fun _=>true)) (Sum.elim (fun _=>true) (fun _=>false))

local notation "τφ" => parity J I
local notation "a[" i "]" => atLetter (a i) (R:=ℂ)
local notation "k[" i "]" => atLetter (k i) (R:=ℂ)
local notation "c[" i "]" => atLetter (c i) (R:=ℂ)
local notation "b[" i "]" => atLetter (b i) (R:=ℂ)
local infixl:70 " ⋆ " => product (parity J I)

/-- `∆ = D_A D_K − D_c D_B`. -/
def bracket (J I) : Bonded (parity J I) (J⊕I) where
  plain:=⟨Sum.inl,Sum.inl_injective⟩
  dual:=⟨Sum.inr,Sum.inr_injective⟩
  diff _ _:= Sum.inl_ne_inr
  wave i:= by cases i <;> rfl
variable [Fintype J] [Fintype I]

lemma lap_apply (F : Raw (Letters J I) ℂ) :
    (bracket J I).BV F = (∑ i : J, D (a i) (D (k i) F)) - ∑ i : I, D (c i) (D (b i) F) := by
  simp only [Bonded.BV,loop,LinearMap.sum_apply,LinearMap.smul_apply,diffPair_apply]
  rw [Fintype.sum_sum_type (α₁:=J) (α₂:=I)]
  simp_rw [show ∀ i:J,(bracket J I).fee (R:=ℂ) (.inl i)=1 from fun i=>rfl,
    show ∀ i:I,(bracket J I).fee (R:=ℂ) (.inr i)= -1 from fun i=>rfl, neg_smul, one_smul,
    Finset.sum_neg_distrib, sub_eq_add_neg]; rfl

/-- Boson energy Hessian and gauge gradient. -/
structure Kinetics (J I : Type) where
  H : Matrix J J ℂ
  X : Matrix J I ℂ
  sym (i j) : H i j=H j i

namespace Kinetics
variable (T : Kinetics J I)
def vector : Letters J I → Raw (Letters J I) ℂ
  | .inl (.inl i) => ∑ j, T.X i j • c[j]
  | .inl (.inr _) => 0
  | .inr (.inl i) => -(∑ j, T.H i j • a[j])
  | .inr (.inr i) => ∑ j, T.X j i • k[j]

private lemma negRank {V : Type} {F : Raw V ℂ} {d : ℤ} (h : Book.rank d F) :
    Book.rank d (-F) := fun l hl=>by simp [h _ hl]
private lemma negPure {V : Type} {π : Sector V} {F : Raw V ℂ} {d : Bool} (h : Pure π d F) :
    Pure π d (-F) := fun l hl=>by simp [h _ hl]

def Q : OddField τφ where
  field := T.vector
  rank x:= by
    rcases x with (i|i)|(i|i)
    · exact Rails.sum univ fun j _=> (rank_letter _).smul _
    · exact Rails.zero
    · exact negRank (Rails.sum univ fun j _=> (rank_letter _).smul _)
    exact Rails.sum univ fun j _=> (rank_letter _).smul _
  odd x:= by
    rcases x with (i|i)|(i|i)
    · exact Pure.sum univ fun j _=> (speaks_p (p:=τφ) (c j)).smul _
    · exact Pure.zero
    · exact negPure (Pure.sum univ fun j _=> (speaks_p (p:=τφ) (a j)).smul _)
    exact Pure.sum univ fun j _=> (speaks_p (p:=τφ) (k j)).smul _
  symm x:= by
    rcases x with (i|i)|(i|i)
    · exact Symm.sum univ fun j _=> (speaks_s _).smul _
    · exact Symm.zero
    · exact (Symm.sum univ fun j _=> (speaks_s _).smul _).neg
    exact Symm.sum univ fun j _=> (speaks_s _).smul _

@[simp] lemma Qa (i:J) : T.Q.field (a i) = ∑ j,T.X i j • c[j] := rfl
@[simp] lemma Qk (i:J) : T.Q.field (k i) = -(∑ j,T.H i j • a[j]) := rfl
@[simp] lemma Qc (i:I) : T.Q.field (c i) = 0 := rfl
@[simp] lemma Qb (i:I) : T.Q.field (b i) = ∑ j,T.X j i • k[j] := rfl

lemma Q_apply (F : Raw (Letters J I) ℂ) :
    T.Q.deriv F = (∑ i : J, (∑ j,T.X i j • c[j]) ⋆ D (a i) F) +
      ((∑ i : J, -(∑ j,T.H i j • a[j]) ⋆ D (k i) F) +
        ∑ j : I, (∑ i,T.X i j • k[i]) ⋆ D (b j) F) := by
  rw [OddField.run,Fintype.sum_sum_type]; simp only [Fintype.sum_sum_type]
  change (∑ i:J, _)+ (∑ j:I,(product τφ 0 (D (c j) F))) + _ = _
  simp only [map_zero, LinearMap.zero_apply, Finset.sum_const_zero,add_zero]; rfl

/-- The blocks of the specified quadratic form. -/
structure Blocks (F : Raw (Letters J I) ℂ) : Prop where
  DK i : D (k i) F = ∑ j,T.X i j • c[j]
  DA i : D (a i) F = -(∑ j,T.H i j • a[j])
  Dc i : D (c i) F = -(∑ j,T.X j i • k[j])
  D_B i : D (b i) F = 0

namespace Blocks
variable {S : Raw (Letters J I) ℂ} {T : Kinetics J I} (h : T.Blocks S)
include h
lemma hamiltonian (he : Pure τφ false S) (F) :
    T.Q.deriv F = link (bracket J I).BV true τφ S F := by
  rw [T.Q_apply,(bracket J I).by_lap he,Fintype.sum_sum_type]
  change _=(∑ i:J,(1:ℂ) • (D (k i) S ⋆ D (a i) F + D (a i) S ⋆ D (k i) F))+
    (∑ j:I, (-(1:ℂ)) • (D (b j) S ⋆ D (c j) F + D (c j) S ⋆ D (b j) F))
  simp_rw [h.DK,h.D_B,h.DA,h.Dc]; simp [add_assoc, Finset.sum_add_distrib]

def toFreeBV (hr : Book.rank 2 S) (hs : MS.Koszul.Symm τφ S) (he : Pure τφ false S)
    (hm : link (bracket J I).BV true τφ S S=0) : FreeBV (bracket J I) where
  quadratic := S
  symm := hs
  even := he
  rank := hr
  classicalMaster := hm
  div := by
    rw [lap_apply]; simp_rw [h.DK,h.D_B,map_zero,map_sum,map_smul, show ∀ i:J,∀ j:I,
      D (a i) c[j]=0 from fun i j=>unheard _ (by simp [a,c])]; simp
  Q := T.Q
  hamiltonian F := h.hamiltonian he F
end Blocks

variable [DecidableEq J] [DecidableEq I]

/-- A gauge fixing for which Wick scalar projection kills boundaries. `N` is the full `AA`
    covariance, `Y` is `−` the full `cK` covariance. -/
structure Fixing (T : Kinetics J I) where
  N : Matrix J J ℂ
  Y : Matrix I J ℂ
  sym i j : N i j=N j i
  green : N*T.H + T.X*Y=1
  ghost : Y*T.X=1

namespace Fixing
variable {T : Kinetics J I} (P : Fixing T)
def chill : Cog.Grain (Letters J I)
  | .inl (.inl i),.inl (.inl j) => P.N i j
  | .inl (.inr i),.inr (.inl j) => - P.Y i j
  | .inr (.inl j),.inl (.inr i) => P.Y i j
  | _,_=> 0
/-- The Wick line uses **half** the covariance. -/
def half : Cog.Grain (Letters J I) := fun i j=> (1/2:ℂ)*P.chill i j
lemma ch (i j) : Chill P.half i j=P.chill i j:= by unfold Chill half; ring
lemma clear : Cog.Clear τφ P.half := by
  rintro ((i|i)|(i|i)) ((j|j)|(j|j)) h <;> first| rfl| simp [half,chill] at h
lemma symmetry : Cog.Sym τφ P.half := by
  rintro ((i|i)|(i|i)) ((j|j)|(j|j)) <;>
    simp [half,chill,parity, P.sym]

-- matrix contraction on letters. Use these sum forms also to avoid reshaping slots in IBP.
lemma contracts {E : Type} [AddCommGroup E] [Module ℂ E] (i : J) (f : J → E) :
    (∑ j, P.N i j • ∑ k:J, T.H j k • f k) + (∑ j,T.X i j • ∑ k:J,P.Y j k • f k)=f i := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, Finset.sum_comm (s:=univ (α:=I))]; simp_rw [← Finset.sum_smul]
  rw [← Finset.sum_add_distrib]; simp_rw [← add_smul]
  change ∑ k:J, (P.N*T.H + T.X*P.Y) i k • _ = _
  rw [P.green]; simp [Matrix.one_apply, ite_smul]

lemma contractsTranspose {E : Type} [AddCommGroup E] [Module ℂ E] (i : J) (f : J → E) :
    (∑ j, T.H i j • ∑ k:J, P.N j k • f k) + (∑ j,P.Y j i • ∑ k:J,T.X k j • f k)=f i := by
  have H : T.H * P.N + P.Y.transpose * T.X.transpose=1 := by
    have h:= congr_arg Matrix.transpose P.green
    rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_one,
      show T.H.transpose=T.H from funext fun i=>funext fun j=> T.sym j i,
      show P.N.transpose=P.N from funext fun i=>funext fun j=> P.sym j i] at h
    exact h
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, Finset.sum_comm (s:=univ (α:=I))]; simp_rw [← Finset.sum_smul]
  rw [← Finset.sum_add_distrib]; simp_rw [← add_smul]
  change ∑ k:J, (T.H*P.N + P.Y.transpose*T.X.transpose) i k • _ = _
  rw [H]; simp [Matrix.one_apply, ite_smul]

lemma contractsGhost {E : Type} [AddCommGroup E] [Module ℂ E] (i : I) (f : I → E) :
    (∑ j, P.Y i j • ∑ k:I,T.X j k • f k)=f i := by
  simp_rw [Finset.smul_sum, smul_smul]; rw [Finset.sum_comm]; simp_rw [← Finset.sum_smul]
  change ∑ k:I, (P.Y*T.X) i k • _= _
  rw [P.ghost]; simp [Matrix.one_apply, ite_smul]
lemma contractsGhostTranspose {E : Type} [AddCommGroup E] [Module ℂ E] (i : I) (f : I → E) :
    (∑ j, T.X j i • ∑ k:I,P.Y k j • f k)=f i := by
  have h:= congr_arg Matrix.transpose P.ghost
  rw [Matrix.transpose_mul, Matrix.transpose_one] at h
  simp_rw [Finset.smul_sum, smul_smul]; rw [Finset.sum_comm]; simp_rw [← Finset.sum_smul]
  change ∑ k:I, (T.X.transpose*P.Y.transpose) i k • _= _
  rw [h]; simp [Matrix.one_apply, ite_smul]

def primitive : Letters J I → Raw (Letters J I) ℂ
  | .inl (.inl i) => -(∑ j, P.N i j • k[j])
  | .inl (.inr i) => ∑ j, P.Y i j • a[j]
  | .inr (.inl i) => ∑ j, P.Y j i • b[j]
  | .inr (.inr _) => 0

def R : OddField τφ where
  field := P.primitive
  rank x:= by
    rcases x with (i|i)|(i|i)
    · exact negRank (Rails.sum univ fun j _=> (rank_letter _).smul _)
    · exact Rails.sum univ fun j _=> (rank_letter _).smul _
    · exact Rails.sum univ fun j _=> (rank_letter _).smul _
    exact Rails.zero
  odd x:= by
    rcases x with (i|i)|(i|i)
    · exact negPure (Pure.sum univ fun j _=> (speaks_p (p:=τφ) (k j)).smul _)
    · exact Pure.sum univ fun j _=> (speaks_p (p:=τφ) (a j)).smul _
    · exact Pure.sum univ fun j _=> (speaks_p (p:=τφ) (b j)).smul _
    exact Pure.zero
  symm x:= by
    rcases x with (i|i)|(i|i)
    · exact (Symm.sum univ fun j _=> (speaks_s _).smul _).neg
    · exact Symm.sum univ fun j _=> (speaks_s _).smul _
    · exact Symm.sum univ fun j _=> (speaks_s _).smul _
    exact Symm.zero

@[simp] lemma Ra (i:J) : P.R.field (a i) = -(∑ j,P.N i j • k[j]) := rfl
@[simp] lemma Rk (i:J) : P.R.field (k i) = ∑ j,P.Y j i • b[j] := rfl
@[simp] lemma Rc (i:I) : P.R.field (c i) = ∑ j,P.Y i j • a[j] := rfl
@[simp] lemma Rb (i:I) : P.R.field (b i) = 0 := rfl

lemma basis_contract (x) : T.Q.deriv (P.R.field x)+P.R.deriv (T.Q.field x)=atLetter x := by
  rcases x with (i|i)|(i|i)
  · change T.Q.deriv (P.R.field (a i))+P.R.deriv (T.Q.field (a i))=_
    simp_rw [P.Ra,T.Qa,map_neg,map_sum,map_smul,OddField.on_letter,P.Rc,T.Qk,smul_neg,Finset.sum_neg_distrib, neg_neg]
    exact P.contracts i _
  · change T.Q.deriv (P.R.field (c i))+P.R.deriv (T.Q.field (c i))=_
    simp_rw [P.Rc,T.Qc,map_zero,map_sum,map_smul,OddField.on_letter,T.Qa,add_zero]; exact P.contractsGhost i _
  · change T.Q.deriv (P.R.field (k i))+P.R.deriv (T.Q.field (k i))=_
    simp_rw [P.Rk,T.Qk,map_neg,map_sum,map_smul,OddField.on_letter,P.Ra,T.Qb,smul_neg,Finset.sum_neg_distrib, neg_neg]
    rw [add_comm]; exact P.contractsTranspose i _
  change T.Q.deriv (P.R.field (b i))+P.R.deriv (T.Q.field (b i))=_
  simp_rw [P.Rb,T.Qb,map_zero,map_sum,map_smul,OddField.on_letter,P.Rk,zero_add]; exact P.contractsGhostTranspose i _
-- scalar Stokes relation, no determinant normalization needed in this based complex
variable {F : Raw (Letters J I) ℂ} (hf : F∈ Mini (Letters J I)) (hs : MS.Koszul.Symm (parity J I) F)
local notation "W" => View P.half
include hf hs
lemma by_a (i:J) : W (a[i] ⋆ F) = ∑ j,P.N i j • W (D (a j) F) := by
  rw [ibpV (a i) P.clear P.symmetry hs hf]
  simp [P.ch, chill, a, Letters, Fintype.sum_sum_type]
lemma by_c (i:I) : W (c[i] ⋆ F) = -∑ j,P.Y i j • W (D (k j) F) := by
  rw [ibpV (c i) P.clear P.symmetry hs hf]
  simp [P.ch, chill, c, k, Letters, Fintype.sum_sum_type, Finset.sum_neg_distrib]
lemma by_k (i:J) : W (k[i] ⋆ F) = ∑ j,P.Y j i • W (D (c j) F) := by
  rw [ibpV (k i) P.clear P.symmetry hs hf]
  simp [P.ch, chill,c,k, Letters, Fintype.sum_sum_type]
lemma by_parts : W (T.Q.deriv F) = - W ((bracket J I).BV F) := by
  have A (i j:J) : D (k i) (D (a j) F) = D (a j) (D (k i) F) := by rw [hs.commute]; simp [parity,a,k]
  let g (i j:J) := W (D (k j) (D (a i) F))
  have E : (∑ i:J,∑ j:J, T.H i j • ∑ u:J,P.N j u • g u i)= ∑ i:J,∑ j:J, P.N i j • ∑ u:J,T.H j u • g i u := by
    simp_rw [Finset.smul_sum]; rw [Finset.sum_comm,Finset.sum_comm (f:=fun i j=>∑ u:J, P.N i j • (T.H j u • g i u))]; refine Finset.sum_congr rfl (fun j _=>?_); rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun u _=> ?_
    rw [P.sym,T.sym]; exact smul_comm ..
  simp only [Q_apply,lap_apply,map_add,map_sub,map_neg,map_sum,map_smul,LinearMap.sum_apply,LinearMap.neg_apply,LinearMap.smul_apply]; simp_rw [P.by_a (miD hf (k _)) (hs.drop (k _)),P.by_k (miD hf (b _)) (hs.drop (b _)),P.by_c (miD hf (a _)) (hs.drop (a _)),smul_neg, Finset.sum_neg_distrib,P.contractsGhostTranspose]; simp_rw [← A]
  change -(∑ i,∑ j,T.X i j • ∑ u:J, P.Y j u • g i u) + (-(∑ i:J,∑ j:J, T.H i j • ∑ u:J,P.N j u • g u i)+_) = -( ∑ i:J,g i i - _ )
  rw [E, neg_sub, ← add_assoc, ← neg_add, ← Finset.sum_add_distrib]; -- inspect
  simp_rw [add_comm (∑ j,T.X _ j • _) _, P.contracts]; abel

lemma wick_independent {S} (hT : T.Blocks S) (hr : Book.rank 2 S) (hs' : MS.Koszul.Symm τφ S) (he : Pure τφ false S)
    (hm : link (bracket J I).BV true τφ S S=0) (P' : Fixing T) (h : T.Q.deriv F+(bracket J I).BV F=0) :
    View P.half F=View P'.half F :=
  (hT.toFreeBV hr hs' he hm).scalar_independent P.R P.basis_contract P.half P'.half
    (fun G hu hd=> by change W (T.Q.deriv G+(bracket J I).BV G)=0; rw [map_add,P.by_parts hu hd,neg_add_cancel])
    (fun G hu hd=> by change View P'.half (T.Q.deriv G+(bracket J I).BV G)=0; rw [map_add,P'.by_parts hu hd,neg_add_cancel]) F hf hs h
end Fixing
end Kinetics
end YM.WilsonBridge.Based
