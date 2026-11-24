import YM.Integration.WilsonCenteredNestedLoggedRow

/-! The complete measured finite grade/shape census is financed by the
existing matrix ticket, before the independent perturbative order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedGross
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Atom OPE.Nesting.Tree
open OPE.Nesting.Composite OPE.Log Filter Extraction Table Spec
open WilsonCenteredNestedLoggedRow WilsonCenteredNestedProgram WilsonCenteredNestedIntake
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def wage (k : ℕ) (B r : ℝ) := B * shell r^k

theorem wage_le {k j : ℕ} {B C r : ℝ} (kj : k ≤ j) (Bn : 0 ≤ B) (BC : B ≤ C) :
    wage k B r ≤ wage j C r :=
  mul_le_mul BC (pow_le_pow_right₀ (shell_one r) kj)
    (pow_nonneg (zero_le_one.trans (shell_one r)) _) (Bn.trans BC)

theorem pool {I : Type*} [Fintype I] (P : I→ℕ→ℝ→Prop)
    (up : ∀i k B j C,k ≤ j → 0 ≤ B → B ≤ C → P i k B → P i j C)
    (source : ∀i,∃k B,0 ≤ B ∧ P i k B) : ∃k B,0 ≤ B ∧ ∀i,P i k B := by
  choose k B positive issue using source
  refine ⟨∑ i,k i,∑ i,B i,Finset.sum_nonneg (fun i _=>positive i),fun i=>?_⟩
  exact up i (k i) (B i) _ _ (Finset.single_le_sum (f:=k) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i))
    (positive i) (Finset.single_le_sum (f:=B) (fun j _=>positive j) (Finset.mem_univ i)) (issue i)

theorem widen (A : Rule F Q) (g L M E : ℝ→ℝ) {rad eta : ℝ} (t : Tree)
    (v : t.Leaf→S.Tag) (D : t.Inner→ℕ) (H : ℕ)
    (more : ∀ r,0 < r → L r ≤ M r) (rate : ∀ r,0 ≤ E r)
    (source : localRows F Q A g L E rad eta t v D H) :
    localRows F Q A g M E rad eta t v D H := by
  induction t generalizing H with
  | bud => trivial
  | fork n p ih =>
    constructor
    · intro j k c
      filter_upwards [source.1 j k c,(show ∀ᶠ r:ℝ in 𝓝[>]0,0<r from self_mem_nhdsWithin)] with r row rp x o close apart
      obtain ⟨left,right,change⟩ := row x o close apart
      have grow : L r * (r^k.val / ∏i,r^(echoTags F Q v j i).1) ≤ M r * (r^k.val / ∏i,r^(echoTags F Q v j i).1) :=
        mul_le_mul_of_nonneg_right (more r rp)
        (div_nonneg (pow_nonneg rp.le k.val) (Finset.prod_nonneg
          (fun i _=>pow_nonneg rp.le (echoTags F Q v j i).1)))
      exact ⟨left.trans grow,right.trans grow,change.trans (mul_le_mul_of_nonneg_right grow (rate r))⟩
    · exact fun i=>ih i _ _ _ (source.2 i)

/-- Fix one logarithmic exponent before any order-dependent signed
comparison, for all measurable rows of this tree and all its root grades. -/
theorem original (fac : Services C f S) (log : SingleLog F Q.port) (g : ℝ→ℝ)
    {M η : ℝ} (Mn : 0 ≤ M) (ηp : 0 < η) (t : Tree) (v : t.Leaf→S.Tag)
    (D : t.Inner→ℕ) (H : ℕ) :
    ∃ k B,0 ≤ B ∧ localRows F Q (measured F Q) g (wage k B) (fun _=>0) M η t v D H := by
  induction t generalizing H with
  | bud => exact ⟨0,0,le_refl _,trivial⟩
  | fork n p ih =>
    let T := Σ _ : Branches F Q (f:=p) (rollCaps D),Σ m : Fin (H+1),Q.channels m
    let lane (u : T) (k : ℕ) (B : ℝ) := ∀ᶠ r:ℝ in 𝓝[>]0,∀ (x : Fin n→E4) (o : E4),
      (∀ i,‖x i-o‖ ≤ M*r) → (∀ i j,i ≠ j → η*r ≤ ‖x i-x j‖) →
      ‖express Q u.2.1 u.2.2 x (echoTags F Q v u.1) o‖ ≤
        wage k B r * (r^u.2.1.val / ∏ i,r^(echoTags F Q v u.1 i).1)
    have enlarge (u : T) (k : ℕ) (B : ℝ) (j : ℕ) (C : ℝ)
        (kj : k ≤ j) (Bn : 0 ≤ B) (BC : B ≤ C) (src : lane u k B) : lane u j C := by
      filter_upwards [src,(show ∀ᶠ r:ℝ in 𝓝[>]0,0<r from self_mem_nhdsWithin)] with r row rp x o close clear
      exact (row x o close clear).trans (mul_le_mul_of_nonneg_right (wage_le kj Bn BC)
        (div_nonneg (pow_nonneg rp.le _) (Finset.prod_nonneg (fun i _=>pow_nonneg rp.le _))))
    obtain ⟨k0,B0,b0,heads⟩ := pool lane enlarge (fun u=> WilsonCenteredNestedLoggedRow.original F Q fac log
      (echoTags F Q v u.1) u.2.1 u.2.2 Mn ηp)
    let child (i : Fin n) (k : ℕ) (B : ℝ) := localRows F Q (measured F Q) g (wage k B) (fun _=>0)
      M η (p i) (childWages i v) (childAge i D) (rollCaps D i)
    have shelter (i : Fin n) (k : ℕ) (B : ℝ) (j : ℕ) (C : ℝ)
        (kj : k ≤ j) (Bn : 0 ≤ B) (BC : B ≤ C) (prev : child i k B) : child i j C :=
      widen F Q _ g _ _ _ _ _ _ _ (fun _ _=>wage_le kj Bn BC) (fun _=>le_refl _) prev
    obtain ⟨k1,B1,b1,children⟩ := pool child shelter (fun i=>ih i _ _ _)
    have b0' : B0 ≤ B0+B1 := le_add_of_nonneg_right b1
    have b1' : B1 ≤ B0+B1 := le_add_of_nonneg_left b0
    refine ⟨k0+k1,B0+B1,add_nonneg b0 b1,?_,?_⟩
    · intro j m c
      have paid := enlarge ⟨j,m,c⟩ k0 B0 (k0+k1) (B0+B1) (Nat.le_add_right ..) b0 b0' (heads _)
      filter_upwards [paid] with r src x o close apart
      have eqv := src x o close apart
      exact ⟨eqv,eqv,by simp [measured]⟩
    · exact fun i=>shelter i k1 B1 (k0+k1) (B0+B1) (Nat.le_add_left ..) b1 b1' (children i)

end YM.Integration.WilsonCenteredNestedGross
