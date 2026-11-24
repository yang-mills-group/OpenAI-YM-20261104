import YangMills.WilsonProof.NativeSupport.CalibratedPacking
import YangMills.WilsonProof.NativeSupport.PacketPrice

/-! Native cover size pays for all occupied packets when a connected
coefficient reaches two of the separated translates of the planted word. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Finset Lattice RG
open scoped BigOperators Classical
variable {V H : Type} [Fintype V] [DecidableEq V] [DecidableEq H] {n : Side}

omit [Fintype V] [DecidableEq V] in
private theorem selected_cover (g : V → H) (o : V → Site n) (distinct : Injective o)
    (T : Finset V) (X : Support n) (M L : ℕ) (pos : 0<L)
    (inside : T.image o⊆X) (many : 2 ≤ (T.image g).card)
    (apart : ∀ i j,g i≠g j  →  2*M+4*(2*M+1)*L<separation (o i) (o j)) :
    (T.image g).card*L  ≤  coverNumber M X := by
  let B:=T.image g
  have pick (b : B) : ∃ i∈T,g i=b.val := mem_image.mp b.property
  choose v member group using pick
  let site (b : B) := o (v b)
  have unique : Injective site := by
    intro b b' eq
    have ev : v b=v b' := distinct eq
    exact Subtype.ext ((group b).symm.trans ((congrArg g ev).trans (group b')))
  let A:Finset (Site n):=univ.image site
  have size : A.card=B.card := (card_image_of_injective _ unique).trans (by simp)
  have covered : A⊆X := by
    intro j hj
    obtain ⟨i,_,rfl⟩:=mem_image.mp hj
    exact inside (mem_image_of_mem o (member i))
  have far (x) (hx : x∈A) (y) (hy : y∈A) (ne : x≠y) :
      2*M+4*(2*M+1)*L<separation x y := by
    obtain ⟨i,_,rfl⟩:=mem_image.mp hx
    obtain ⟨j,_,rfl⟩:=mem_image.mp hy
    apply apart
    intro eq
    exact ne (congrArg site (Subtype.ext ((group i).symm.trans (eq.trans (group j)))))
  rw [← show A.card=(T.image g).card from size]
  exact separated_cover M L pos X A covered (size.symm ▸ many) far

omit [DecidableEq V] in
theorem mode_payment (g : V → H) (o : V → Site n) (distinct : Injective o) (m M L : ℕ)
    (fibres : ∀ j,(fibre g j).card ≤ m)
    (apart : ∀ i j,g i≠g j  →  2*M+4*(2*M+1)*L<separation (o i) (o j))
    (pos : 0<L) {A D ρ a : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (radius : Real.exp (-A) ≤ ρ) (exponent : 1 ≤ a) (paid : m*A+D ≤ L)
    (T : Finset V) (X : Support n) (inside : T.image o⊆X) (many : 2 ≤ (T.image g).card) :
    1 ≤ Real.exp (-2*D)*(ρ^T.card*Real.exp (a*coverNumber M X)) := by
  let b:ℕ:=(T.image g).card
  let v:ℕ:=coverNumber M X
  have cover : b*L ≤ v := selected_cover g o distinct T X M L pos inside many apart
  have size : T.card ≤ b*m := by
    calc
      T.card = ∑ j∈T.image g,(T.filter (fun i=>g i=j)).card := card_eq_sum_card_image g T
      _  ≤  ∑ _j∈T.image g,m := sum_le_sum fun j _ =>
        (card_le_card (fun i hi => show i∈fibre g j from mem_filter.mpr ⟨mem_univ i,(mem_filter.mp hi).2⟩)).trans (fibres j)
      _ = _ := by simp [b]
  have c : (b:ℝ)*L ≤ v := by exact_mod_cast cover
  have s : (T.card:ℝ) ≤ (b:ℝ)*m := by exact_mod_cast size
  have two : (2:ℝ) ≤ b := by exact_mod_cast many
  have scale := mul_le_mul_of_nonneg_left paid (Nat.cast_nonneg b)
  have bulk := mul_le_mul_of_nonneg_right s hA
  have small := mul_le_mul_of_nonneg_right two hD
  have localPrice := mul_le_mul_of_nonneg_right exponent (Nat.cast_nonneg (α:=ℝ) v)
  have nonneg : 0 ≤  -2*D+T.card*(-A)+a*v := by nlinarith only [c,scale,bulk,small,localPrice]
  have power := pow_le_pow_left₀ (Real.exp_pos (-A)).le radius T.card
  calc
    (1:ℝ)  ≤  Real.exp (-2*D+T.card*(-A)+a*v) := Real.one_le_exp_iff.mpr nonneg
    _ = Real.exp (-2*D)*(Real.exp (-A)^T.card*Real.exp (a*v)) := by
      rw [Real.exp_add,Real.exp_add,Real.exp_nat_mul,mul_assoc]
    _  ≤  _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right power (Real.exp_pos _).le) (Real.exp_pos _).le

end YM.Integration.InletSusceptibility.Packet
