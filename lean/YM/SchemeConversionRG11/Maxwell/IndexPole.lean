import YM.SchemeConversionRG11.Maxwell.Slope

/-! # Use bi-residue from an ordinary separated kernel family, off coincidence -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Corona
open Function Filter Maxwell Maxwell.Free Set Tensor
open MvPolynomial hiding C coeff
open scoped Topology BigOperators ComplexOrder
variable {G : Gauge} {n k l : ℕ} {a y : Fin n}

def poles (x : Points n) : Fin n → Space := fun i ↦ paint (x i)
lemma disperses {x : Points n} (h : x ∈ conf _) : Dispersed (poles x) := fun i j hij ↦ by
  unfold poles; rw [←paint_sub]; exact paint_separate (sub_ne_zero.mpr ((show Injective x.ofLp from h).ne hij))
lemma avoided (x : Points n) : ∃ b:E4, ∀ i,b≠x i := by
  obtain ⟨b,h⟩ := (finite_range x.ofLp).exists_notMem
  exact ⟨b,fun i hi ↦ h ⟨i,hi.symm⟩⟩
lemma iced {p : Script} (x : Points n) (h : ∀ b : E4,(∀ i, b≠x i) → aeval (paint b) p=0) : p=0 := by
  obtain ⟨b,hb⟩ := avoided x
  apply eqOpen (x₀:=b)
  have he (i) : ∀ᶠ z in 𝓝 b, z≠x i := isOpen_compl_singleton.mem_nhds (show b∈({x i}:Set E4)ᶜ from hb i)
  filter_upwards [eventually_all.mpr he] with z hz; rw [h _ hz,map_zero]

lemma bi_read {ι : Type*} (B : Finset ι) (P : ι → Script) (L : ι → Fin n → ℕ) {x : Points n} (d : Space)
    (hp : x ∈ conf _) (hx : Blip (poles x) a y d) (ha : a≠y) (K T : ℕ)
    (h : ∀ i∈B,P i=0 ∨ L i a<K ∨ L i y<T ∨ L i a=K ∧ L i y=T)
    (he : ∀ b:E4,(∀ i,b ≠ x i) → ∑ i∈B, aeval (paint b) (P i)/aeval (paint b) (DD (poles x) (L i))=0) :
    ∑ i∈B, (if L i a=K ∧ L i y=T then aeval (d+poles x a) (P i)/aeval (d+poles x a) (extDD (poles x) (L i) a y) else 0)=0 := by
  classical
  let M j := B.sup (fun i ↦ L i j)+K+T
  let u := poles x
  have hl i (hi : i ∈ B) : L i ≤ M := fun j ↦ by have he := Finset.le_sup (f:=fun i ↦ L i j) hi; dsimp [M]; omega
  let D i := DD u (M-L i)
  have ht : (∑ i∈B,D i*P i)=0 := by
    apply iced x; intro b hb
    calc
      aeval (paint b) _ = ∑ i∈B, aeval (paint b) (D i*P i) := map_sum ..
      _ = ∑ i∈B, aeval (paint b) (DD u M)*(aeval (paint b) (P i)/aeval (paint b) (DD u (L i))) := by
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [map_mul]
        have hm : M=L i+(M-L i) := funext fun j ↦ (add_tsub_cancel_of_le (hl i hi j)).symm
        conv_rhs => rw [hm,DD_add,map_mul]
        have hn : aeval (paint b) (DD u (L i))≠0 := DD_ne _ _ _ (fun j ↦ by unfold u poles; rw [←paint_sub]; exact paint_separate (sub_ne_zero.mpr (hb _)))
        unfold D; field_simp
      _ = 0 := by rw [← Finset.mul_sum,he _ hb,mul_zero]
  let N := pick (M a-K) (M y-T)
  let f := fling u d a y
  let c := jumble u d a y
  let R := c^(M a-K)*c^(M y-T)*aeval (d+u a) (extDD u M a y)
  have hc : c≠0 := mul_ne_zero (by norm_num) (hx.sharp (disperses hp) (Ne.symm ha))
  have hr : R≠0 := mul_ne_zero (mul_ne_zero (pow_ne_zero _ hc) (pow_ne_zero _ hc)) (ext_ne u M d hx)
  apply mul_left_cancel₀ hr
  rw [mul_zero, Finset.mul_sum]
  conv_rhs => rw [← show MvPolynomial.coeff N (f (∑ i∈B,D i*P i))=0 from by rw [ht,map_zero,MvPolynomial.coeff_zero], map_sum,MvPolynomial.coeff_sum]
  exact Finset.sum_congr rfl fun i hi ↦ (radiates u d hx ha K T (M:=M) (by unfold M; omega) (by unfold M; omega) (hl i hi) _ (h i hi)).symm
end YM.SchemeConversionRG11.Corona
