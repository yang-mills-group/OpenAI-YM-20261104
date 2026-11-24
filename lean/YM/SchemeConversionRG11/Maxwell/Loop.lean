import YM.Next.MAXWELL.Rumbles
import YM.SchemeConversionRG11.Maxwell.Arc

/-! # Puncturing the moment algebra

Concrete complex-linear constrained directional derivatives. Partial on slot k,
color i. Laws for manipulating in the family and at cap W. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Corona
open Function Filter Maxwell Maxwell.Free Set Wick
open MvPolynomial
open scoped Topology BigOperators ComplexOrder
variable {G : Gauge} {n k l j : ℕ}

def rip (D : Echo k) (i : G.ColorIndex) : Derivation ℂ (WickPol G) (WickPol G) :=
  ∑ a : Fin (legDim G k), D (flavor_pick (coordinateLeg (keyAt k a)) i) • pderiv (keyAt k a)
lemma rip_eval (D : Echo k) (i : G.ColorIndex) (p : WickPol G) : rip D i p=
    ∑ a : Fin (legDim G k), D (flavor_pick (coordinateLeg (keyAt k a)) i) • pderiv (keyAt k a) p := derivation_sum_apply ..

lemma rip_same (D : Echo k) (i : G.ColorIndex) (a : Fin (legDim G k)) : rip D i (X (keyAt k a))=
    C (D (flavor_pick (coordinateLeg (keyAt k a)) i)) := by
  rw [rip_eval,Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
  · rw [pderiv_X_self, ← C_mul',mul_one]
  intro b _ hb; rw [pderiv_X_of_ne (by simp [Ne.symm hb]),smul_zero]
lemma rip_off (D : Echo k) (i : G.ColorIndex) (a : Fin (legDim G l)) (h : l ≠ k) : rip D i (X (keyAt l a))=0 := by
  rw [rip_eval]; refine Finset.sum_eq_zero fun b _ ↦ ?_
  rw [pderiv_X_of_ne (fun h' ↦ h (congrArg Sigma.fst h')),smul_zero]
lemma sym_pick (D : Echo k) (i : G.ColorIndex) (p : Probe G k) : rip D i (symbol k p)=C (D (flavor_pick p i)) := by
  unfold symbol; rw [map_sum]
  have he := probe_expansion p
  let L : Probe G k →ₗ[ℝ] Flavor k := LinearMap.lcomp ℝ _ (fill k (unitColor G i)) -- ?
  change _ = C (D (L p))
  conv_rhs => rw [he, map_sum,map_sum,map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [C_mul',Derivation.map_smul,rip_same,map_smul,map_smul,Complex.real_smul,map_mul (C (σ:=Slot G)),C_mul']; rfl
lemma flavor_self (i : G.ColorIndex) (p : Flavor k) : flavor_pick (flavor k i p) i=p := LinearMap.ext fun u ↦ tasted p i u
lemma flavor_offcolor (p : Flavor k) {i j : G.ColorIndex} (h : j ≠ i) : flavor_pick (flavor k i p) j=0 := by
  apply LinearMap.ext; intro x
  change p (faceMap k _ _) = 0; rw [which,unitPaint]; simp [Ne.symm h]
lemma rip_letter (D : Echo k) (p : Flavor k) (i j : G.ColorIndex) : rip D i (bit p j)= if i=j then C (D p) else 0 := by
  rw [bit,sym_pick]; split_ifs with h
  · subst j; rw [flavor_self]
  rw [flavor_offcolor p h,map_zero,map_zero]
lemma rip_off_letter (D : Echo k) (p : Flavor l) (i j : G.ColorIndex) (h : l≠k) : rip D i (bit p j)=0 := by
  unfold bit symbol; rw [map_sum]; refine Finset.sum_eq_zero fun a _ ↦ ?_; rw [C_mul',Derivation.map_smul,rip_off _ _ _ h,smul_zero]
lemma rip_team (D : Echo k) (p : Flavor k) (i : G.ColorIndex) : rip D i (team G p p)=(2* D p) • bit p i := by
  simp_rw [team,map_sum,Derivation.leibniz,rip_letter]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · rw [if_pos rfl, smul_eq_mul,mul_comm,C_mul',two_mul,add_smul]
  intro j _ hj; rw [if_neg (Ne.symm hj),smul_zero,add_zero]
lemma rip_shelf (D : Echo k) (i : G.ColorIndex) (p : WickPol G) (hp : p∈ shelf G l) : rip D i p∈ shelf G l := by
  rw [rip_eval]; exact Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (shelf_var hp _)
lemma rip_none (D : Echo k) (i : G.ColorIndex) {p : WickPol G} (hp : p∈ shelf G j) (h : j<k) : rip D i p=0 := by
  rw [rip_eval]; refine Finset.sum_eq_zero fun a _ ↦ ?_
  rw [pderiv_eq_zero_of_notMem_vars _,smul_zero]
  exact fun h' ↦ h.not_ge (mem_supported.mp (show p∈Rack G j from hp) h')
lemma rip_add (D D' : Echo k) (i : G.ColorIndex) (p : WickPol G) : rip (D+D') i p=rip D i p+rip D' i p := by simp_rw [rip_eval,LinearMap.add_apply,add_smul,Finset.sum_add_distrib]
lemma rip_scale (t : ℂ) (D : Echo k) (i : G.ColorIndex) (p : WickPol G) : rip (t • D) i p=t • rip D i p := by simp_rw [rip_eval, LinearMap.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum]
lemma rips_commute (D : Echo k) (E : Echo j) (a b : G.ColorIndex) (p : WickPol G) : rip D a (rip E b p)=rip E b (rip D a p) := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [derivation_C,derivation_C,map_zero,map_zero]
  | add p q hp hq => rw [map_add,map_add,map_add,map_add,hp,hq]
  | mul_X p i hp =>
    have he {k j} (D : Echo k) (E : Echo j) (a b : G.ColorIndex) : rip D a (rip E b (X i))=0 := by
      obtain ⟨k',i⟩ := i
      by_cases ht : k'=j
      · subst k'; rw [rip_same E b i,derivation_C]
      rw [rip_off _ _ _ ht,map_zero]
    simp_rw [Derivation.leibniz, map_add,smul_eq_mul,Derivation.leibniz,hp,he]; ring

variable (C₀ : G.ColorIndex)

lemma rip_fare (r : Flavor 0) (i : G.ColorIndex) {z : E4} (hz : z ≠ 0) : rip (shoot C₀ k (paint z) r) i =
    sq (paint z)^(k+3) • singleBite k (flavor 0 i r) z := by
  classical
  apply derivation_ext
  intro a
  rcases a with ⟨j,a⟩
  rw [Derivation.smul_apply,bite_letter]; split_ifs with h
  · change j=k at h; subst j; rw [rip_same]; change MvPolynomial.C (aeval (paint z) _) = _
    rw [arrow_at C₀ _ _ z hz,← C_mul',←map_mul]; apply congr_arg MvPolynomial.C
    let P : Probe G k := coordinateLeg (keyAt k a)
    have he (P : Probe G k) : P=∑ b : G.ColorIndex, flavor k b (flavor_pick P b) := LinearMap.ext fun x ↦ by
      conv_lhs => rw [← half_sum x, map_sum]
      rw [LinearMap.sum_apply]; rfl
    change _ = _ * (↑(pairing (show z ∈ away from hz) (flavor 0 i r) P):ℂ)
    conv_rhs => rw [he P,map_sum]
    congr 2
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
    · dsimp only; apply congr_arg ((↑) : ℝ → ℂ); exact ( (any_ink C₀ r _ _ _ hz).trans (by rw [if_pos (show i=i from rfl),one_mul])).symm -- ofReal
    intro b _ hb; exact (any_ink C₀ r _ i b hz).trans (by rw [if_neg hb.symm,zero_mul])
  rw [rip_off _ _ a h,smul_zero]

end YM.SchemeConversionRG11.Corona
