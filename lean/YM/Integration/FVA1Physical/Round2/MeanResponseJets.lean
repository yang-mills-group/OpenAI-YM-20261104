import YM.Integration.FVA1Physical.Round2.SparseResponseJets

/-! Ordered derivatives of the actual normalized push charged to the
conditional mean of the absolute numerator at the very field being tested. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local.Kernel
open Function Lattice Wilson RG Source MeasureTheory Next.Foundations
open scoped Classical BigOperators
variable {G : Gauge} {c f : Side} (S : StepData c f)

theorem sparse_response_mean (β : ℝ) (A : Edges c) (V : Config G c)
    {D : Config G f → ℝ} {F : Config G f → ℂ} (h : S.patch.Branches S.kernel G)
    (hD : Integrable D (prior G f)) (hF : Integrable F (prior G f)) (hp : ∀ U, 0<D U)
    {r : ℝ} (hr : 0≤r)
    (k : ℕ) (l : List (Directions G c)) (hl : l.length≤k)
    (hs : ∀ v∈l, ∀ e∉A, v e=0) (hb : ∀ v∈l, ∀ e∈A, ‖v e‖≤r) :
    ‖leftDerivs (fun U => S.push β F U / ((S.push β D U : ℝ) : ℂ)) l V‖ ≤
      responsePrice G (β*S.kernel.penalty) k A.card r *
        (S.push β (fun U => ‖F U‖) V / S.push β D V) := by
  let K := noiseFactor G (β*S.kernel.penalty) k A.card r
  let C := K^k
  have hK : 1≤K := noiseFactor_ge G (β*S.kernel.penalty) k A.card hr
  have hC : 1≤C := one_le_pow₀ hK
  let q (v : Directions G c) := (∀ e∉A, v e=0) ∧ ∀ e∈A, ‖v e‖≤r
  let Z := Complex.ofRealCLM ∘ S.push β D
  have hv (U : Config G c) : Chart k (S.push β D) U := smooth_pass S β Finset.univ h hD U k
  have hz (U : Config G c) : Chart k Z U := Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hv U)
  have pos (U : Config G c) : 0<S.push β D U := pass_pos S β Finset.univ h U hD hp
  have hnz (U : Config G c) : Z U≠0 := Complex.ofReal_ne_zero.mpr (pos U).ne'
  have hZ : ‖Z V‖ = S.push β D V := (Complex.norm_real _).trans (Real.norm_of_nonneg (pos V).le)
  have positive_mass (B : Config G f → ℝ) (hB : ∀ U, 0≤B U) :
      0≤S.push β B V := by
    change 0≤∫ U, pdf S β Finset.univ U V * B U ∂prior G f
    exact integral_nonneg fun U => mul_nonneg (pdf_pos S β Finset.univ h U V).le (hB U)
  have cost {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] {B : Config G f → T}
      (hi : Integrable B (prior G f)) (m : List (Directions G c)) (hmk : m.length≤k)
      (hmq : ∀ v∈m,q v) :
      ‖leftDerivs (S.push β B) m V‖≤C*S.push β (fun U=>‖B U‖) V := by
    have bound := sparse_push_bound S β A h V hr hi hi.norm (a:=1)
      (fun U => (one_mul ‖B U‖).symm.le) m hmk (fun v hvm=>(hmq v hvm).1)
      (fun v hvm=>(hmq v hvm).2)
    rw [mul_one] at bound
    exact bound.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK hmk)
      (positive_mass _ (fun _=>norm_nonneg _)))
  have habs : (fun U=>‖D U‖) = D := funext fun U => Real.norm_of_nonneg (hp U).le
  have inverse := inv_bound (Z:=Z) (D:=q) (V:=V) hC (le_refl k) hz hnz
    (fun v hv => ⟨fun e he => by simp [hv.1 e he], fun e he => by simpa using hv.2 e he⟩)
    (fun m hmk hm => by
      rw [hZ,show leftDerivs Z m V = _ from left_linear Complex.ofRealCLM m (hv V) hmk]
      have paid := cost hD m hmk hm
      rw [habs] at paid
      simpa using! paid)
  have hi : Chart k (fun U => (Z U)⁻¹) V := (hz V).inv (by simpa [Work.G07.at_zero_increment] using hnz V)
  have hn : Chart k (S.push β F) V := smooth_pass S β Finset.univ h hF V k
  have hq := fun v (hvl : v∈l) => And.intro (hs v hvl) (hb v hvl)
  rw [show (fun U => S.push β F U / ((S.push β D U : ℝ) : ℂ)) =
    S.push β F * (fun U => (Z U)⁻¹) from funext fun U => div_eq_mul_inv ..]
  apply (left_mul_bound hn hi (cost hF) inverse l hl hq).trans
  have hInv := (norm_nonneg _).trans (inverse [] (by simp) (by simp))
  apply (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hl)
    (mul_nonneg (mul_nonneg (zero_le_one.trans hC) (positive_mass _ (fun _=>norm_nonneg _))) hInv)).trans_eq
  rw [hZ]
  unfold responsePrice
  dsimp [C,K]
  ring
end YM.Push.Local.Kernel
