import YM.Integration.FVA1Physical.Round2.SparseKernelJets
import YM.Push.LOCAL_SPLITTING.Response

/-! Ordered derivatives of an actual normalized coarse readout, priced
by the support of the varying directions. Both integrals use the original
full kernel and the same fine vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local.Kernel
open Function Lattice Wilson RG Source MeasureTheory Next.Foundations
open scoped Classical BigOperators
variable {G : Gauge} {c f : Side} (S : StepData c f)

theorem sparse_response_jets (β : ℝ) (A : Edges c) (V : Config G c)
    {D : Config G f → ℝ} {F : Config G f → ℂ} (h : S.patch.Branches S.kernel G)
    (hD : Integrable D (prior G f)) (hF : Integrable F (prior G f)) (hp : ∀ U, 0<D U)
    {r a : ℝ} (hr : 0≤r) (ha : ∀ U, ‖F U‖≤a*D U)
    (k : ℕ) (l : List (Directions G c)) (hl : l.length≤k)
    (hs : ∀ v∈l, ∀ e∉A, v e=0) (hb : ∀ v∈l, ∀ e∈A, ‖v e‖≤r) :
    ‖leftDerivs (fun U => S.push β F U / ((S.push β D U : ℝ) : ℂ)) l V‖ ≤
      responsePrice G (β*S.kernel.penalty) k A.card r * a := by
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
  have cost {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] {B : Config G f → T}
      {w : ℝ} (hi : Integrable B (prior G f)) (hm : ∀ U, ‖B U‖≤w*D U)
      (m : List (Directions G c)) (hmk : m.length≤k) (hmq : ∀ v∈m,q v) :
      ‖leftDerivs (S.push β B) m V‖≤(C*w)*S.push β D V := by
    have hw : 0≤w := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hm 1)) (hp _)
    exact (sparse_push_bound S β A h V hr hi hD hm m hmk (fun v hvm=>(hmq v hvm).1)
      (fun v hvm=>(hmq v hvm).2)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK hmk) hw) (pos V).le)
  have inverse := inv_bound (Z:=Z) (D:=q) (V:=V) hC (le_refl k) hz hnz
    (fun v hv => ⟨fun e he => by simp [hv.1 e he], fun e he => by simpa using hv.2 e he⟩)
    (fun m hmk hm => by
      rw [hZ,show leftDerivs Z m V = _ from left_linear Complex.ofRealCLM m (hv V) hmk]
      simpa using! cost hD (w:=1) (fun U => by rw [Real.norm_of_nonneg (hp _).le,one_mul]) m hmk hm)
  have hi : Chart k (fun U => (Z U)⁻¹) V := (hz V).inv (by simpa [Work.G07.at_zero_increment] using hnz V)
  have hn : Chart k (S.push β F) V := smooth_pass S β Finset.univ h hF V k
  have hq := fun v (hvl : v∈l) => And.intro (hs v hvl) (hb v hvl)
  rw [show (fun U => S.push β F U / ((S.push β D U : ℝ) : ℂ)) =
    S.push β F * (fun U => (Z U)⁻¹) from funext fun U => div_eq_mul_inv ..]
  apply (left_mul_bound hn hi (cost hF ha) inverse l hl hq).trans
  have hInv := (norm_nonneg _).trans (inverse [] (by simp) (by simp))
  have hw : 0≤a := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (ha 1)) (hp _)
  apply (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hl)
    (mul_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans hC) hw) (pos V).le) hInv)).trans_eq
  rw [hZ]
  unfold responsePrice
  dsimp [C,K]
  field_simp [(pos V).ne']
end YM.Push.Local.Kernel
