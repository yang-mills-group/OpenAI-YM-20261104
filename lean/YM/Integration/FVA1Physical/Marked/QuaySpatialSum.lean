import YM.Integration.FVA1Physical.Marked.QuaySpatial

/-! All native coordinate words can be summed without a torus-size cost.
Polynomial support weights can be chosen after the source family. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Function Filter Finset Lattice RG YM.Wilson Tree Precision Source Labels Extra.Histories Marker
open LocalLTE.Sail PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Org RG.Supply
open MergeProof.Accent Bandage.Harmonics Next.Foundations PhysicalNext.Repeat.Legato.Round2
open PhysicalNext.Repeat.Roost YM.Integration.FVA1Physical.Round2 YM.Integration.FVA1Physical.Round2.Quay
open RGComparison.Core16.Lam RGComparison.Core16.Catkin Push.Uniform
open scoped Classical BigOperators Topology
variable {G : Gauge} {n : Side}

theorem word_kernel_sum (o : Site n) (q : ℕ) {α : ℝ} (ha : 0 < α) :
    ∑ f : Fin q → Operand G n,Real.exp (-α*wordRadius o (List.ofFn f)) ≤
        (4*Fintype.card G.ColorIndex*countCost α)^q := by
  have one : (∑ x : Operand G n, Decay α o (crest x)) ≤ 4*(Fintype.card G.ColorIndex:ℝ)*countCost α := by
    change (∑ x : (Site n × Axis) × G.ColorIndex, Decay α o x.1.1) ≤ _
    simp only [Fintype.sum_prod_type,sum_const,card_univ,nsmul_eq_mul]
    rw [←mul_sum,←mul_sum]
    have hh : Fintype.card Axis=4 := by decide
    rw [hh]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (decay_count ha o) (Nat.cast_nonneg _))
      (show 0≤(4:ℝ) by norm_num) |>.trans_eq (by ring)
  have prod (f : Fin q → Operand G n) :
      Real.exp (-α*wordRadius o (List.ofFn f))=∏ j,Decay α o (crest (f j)) := by
    unfold wordRadius Decay
    rw [List.map_ofFn,List.sum_ofFn,Nat.cast_sum,mul_sum,Real.exp_sum]; rfl
  simp_rw [prod]
  rw [←Fintype.prod_sum (fun (_ : Fin q) (x : Operand G n)=>Decay α o (crest x)),prod_const,card_univ,Fintype.card_fin]
  exact pow_le_pow_left₀ (sum_nonneg fun i _=>(decay_pos ..).le) one q

private theorem poly_exponential (x : ℝ) (hx : 0 ≤ x) {α : ℝ} (ha : 0 < α) (s : ℕ) :
    (1+x)^s ≤ (1+α⁻¹)^s * Real.exp ((s:ℝ)*(α*x)) := by
  have h₁ : 1 ≤ Real.exp (α*x) := Real.one_le_exp (mul_nonneg ha.le hx)
  have ex : α*x ≤ Real.exp (α*x) := by linarith only [Real.add_one_le_exp (α*x)]
  have h₂ : x ≤ α⁻¹*Real.exp (α*x) := by
    calc x = α⁻¹*(α*x) := by rw [←mul_assoc,inv_mul_cancel₀ ha.ne',one_mul]
         _ ≤ _ := mul_le_mul_of_nonneg_left ex (inv_nonneg.mpr ha.le)
  have bound : 1+x ≤ (1+α⁻¹)*Real.exp (α*x) := (add_le_add h₁ h₂).trans_eq (by ring)
  rw [Real.exp_nat_mul,←mul_pow]
  exact pow_le_pow_left₀ (by linarith) bound s

/-- Convert a family of exact pointwise word estimates to a complete spatial
sum through a polynomial observation norm of any fixed order. -/
theorem polynomial_word_sum (o : Site n) (q s : ℕ) (Y : (Fin q → Operand G n) → ℝ) {A α : ℝ}
    (ha : 0 < α) (cost : 0 ≤ A) (yn : ∀ f,0 ≤ Y f)
    (paid : ∀ f,Real.exp (((s:ℝ)+1)*α*wordRadius o (List.ofFn f))*Y f ≤ A) :
    (∑ f : Fin q → Operand G n,(1+(wordRadius o (List.ofFn f):ℝ))^s*Y f) ≤
      (1+α⁻¹)^s*(4*Fintype.card G.ColorIndex*countCost α)^q*A := by
  let Z:= (1+α⁻¹)^s
  have zpos : 0 ≤ Z := pow_nonneg (add_nonneg zero_le_one (inv_nonneg.mpr ha.le)) _
  have term (f : Fin q → Operand G n) :
      (1+(wordRadius o (List.ofFn f):ℝ))^s*Y f ≤ Z*Real.exp (-α*wordRadius o (List.ofFn f))*A := by
    let x:ℝ:=wordRadius o (List.ofFn f)
    have hx : 0 ≤ x := Nat.cast_nonneg _
    have heq : Real.exp ((s:ℝ)*(α*x)) = Real.exp (-α*x)*Real.exp (((s:ℝ)+1)*α*x) := by
      rw [←Real.exp_add]; congr 1; ring
    apply (mul_le_mul_of_nonneg_right (poly_exponential x hx ha s) (yn f)).trans
    rw [heq]
    calc _ = Z*Real.exp (-α*x)*(Real.exp (((s:ℝ)+1)*α*x)*Y f) := by unfold Z;ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (paid f) (mul_nonneg zpos (Real.exp_pos _).le)
  apply (sum_le_sum (fun f _=>term f)).trans
  rw [←sum_mul,←mul_sum]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (word_kernel_sum o q ha) zpos) cost

variable {X : Metals G} {D : Rolls X.p} {A : Alloy X D} {P : Bolt A} {R : Factor A}
    {ref : ℕ → ℕ} {fields : ∀ d N n,TransferData ((frames G).level d) (Issue.trail P) N n} {p d c : ℕ}

theorem physical_centered_spatial (books : PhysicalBooks R P ref fields p d c)
    {N n m : ℕ} (hm : m < N) (start : ref 0 ≤ m) {I : Type} [Fintype I] [DecidableEq I]
    (B : Census I) (h : I → ℕ) (v : ∀ j, ((frames G).level (h j)).Coeff)
    (paths : ∀ i : ℕ,LocalLTE.FrameBox.Grove (0:Site (A.B.a.S.side i n)))
    (card : Fintype.card I ≤ c) (grade : ∀ j,h j ≤ d) (fits : ∀ j,ref (h j) ≤ m)
    (test : ∀ j,((frames G).level (h j)).coeffSize (v j) ≤ 1)
    (t : B.Mode) {i : ℕ} (lo : m ≤ i) (hi : i < N)
    (q s : ℕ) (nq : 0 < q) {α : ℝ} (pos : 0 < α) (U : Config G ((Issue.trail P).S.side i n)) :
    let M:=((Issue.trail P).rep N n i).p
    q ≤ M.order → ((s:ℝ)+1)*α*q*(6*M.B+2:ℝ) ≤ M.supportExponent → U ∈ Boulevard.sunny M →
      (∑ f : Fin q → Operand G ((Issue.trail P).S.side i n),(1+(wordRadius 0 (List.ofFn f):ℝ))^s *
        ‖leftDerivs (fun V=>(momentTable B (centeredBatch P N n h v) i hi.le V).part t) ((List.ofFn f).map compass) U‖) ≤
      (1+α⁻¹)^s*(4*Fintype.card G.ColorIndex*countCost α)^q*((M.threshold⁻¹)^q*(1/2:ℝ)^(N-(i+1))) := by
  intro M length room hu
  apply polynomial_word_sum 0 q s _ pos (mul_nonneg (pow_nonneg (inv_nonneg.mpr M.threshold_pos.le) _)
    (pow_nonneg (by norm_num) _)) (fun _=>norm_nonneg _)
  intro f
  have ne : List.ofFn f ≠ [] := by intro eq; have en:=congrArg List.length eq; simp only [List.length_ofFn,List.length_nil] at en; omega
  simpa only [List.length_ofFn] using physical_centered_derivative books hm start B h v paths card grade fits test t lo hi (List.ofFn f) ne
    (α:=((s:ℝ)+1)*α) (mul_nonneg (by positivity) pos.le) U (by simpa using length) (by simpa using room) hu
end YM.Integration.FVA1Physical.Marked
