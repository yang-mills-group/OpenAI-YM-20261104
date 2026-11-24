import YM.Integration.SignedMeasuredSourceSeries

/-! Native absolute price of every registered mixed source coefficient. Only the maximum numerical read of a monomial is used. The number of lattice sites and the period do not enter the rooted geometry price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedMeasuredSourceBudget
open Function Filter Finset Lattice Laurent Wilson RG Precision Exterior Tree Bloch Matrix PowerSeries
open FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Soil Stationary Work.F08
open WilsonCoeffUV.Bank.Mosaic.Near
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {V α I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [Fintype α] {r : ℕ}

omit [NormedSpace ℝ V] [CompleteSpace V] in
theorem cover (T : Ten V (Cloth α) r) {s A:ℝ} {o:Cover} (hs:0<s) (h:Cork Bank.terrain o s A T) :
    SumBudget (fun y=>‖T y‖) (A*tiePay α r s) := by
  by_cases hz:r=0
  · subst r
    refine ⟨fun x=>norm_nonneg _,summable_of_hasFiniteSupport (Set.toFinite _),?_⟩
    let z : dock Cover α 0 := Fin.elim0
    rw [tsum_eq_single z (fun y hy=>False.elim (hy (Subsingleton.elim ..))),tiePay,pow_zero,mul_one]
    exact (h.2 z).trans ((mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) (Nat.cast_nonneg _))) h.1).trans_eq (mul_one ..))
  · have hp : 0<s/r := div_pos hs (by positivity)
    apply budget_minor (cap_scale (train_pay (α:=α) hp o r) h.1) (fun _=>norm_nonneg _)
    intro y
    apply (h.2 y).trans (mul_le_mul_of_nonneg_left _ h.1)
    simpa only [sub_zero,neg_zero,zero_mul,Real.exp_zero,one_mul] using sail_cut (d:=Bank.terrain) (Nat.zero_le (tread Bank.terrain o y)) le_rfl hs (Nat.pos_of_ne_zero hz) o y (fun i=>(show Bank.terrain.gap o (y i).1≤_ from leg_le Bank.terrain (stud o y) 0 i.succ))

omit [NormedSpace ℝ V] [CompleteSpace V] in
/-- A complete absolute sum over the actual aliases pays the original cover fee once, including rank zero and repeated sites on small tori. -/
theorem periodic (T : Ten V (Cloth α) r) {s A:ℝ} {o:Cover} (hs:0<s) (h:Cork Bank.terrain o s A T) (f:Side) :
    ∑x,‖plume T f x‖≤A*tiePay α r s := by
  have hm (x) := (clothBound (n:=f) h (half_pos hs) (half_lt_self hs) x).2.1
  calc
    _≤∑x,∑'y,‖peglet T f x y‖:=sum_le_sum fun x _=>norm_tsum_le_tsum_norm (hm x)
    _=∑'y,∑x,‖peglet T f x y‖:=(Summable.tsum_finsetSum (fun x (_:x∈(univ:Finset (dock (Site f) α r)))=>hm x)).symm
    _=∑'y,‖T y‖:=tsum_congr fun y=>by
      simp only [peglet]
      rw [Finset.sum_eq_single (slideC f y)]
      · simp
      · intro x _ hx
        simp [Ne.symm hx]
      · simp
    _≤_ := (cover T hs h).2.2

variable {G : Gauge} {f : Side} {β : Type} [Fintype β]

def tariff (k n r : ℕ) (s : ℝ) (Z : Woods G f→ Ink β) (L : POL β→ₗ[ℝ]ℝ) : ℝ :=
  ∑j∈range (n+1),∑m∈range (k+j+1), ‖SignedMeasuredSourceSeries.response Z n L j m‖ *
      (flour G (steep s) r m * tiePay (Hooks G) m (steep s))

theorem leg (C : Comet G V r) {k : ℕ} (e : ℕ) (hr : r≤k+e) (hc : shadeStar C) {s : ℝ} (hs : 0<s)
    (E : V→L[ℝ]ℝ) (Z : Woods G f→ Ink β) (n : ℕ) (L : POL β→ₗ[ℝ]ℝ) :
    ‖L (coeff n (train Z (flash (ply E.toLinearMap ((volumeR C e).1 f)))))‖ ≤ integerP C s*(‖E‖*tariff k n r s Z L) := by
  let w := SignedMeasuredSourceSeries.response Z n L
  let T := volumeR C e
  have hu : 0<steep s := div_pos hs (by norm_num)
  have hI := ink_pos C (s:=s)
  have hl j m : ∑x:Fin m→ Woods G f,‖T.1 f j m x‖ ≤ integerP C s*(flour G (steep s) r m*tiePay (Hooks G) m (steep s)) := by
    rw [show T.1 f j m=plume (T.2 j m) f from aug_plane ..]
    simpa [mul_assoc] using periodic (T.2 j m) hu (volume_price C hs e j m) f
  rw [SignedMeasuredSourceSeries.value _ (ply_shell _ ((aug_auth C hc hr).span f)),tariff,Finset.mul_sum,Finset.mul_sum]
  apply (norm_sum_le ..).trans
  refine sum_le_sum fun j _=>?_
  rw [Finset.mul_sum,Finset.mul_sum]
  apply (norm_sum_le ..).trans
  refine sum_le_sum fun m _=>?_
  apply (norm_sum_le ..).trans
  calc
    _≤∑x, (‖w j m‖*‖E‖)*‖T.1 f j m x‖:=by
      apply sum_le_sum;intro x _
      rw [norm_smul,ply_v]
      exact (mul_le_mul (norm_le_pi_norm _ x) (E.le_opNorm _) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_assoc ..).symm
    _≤(‖w j m‖*‖E‖)*(integerP C s*(flour G (steep s) r m*tiePay (Hooks G) m (steep s))):=by rw [←Finset.mul_sum];exact mul_le_mul_of_nonneg_left (hl j m) (by positivity)
    _=_:=by ring

/-- The relative chart has already been evaluated on each signed Wilson insertion. The original purchaser's absolute charge bounds all original Riesz paths together with the full true forest polynomial read. -/
theorem measured {c : Side} (S : StepData c f) (F : Forest S.ratio) (M : Matrix (Woods G f) (Woods G c) ℝ)
    (ρ : fieldDir G c 1→ AxisChart G F) (hM : M=reveal G S F*((reveal G S F).transpose*M)) (hρ : ContDiffAt ℝ ω ρ 0) (h0 : ρ 0=0)
    (T : I→ Comet G V r) {s A : ℝ} {k : ℕ} (hs:0<s) (hp:SumBudget (fun i=>integerP (T i) s) A) (hT:∀i,shadeStar (T i))
    (e b t : ℕ) (hr:r≤k+e) (ht:b+e=r+t) (E:V→L[ℝ]ℝ) (n:ℕ) (L:POL (Active G F⊕Woods G c)→ₗ[ℝ]ℝ) :
    let Z := fun v=>SignedMeasuredSourceSeries.probe S F M ρ (path v)
    SumBudget (fun i=>‖L (coeff (b+n) ((X:Ink (Active G F⊕Woods G c))^t * jet (fun x:Sloc S F G=>
      (dip (T i) E).unmasked (Work.F03.live F (SignedMarkedChartGerm.chart S F ρ x)) 0)))‖)
      ((‖E‖*tariff k n r s Z L)*A) := by
  intro Z
  have htie (m : ℕ) : 0≤tiePay (Hooks G) m (steep s) := by
    by_cases h : m=0
    · subst m
      simp [tiePay]
    · have hm : 0<(m:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)
      have hu : 0<steep s := div_pos hs (by norm_num)
      exact pow_nonneg (boardPay_nn (div_pos hu hm)) m
  have hfee : 0≤tariff k n r s Z L := sum_nonneg fun j _=>sum_nonneg fun m _=>mul_nonneg (norm_nonneg _) (mul_nonneg (flour_nn ..) (htie m))
  apply budget_minor (cap_scale hp (mul_nonneg (norm_nonneg E) hfee)) (fun i=>norm_nonneg _)
  intro i
  rw [←SignedMarkedChartGerm.cleared S F M ρ (T i) E e b t ht hM hρ h0,coeff_X_pow_mul',if_pos (Nat.le_add_right b n),Nat.add_sub_cancel_left]
  change ‖L (coeff n (SignedMeasuredSourceSeries.probe S F M ρ _))‖≤_
  rw [SignedMeasuredSourceSeries.genuine,mul_comm]
  exact leg (T i) e hr (hT i) hs E Z n L

end YM.Integration.SignedMeasuredSourceBudget
