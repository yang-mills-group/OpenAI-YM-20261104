import YM.UVExt.FreeSymbol
import YM.PCalc.Band

/-!
# Full-cutoff convergence of linear stiffness

On one directed horizon, uniqueness on the periodic directions identifies
the unmasked quadratic precision. The convergence statement takes the
cutoff to infinity at a fixed level and period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG YM.Next.Free
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
private lemma dot_nonneg {ι : Type*} [Fintype ι] (x : ι→ℝ) : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

private lemma k_positive {n : Side} (H : Matrix (Body 2 n) (Body 2 n) ℝ) (h : ∀ v, 0≤v ⬝ᵥ (H *ᵥ v)) (x : Body 1 n→ℝ) :
    0 ≤ x ⬝ᵥ (K H *ᵥ x) := by unfold K; rw [Matrix.mul_assoc,← Matrix.mulVec_mulVec,dotProduct_mulVec,vecMul_transpose,←Matrix.mulVec_mulVec]; exact h _

private theorem output_unique {ι κ : Type*} [Fintype ι] [Fintype κ] {A : Matrix ι ι ℝ} {F : Matrix κ κ ℝ} {B : Matrix κ ι ℝ}
    {T : Matrix ι κ ℝ} {s : ℝ} (hs : 0<s) (hA : ∀ v,0≤ v ⬝ᵥ (A *ᵥ v))
    (H : A*T=B.transpose*F) (H' : B*T= - s • F) : F = 0 := by
  apply Matrix.mulVec_injective; funext v
  let w := T *ᵥ v
  have hh : B *ᵥ w = - s • (F *ᵥ v) := by unfold w; rw [Matrix.mulVec_mulVec,H', Matrix.smul_mulVec]
  have hk := hA w
  unfold w at hk; rw [Matrix.mulVec_mulVec,H,←Matrix.mulVec_mulVec,dotProduct_mulVec,vecMul_transpose] at hk
  rw [show (B *ᵥ (T *ᵥ v))= - s • (F *ᵥ v) from hh,smul_dotProduct,smul_eq_mul] at hk
  suffices ht : (F *ᵥ v) ⬝ᵥ (F *ᵥ v) = 0 by rw [dotProduct_self_eq_zero] at ht; rwa [zero_mulVec]
  nlinarith [dot_nonneg (F *ᵥ v)]

private lemma stiffness_unique {c f : Side} {S : StepData c f} {W Z : Matrix (Body 1 f) (Body 1 c) ℝ}
    {M U : Matrix (Body 2 f) (Body 2 f) ℝ} {M' U' : Matrix (Body 2 c) (Body 2 c) ℝ}
    (h : Inputs S W M M') (g : Inputs S Z U U') (hM : ∀ v,0≤v ⬝ᵥ (M *ᵥ v)) (he : K M=K U) : K M'=K U' := by
  obtain ⟨h,h'⟩:= h; obtain ⟨g,g'⟩:=g
  let T := mean S; apply sub_eq_zero.mp; apply output_unique (A:=K M) (inv_pos.mpr S.kernel.penalty_pos) (k_positive M hM)
    (B:=T) (T:=W-Z) (by rw [← he] at g; unfold T; rw [Matrix.mul_sub,Matrix.mul_sub,h,g])
    (by unfold T; rw [Matrix.mul_sub,h',g']; rw [show -(S.kernel.penalty⁻¹) • (K M' - K U') = _ from neg_smul _ _ |>.trans (congr_arg Neg.neg (smul_sub ..))]; abel)

variable {G : Gauge} {A : Levels G} (V : Horizon A) {Q : MapPrices} (hV : V.Suffices Q)

include hV
/-- Identification on the very same horizon with all steps and calendars fixed. -/
lemma horizon_exact {N m p : ℕ} (hm : m ≤ N) :
    K ((V.H N m).metric.acts (A.S.side m p)) = K ((record (pulse A.clock.kernel.penalty (location A N m))).acts (A.S.side m p)) := by
  let D m := V.H N m
  induction hm using Nat.decreasingInduction with
  | self =>
    have h := loc_top A N
    rw [h]
    let n := A.S.side N p
    have ht (p : Site n) := (heart_true A.clock.kernel.penalty A.clock.kernel.penalty_pos (A.clock.adm N) (Train.top _)).1.echo (mon p) (mon_mem n p)
    simp_rw [(top_metric A.clock.kernel.penalty A.clock.kernel.penalty_pos (A.clock.J N) (base_subset_realCube zone_pos (mon_mem n _))).2] at ht
    have hf := circulant n _ ((heart_true A.clock.kernel.penalty A.clock.kernel.penalty_pos (A.clock.adm N) (Train.top _)).1.safe)
    have hk : fiber (fun p : Site n => (record (pulse A.clock.kernel.penalty (Train.top (A.clock.J N)))).read (mon p))=1 := by
      ext i j; simp only [fiber,ht,of_apply,Matrix.one_apply]; by_cases h:i=j; · simp [h]
      by_cases h':i.1=j.1; · simp [h,h',show i.2≠j.2 from fun z=> h (Prod.ext h' z)]
      simp [h',h]
    have hId : (record (pulse A.clock.kernel.penalty (Train.top (A.clock.J N)))).acts n=1 := Bloch.prom_inj (cancel_rotation n _ _ (by rw [hk, Matrix.mul_one] at hf; rw [hf, show approached 1=1 from (by ext i j; by_cases h:i=j <;> simp [approached,Matrix.one_apply,h])] ; rw [Matrix.one_mul]))
    change K ((V.H N N).metric.acts n)=K ((record _).acts n)
    unfold Precision.K; simp only [Matrix.mul_assoc,(hV.all N N le_rfl n).same,hV.top,hId]
  | of_succ m hm ih =>
    let c := A.S.side m p; let f := A.S.side (m+1) p
    let n : ℕ→Side := fun i=>A.S.side i p
    let F i := location A N i; let R i := record (pulse A.clock.kernel.penalty (F i)); let k' i := K ((D i).metric.acts (n i))
    let u i := K ((R i).acts (n i)); change k' m=u m
    have hM v : 0 ≤ v ⬝ᵥ ((D (m+1)).metric.acts (n (m+1)) *ᵥ v) := le_trans (by let s:=A.clock.J (m+1); exact mul_nonneg (Q.eta_pos _).le (dot_nonneg v))
      (hV.all _ _ (by omega) _ |>.uniform.1 v|>.1)
    have hl := (hV.crossings N m p hm).trial
    let P := destination A N m
    have hP := loc_land A N m hm
    have he : f.val=c.val*P.L.val := (A.S.oneStep m p).exact_size
    have hx := Flight.tangent P A.clock.kernel (A.clock.adm m) he
    dsimp only at hx
    have hy : ∃ W, Inputs (A.clock.op m p) W ((R (m+1)).acts (n (m+1))) ((R m).acts (n m)) := by
      have h₁ : P.land=F m:=hP.symm; have hh := hx.1; rw [h₁] at hh
      exact ⟨_, hh⟩
    obtain ⟨W,hW⟩ := hy
    exact stiffness_unique hl hW hM ih

lemma horizon_limit (m p : ℕ) : Tendsto (fun N=> K ((V.H N m).metric.acts (A.S.side m p))) atTop
    (𝓝 (K ((YM.Next.Free.UV.stockInf A m (A.S.side m p) A.clock.kernel.penalty).map Complex.re))) := by
  have h := YM.Next.Free.UV.pulse_period_limit A m (A.S.side m p) A.clock.kernel.penalty_pos
  have hk : Continuous (fun H:Matrix (Body 2 (A.S.side m p)) (Body 2 (A.S.side m p)) ℝ => Precision.K H) := by unfold Precision.K; fun_prop
  refine ((hk.tendsto _).comp h).congr' ?_
  filter_upwards [eventually_ge_atTop m] with N hN;
  exact (horizon_exact V hV hN).symm

end YM.UVExt
