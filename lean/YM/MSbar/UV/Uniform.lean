import YM.MSbar.UV.Schedule
/-! Uniform temperate growth on an expanding chart. smoothness separately in log scale.
Apply this price on all *linear* momentum plots, preserving the independent derivative cost of any demand.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.High
open Function Filter Set Metric Asymptotics
open scoped Topology BigOperators Classical ContDiff
variable {ι X Y Z:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y]
  [NormedAddCommGroup Z][NormedSpace ℝ Z]
variable {B:Book ι}{P Q:Damping ι}{u v:ι→X→Y}{f g:ι→X→ℂ}
structure Stamp (B:Book ι)(P:Damping ι)(f:ι→X→Y):Prop where
    qualify : ∀ i ∈ B.using_, ContDiff ℝ ∞ (f i)
    known : ∀ n:ℕ, Allows B P fun i x=> ‖iteratedFDeriv ℝ n (f i) x‖
namespace Stamp
lemma tame (B: Book ι){F:X→Y}(h:F.HasTemperateGrowth): Stamp B 0 (fun _=>F):=by
    refine ⟨fun _ _=> h.1,fun n=>?_⟩; obtain ⟨k,c,hc,H⟩:= h.norm_iteratedFDeriv_le_uniform n; refine ⟨c,k,hc,fun i hi x=>?_⟩; apply (H n le_rfl x).trans; simp only [Pi.zero_apply,Real.exp_zero,one_mul,price]; unfold Credit; gcongr; exact le_mul_of_one_le_left (by positivity) (B.right i)
lemma zero (B:Book ι)(P:Damping ι): Stamp B P (0:ι→ X → Y):=by
    refine ⟨fun i _=>contDiff_const,fun n=> (Allows.zero B P).adjust fun i hi x=>?_⟩; cases n <;> simp
lemma agrees (h:Stamp B P u)(H:EqOn v u B.using_): Stamp B P v:=⟨fun i hi=> H hi ▸ h.qualify i hi,fun n=>(h.known n).adjust (fun i hi _=>by simp [H hi])⟩
lemma budget (h:Stamp B P u)(he:∀ i∈B.using_,P i≤Q i): Stamp B Q u:=⟨h.qualify,fun n=>(h.known n).weaken he⟩
lemma see (h:Stamp B P u) {i:ι}(hi:i∈B.using_): HasTemperateGrowth (u i):=by
    constructor; exact h.qualify i hi; intro n; obtain ⟨c,r,hC,H⟩:=h.known n; refine ⟨r,Real.exp (P i)*c*B.fee i^r,fun x=>?_⟩; refine le_trans (H i hi x) (le_of_eq ?_); unfold price Credit; rw [mul_pow]; ring
lemma bare (h:Stamp B P u) : Allows B P (fun i x=> ‖u i x‖):=by simpa using h.known 0
lemma add (x:Stamp B P u)(y:Stamp B P v): Stamp B P (u+v):=by
    refine ⟨fun i hi=>(x.qualify i hi).add (y.qualify i hi), fun n=> (x.known n).combine (y.known n) (fun i hi f=>?_)⟩
    dsimp only [Pi.add_apply]; rw [iteratedFDeriv_add_apply ((x.qualify i hi).of_le (by exact_mod_cast le_top)|>.contDiffAt) ((y.qualify i hi).of_le (by exact_mod_cast le_top)|>.contDiffAt)]; apply norm_add_le
lemma neg (h:Stamp B P u): Stamp B P (-u):=by refine ⟨fun i hi=> (h.qualify i hi).neg, fun n=> (h.known n).adjust ?_⟩; intro i hi x; dsimp only [Pi.neg_apply]; rw [iteratedFDeriv_neg_apply,norm_neg]
lemma sub (x:Stamp B P u)(y:Stamp B P v): Stamp B P (u-v) := by rw [sub_eq_add_neg]; exact x.add y.neg
lemma times {𝕜:Type}[NontriviallyNormedField 𝕜][NormedSpace 𝕜 Y][SMulCommClass ℝ 𝕜 Y](x:Stamp B P u)(c:𝕜) : Stamp B P (c•u):=by
    refine ⟨fun i hi=> (x.qualify i hi).const_smul c, fun n=> ((x.known n).scale ‖c‖ (by positivity)).adjust (fun i hi y=> ?_)⟩
    dsimp only [Pi.smul_apply]; rw [ iteratedFDeriv_const_smul_apply ((x.qualify i hi).of_le (by exact_mod_cast le_top)|>.contDiffAt),norm_smul]
lemma sum {ι':Type*}(I:Finset ι'){F:ι'→ι→X→Y}(h:∀ i∈I,Stamp B P (F i)):Stamp B P (∑ i∈I,F i):=by induction I using Finset.induction_on with|empty=> simp only [Finset.sum_empty]; exact zero ..|insert i s h' ih=>rw [Finset.sum_insert h']; exact (h _ (Finset.mem_insert_self ..)).add (ih fun j hj=> h _ (Finset.mem_insert_of_mem hj))
-- product
lemma mul (x:Stamp B P f)(y:Stamp B Q g): Stamp B (P+Q) (f*g):=by
    refine ⟨fun i hi=> (x.qualify i hi).mul (y.qualify i hi),?_⟩; intro n
    let F := fun (j:ℕ) (i:ι)(a:X)=> (n.choose j:ℝ)*‖iteratedFDeriv ℝ j (f i) a‖*‖iteratedFDeriv ℝ (n-j) (g i) a‖
    refine (Allows.sum (Finset.range (n+1)) F (fun j _=> Allows.times ((x.known j).scale _ (Nat.cast_nonneg (α:=ℝ) (n.choose j))) (y.known (n-j)) (fun _ _ _=> norm_nonneg _) (fun _ _ _=> le_rfl))).adjust ?_; intro i hi a; simp only [Finset.sum_apply]; exact norm_iteratedFDeriv_mul_le (x.qualify i hi) (y.qualify i hi) a (n:=n) (by exact_mod_cast le_top)
lemma mul_left (x:Stamp B P f)(y:Stamp B 0 g):Stamp B P (f*g):=by simpa using x.mul y
lemma mul_right (x:Stamp B 0 f)(y:Stamp B Q g):Stamp B Q (f*g):=by simpa using x.mul y
-- linear composition preserving P
lemma pull (x:Stamp B P u)(L:Z→L[ℝ] X): Stamp B P (fun i=> (u i)∘ L):=by
    refine ⟨fun i hi=>(x.qualify i hi).comp L.contDiff,fun n=>?_⟩; obtain ⟨c,m,hC,H⟩:=x.known n
    refine ⟨c*(1+‖L‖)^m * ‖L‖^n,m,by positivity,fun i hi z=>?_⟩; dsimp only; rw [L.iteratedFDeriv_comp_right (x.qualify i hi) z (i:=n) (by exact_mod_cast le_top)]; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans; simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]; apply le_trans (mul_le_mul_of_nonneg_right (H i hi (L z)) (by positivity)); unfold price Credit; have h:= B.right i; have he:1+‖L z‖≤ (1+‖L‖)*(1+‖z‖):=by linarith [L.le_opNorm z,norm_nonneg z,norm_nonneg L]
    calc
     _ ≤ _ := show _ ≤ Real.exp _*c*(B.fee i*((1+‖L‖)*(1+‖z‖)))^m*‖L‖^n from by gcongr
     _ = _ := by simp only [mul_pow]; ring
end Stamp
end YM.MSbar.High
