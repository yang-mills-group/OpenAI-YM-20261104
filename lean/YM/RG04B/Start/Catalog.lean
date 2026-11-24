import YM.RG04B.Start.Face
import YM.FullVolume.Stage.Crests

/-!
# Top analytic packets on the actual labels

The implementation uses `Tent.launch`, `Design.top` and their local (unmasked)
kinematics. Taylor predicts the Wilson deficit *relative* to those full lower
completions (β already used there). Thus packet with curvature degree d≥5 starts
at order d-2 in fluctuation coordinates. No changes to gas anywhere when using
this particular catalogue: resource comparison is on exactly the `raw` footprints,
fused as in this *actual* construction. Includes the reference clip/weights.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG04B.Startup
open Function Filter Work Tensor RG Wilson Lattice Ovens
open WilsonStartup Start Progress.DirectedRecipe
open scoped ContDiff Topology Matrix.Norms.Frobenius BigOperators Classical Padded
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n : Side}

/-- Polynomial positive orders of the top correction; independent ranks and tensors.
(Order arguments d indexing powers of `G.curvature`. Analytic completion entails
terms at higher orders in g when rendered at U.) -/
def incrementTop (j : ℕ) (x : G.Color) := predict G j x - predict G 4 x

lemma prescribed (p : Clip) (U : Config G n) {j : ℕ} (hc : p.direct ≤ 1) :
    Precision.quadratic p (Design.top G p) U + Precision.uncut (Design.top G p).cubic U +
      Precision.uncut (Design.top G p).quartic U +
      ∑ i : Cell n, Design.bulk p * (incrementTop j (G.curvature (faceValue U i)) + lag G j i U)
      = energy U := by
  have he (u:G.El): surplus u=incrementTop j (G.curvature u)+later j u:= by
    rw [← correct_four]; unfold later incrementTop; abel
  simp only [lag]; simp_rw [←he]; exact Design.principal_top p U hc

lemma rank_sum {j : ℕ} (h : 4 ≤ j) (x : G.Color) :
    incrementTop j x = ∑ i ∈ Finset.Ico 5 (j+1), diagonal (coeff (inK G) i 0) x := by
  unfold incrementTop
  induction j, h using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    rw [show Finset.Ico 5 (j+1+1) = insert (j+1) (Finset.Ico 5 (j+1)) by ext; simp; omega,
      Finset.sum_insert (by simp),predicts, ← ih]; abel

open Padded in
/-- The occurrences as actually rendered, using *fresh* Taylor coefficients of the
extra Wilson action, not subtracting two different lists. -/
def row (G : Gauge) (n : Side) (c : Clip) (β : ℝ) (j : ℕ) (i : ℕ) : Config G n → ℝ :=
  if fixed (Start.Sheet n) i then Sum.elim (fun p : Key n => Start.weight c β •
    (fun U => incrementTop j (G.curvature (faceValue U p.positive)))) (fun _=> 0) (name (Start.Sheet n) i)
  else 0
open Padded in
private def batch (G : Gauge) (n : Side) (c : Clip) (β : ℝ) (j : ℕ) (i : ℕ) : Config G n→ℝ :=
  if fixed (Start.Sheet n) i then Sum.elim (fun p : Key n => Start.weight c β • lag G j p.positive)
     (fun _=> 0) (name (Start.Sheet n) i)
  else 0

/-- Actual labels on the outgoing construction catalogue (not extensions out
of this `Campaign`). -/
def chart (G : Gauge) (n : Side) (c : Clip) (β : ℝ) (e : ℕ) : ℕ → Config G n → ℝ :=
  stuff (Rack.upE (Start.dictionary G n)) (row G n c β e)

private def late (G : Gauge) (n : Side) (c : Clip) (β : ℝ) (e : ℕ) : ℕ → Config G n → ℝ :=
  stuff (Rack.upE (Start.dictionary G n)) (batch G n c β e)

section Limits
variable {b : BudgetPoint}{c : Clip}{β : ℝ}
open Padded Rack
private lemma rawSplit (j : ℕ) : (payload c b G n β).regular = row G n c β j + batch G n c β j := by
  funext i U
  simp only [payload,Pi.add_apply,row,batch]; split
  · rcases name (Start.Sheet n) i with x|x
    · change (Start.weight c β * x.accrual U : ℝ) = Start.weight c β * incrementTop j (G.curvature (faceValue U x.positive)) + Start.weight c β * lag G j x.positive U
      have he (u:G.El): surplus u=incrementTop j (G.curvature u)+later j u:= by rw [← correct_four]; unfold later incrementTop; abel
      rw [Key.accrual_def,WilsonStartup.residual,he,lag,mul_add]
    exact (add_zero 0).symm
  exact (add_zero 0).symm

private abbrev delayTap (G : Gauge) (n : Side) (c : Clip) (b : BudgetPoint) (β : ℝ) (j : ℕ) :=
  { Start.payload c b G n β with regular := batch G n c β j }
private abbrev backed (G : Gauge) (n : Side) (c : Clip) (b : BudgetPoint) (β : ℝ) (e : ℕ) :=
  (Start.dictionary G n).pours (delayTap G n c b β e)

private lemma backed_shape {j : ℕ} (hd : 2≤j) : (backed G n c b β j).RegularFamily b := by
  let A:= backed G n c b β j
  have he (i : ℕ) : b.Regular ((A.reg i).support) (A.E i) ∧ A.E i 1 = 0 ∧ ∀ x y, logHessian (A.E i) x y = 0 := by
    change b.Regular (eInfo _).support _ ∧ _
    simp only [A, Pipes.pours,batch]
    split
    · cases h : name (Start.Sheet n) i with
      | inl p =>
        let s := Start.weight c β
        change b.Regular p.skin (s • _) ∧ _
        rw [p.skin_positive]
        let f := lag G j p.positive
        change b.Regular _ (s • f) ∧ (s•f) 1=0 ∧ ∀ x y, _
        refine ⟨times_reg _ (lag_regular ..),by simp [f,lag_one],fun x y=> ?_⟩
        change iteratedFDeriv ℝ 2 (s • (f ∘ increment 1)) 0 ![x,y] = 0
        rw [iteratedFDeriv_const_smul_apply ((lag_smooth _ _ _).contDiffAt.of_le le_top),smul_apply]
        exact (congr_arg (s • ·) (lag_hessian j p.positive hd x y)).trans (smul_zero ..)
      | inr p=>
        exact ⟨zero_reg,rfl, fun _ _=> by simp [logHessian]⟩
    exact ⟨zero_reg,rfl, fun _ _=> by simp [logHessian]⟩
  exact ⟨fun i=>(he i).1, fun i=>(he i).2.1, fun i _ x y _ _=>(he i).2.2 x y⟩

def required (G : Gauge) (j k p : ℕ) := (lag_price G j k p).choose_spec.choose
def offered (G : Gauge) (j k p : ℕ) := (lag_price G j k p).choose
def cost (G : Gauge) (b : BudgetPoint) (v : ℝ) (j : ℕ) :=
   (Fintype.card Signed:ℝ)*Fintype.card PlaqAxes*(Start.overhead b*(v*(offered G j b.order b.power*b.threshold^(j+1))))
lemma required0 (G : Gauge) (j k p : ℕ) : 0 < required G j k p := (lag_price G j k p).choose_spec.choose_spec.2.1
lemma offered0 (G : Gauge) (j k p : ℕ) : 0 < offered G j k p := (lag_price G j k p).choose_spec.choose_spec.1

private lemma backed_energy (hc : c.direct ≤ 1) (e : ℕ) (h : b.threshold ≤ required G e b.order b.power)
    (x : ℝ) (hx : ‖β‖ ≤ x) : (backed G n c b β e).EBound b (cost G b x e) := by
  let Y:=offered G e b.order b.power * b.threshold^(e+1)
  have hY : 0 ≤ Y:= mul_nonneg (offered0 ..).le (pow_nonneg b.threshold_pos.le _)
  let E:= fun i : Start.Sheet n => i.elim (fun _ => ‖Start.weight c β‖*Y) (fun _=> (0:ℝ))
  let B (i : ℕ) := if fixed (Start.Sheet n) i then E (name (Start.Sheet n) i) else 0
  let A := backed G n c b β e
  have he : ∀ i : ℕ, b.supBounds (A.reg i).site (A.reg i).support (A.E i) (B i) := by
    intro i
    simp only [B,A,Pipes.pours,batch,dictionary]; split
    · cases h' : name (Start.Sheet n) i with
      | inl p =>
        change b.supBounds p.native p.skin (Start.weight c β • _) _
        apply times_bound
        rw [Key.skin_positive]
        exact (lag_price G e b.order b.power).choose_spec.choose_spec.2.2.2 b rfl rfl h n p.positive p.native (p.skin_positive ▸ p.native_mem)
      | inr p => exact zero_bound
    exact zero_bound
  refine ⟨B,he,fun o=>?_⟩
  let f(i:Start.Sheet n):ℝ:= if (eInfo i).site=o then b.mass (eInfo i).support (E i) else 0
  apply Padded.budget (α:=Start.Sheet n) (g:=f)
  · intro i; change (if _ then b.mass _ (ite ..) else _) = _; by_cases hs : fixed (Start.Sheet n) i
    · rw [if_pos hs,if_pos hs]; rfl
    rw [if_neg hs,if_neg hs]; simp [BudgetPoint.mass]
  · intro i; unfold f; split
    · apply mul_nonneg (Real.exp_pos _).le
      simpa only [B,Padded.name_index,fixed_index,if_true] using (show 0 ≤ B (Padded.index i) from (he _).1)
    exact le_rfl
  dsimp only [f]
  rw [Fintype.sum_sum_type]; simp only [E,Sum.elim_inl,Sum.elim_inr,BudgetPoint.mass,mul_zero,ite_self,Finset.sum_const_zero,add_zero]
  rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type (fun _:Cell n=> _)]
  rw [show cost G b x e= ∑ _s : Signed,∑ y : Site n,∑ _i:PlaqAxes, (if y=o then Start.overhead b*(x*Y) else 0) from by change ↑(Fintype.card Signed)*_*(_*(_*Y))=_; simp; ring]
  gcongr ∑ _,∑ _,∑ _,?_ with s _ y _ i _
  change (if y=o then b.mass (Key.skin (s,y,i)) (‖Start.weight c β‖*Y) else _) ≤ _
  split
  · refine mul_le_mul (Real.exp_monotone ?_) (mul_le_mul_of_nonneg_right ((Start.weight_le β hc).trans hx) hY) (mul_nonneg (norm_nonneg _) hY) (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_left _ b.exponent_pos.le
    exact_mod_cast skin_cost (s,y,i)
  rfl

lemma deployed (hc : c.direct ≤ 1) {j : ℕ} (hj : 2≤j) (h : b.threshold ≤ required G j b.order b.power)
    (x : ℝ) (hx : ‖β‖ ≤ x) :
    let d := Start.payload c b G n β
    let X := Start.dictionary G n
    let T := Pipes.fused (folio G n) b (Rack.widen X d)
    let Q := {T with E:= T.E-chart G n c β j}
    Q.RegularFamily b ∧ Q.EBound b (cost G b x j) := by
  intro d X T Q
  have he : Q.E= late G n c β j := by
    funext i U
    by_cases hp : i∈Set.range (Rack.upE X)
    · obtain ⟨i,rfl⟩:=hp
      change stuff (Rack.upE X) d.regular _ U - stuff (Rack.upE X) (row G n c β j) _ U = stuff _ (batch G n c β j) _ U
      rw [stuffed,stuffed,stuffed,show d=Start.payload .. from rfl, rawSplit j]; exact add_sub_cancel_left ..
    unfold Q; dsimp only []; change stuff (Rack.upE X) d.regular i U - stuff (Rack.upE X) (row G n c β j) i U = stuff _ (batch G n c β j) i U
    rw [blank _ _ hp, blank _ _ hp, blank _ _ hp]; exact sub_self _
  let H := (drawer G n).pours (Rack.widen X (delayTap G n c b β j))
  have hR : Q.E=H.E := he
  have hD : Q.reg=H.reg:=rfl
  have hs:= Rack.preserves X (delayTap G n c b β j) b
  obtain ⟨ha,hf,hv⟩ := (show H.RegularFamily b from hs.regular (backed_shape hj)); obtain ⟨g,hg,hw⟩ := (show H.EBound b _ from hs.Ebound (backed_energy hc j h x hx))
  refine ⟨⟨fun i=> ?_,fun i=>?_,fun i hi=>?_⟩,g,?_,?_⟩
  · rw [hR,hD]; exact ha i
  · rw [hR]; exact hf i
  · rw [hD,hR]; rw [hD] at hi; exact hv i hi
  · rw [hR,hD]; exact hg
  rw [hD]; exact hw
end Limits
end YM.RG04B.Startup
