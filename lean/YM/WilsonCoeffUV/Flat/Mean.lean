import YM.WilsonCoeffUV.Flat.ConditionalInverse
/-!
# Mean convention for capped canonical supplies. Volume and URI horizon
are not tied by any of these bills. ``gradient'' issues for true labels
kept in a straightening row. A0 is on ALL longitudinal representatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV
open Filter Function Lattice RG Laurent Exterior Bloch Metric Matrix Precision Stationary
open Next.Free Tree Work.F08 FreeResolvent
open UVNext.PricedKernels (rootAt hiker)
open scoped Topology BigOperators ComplexConjugate
variable {G:Gauge} {c f L : Side} {S:StepData c f} {η σ D C : ℝ} {P:Patch}

abbrev PoleRows (P:Patch) := Row (Co P.L (TypeFace 1)) (TypeFace 1)
abbrev CoarseMean (G : Gauge) (P:Patch) := Row (Co P.L (PAC G 1)) (PAC G 1)

def meanA (G:Gauge) (P:Patch) (k : ℝ) (U:TreeRow G P) : CoarseMean G P := composeRows U
    (scaleRows k (transRows (coloration G id (expandI G P.L _) (probeRow P))))

lemma degree_bill {Z : ℝ} {α β γ:Type} [Fintype β] {u v:Row α β} {x:Row β γ}
    (h : Whole u) (g : Whole v) (f:x.strip σ C) (he:0<σ) (hp : (minusRows u v).strip σ Z) :
    (minusRows (composeRows u x) (composeRows v x)).strip σ (Fintype.card β * (Z*C)) := by
  have hh : Whole x := ⟨_,_,he,f⟩
  have hy : minusRows (composeRows u x) (composeRows v x)=composeRows (minusRows u v) x := by
    apply bank_injective ((h.prod hh).minus (g.prod hh)).safe ((h.minus g).prod hh).safe
    intro n; rw [(h.prod hh).less (g.prod hh),h.acts hh,g.acts hh,(h.minus g).acts hh,h.less g,Matrix.sub_mul]
  rw [hy]; exact strip_compose he.le hp f

lemma probe_pay (G:Gauge) (P:Patch) (k :ℝ) (he:0≤σ) : ∃ C : ℝ, 0 ≤ C ∧
    (scaleRows k (transRows (coloration G id (expandI G P.L _) (probeRow P)))).strip σ C := by
  obtain ⟨Z,hZ,h⟩ := probe_ready P σ he
  exact ⟨_,by positivity,strip_scale (strip_trans (coloration_paid (G:=G) id (expandI G _ _) _ hZ h)) _⟩

lemma meanA_period {c f : Side} (S:StepData c f) {U:TreeRow G S.patch} (hU:U.strip σ C) (he:0≤σ)
    : (meanA G S.patch S.kernel.penalty U).acts c =
      U.acts c * (show Matrix (Co c (Co S.patch.L (PAC G 1))) (Co c (PAC G 1)) ℝ from repackM (unitSplit G S 1) (Equiv.refl _) (S.kernel.penalty • (tensor G (probe S))ᵀ) ) := by
  classical
  obtain ⟨Z,hZ,h⟩ := probe_pay G S.patch S.kernel.penalty he
  rw [meanA,acts_compose he hU h c,acts_scale,acts_trans, across_backed (probeRow _) (probe S) (block_probe _)]
  rfl

lemma mean_map (G:Gauge) (S:StepData c f) (T : Forest S.ratio) (H H' : ShapeRow)
    (M:Matrix (Body 1 f) (Body 1 c) ℝ)
    (hM:Inputs S M (H.acts f) (H'.acts c))
    (hU:IsUnit (treeMatrix G S T H).det) :
    FreeResolvent.covariance G S T H * (S.kernel.penalty • (tensor G (probe S))ᵀ) = tensor G (extracted S T M) := by
  classical
  let U:=extracted S T M; let V:=tensor G U; let W:=FreeResolvent.reduce G S T*V; let I:=insertion (plant (G:=G) T)
  have hv : V=I* W := by
    refine testers fun u v=>congr_arg (dotProduct u) (Eq.symm ?_)
    rw [← Matrix.mulVec_mulVec, show W=_ from rfl,← Matrix.mulVec_mulVec]; unfold I; apply projects
    intro i; unfold V; rw [component_mul]; exact stays T M _
  have hy : fullMatrix G S H * V = S.kernel.penalty • (tensor G (probe S))ᵀ := by
    unfold fullMatrix V; rw [← tensor_mul, tensor_transpose,← tensor_scale]; congr 1
    obtain ⟨ha,hb⟩ := stationed T M _ _ hM
    unfold U baseMatrix; rw [Matrix.add_mul,hb,Matrix.smul_mul, Matrix.mul_assoc, ha, Matrix.mul_sub, Matrix.mul_one,Matrix.mul_smul,smul_sub,smul_smul,mul_inv_cancel₀ S.kernel.penalty_pos.ne',one_smul,add_sub_cancel]
  change _=V
  rw [← hy,hv, covariance]; unfold treeInverse resolve; rw [zero_smul,add_zero]
  let A := treeMatrix G S T H; let B:=fullMatrix G S H
  change (I*A⁻¹*Iᵀ)*(B*(I*W))=I*W
  have hr : Iᵀ*B*I=A := insertion.compress ..
  simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Iᵀ,← Matrix.mul_assoc (Iᵀ*B),hr, ← Matrix.mul_assoc A⁻¹, Matrix.nonsing_inv_mul A hU,Matrix.one_mul]

def loose (A:Levels G) (m:ℕ) := (A.clock.op m 0).patch
def predictionA (A:Levels G) (N m:ℕ) : PoleRows (loose A m) := ((destination A N m).duo A.clock.kernel.penalty).A0
def gaugedA (G:Gauge) (P:Patch) (R:PoleRows P) : CoarseMean G P := coloration G (expandI G P.L 1) id R

def angle (G:Gauge) (P:Patch) (Q:CoarseMean G P) : Row (Co P.L (PAC G 0)) (PAC G 1) :=
    minusRows (composeRows (climbS G P) Q) (composeRows (copyS G P) (composeRows (fixS G P) Q))

lemma angle_period (S : StepData c f) {R:PoleRows S.patch} (hR:(gaugedA G S.patch R).strip σ C) (he:0≤σ) :
      let T:=repeatF S
      let A:=installed S.ratio R
      (angle G S.patch (gaugedA G S.patch R)).acts c = repackM (unitSplit G S 0) (Equiv.refl _) (tensor G (straighten S T A)) := by
  classical
  intro T A
  have h : 0 ≤ max 0 C := le_max_left ..
  have hh : Priced (gaugedA G S.patch R) σ := ⟨_,h,fun a b=> (hR a b).mono le_rfl (le_max_right ..)⟩
  have H : (gaugedA G S.patch R).acts c = repackM _ _ (tensor G A) := cross_backed R _ rfl
  rw [angle, (climbS_paid.chain hh he).acts_minus (copyS_paid.chain (fixS_paid.chain hh he) he) he, climbS_paid.acts_chain hh he,
    copyS_paid.acts_chain (fixS_paid.chain hh he) he, fixS_paid.acts_chain hh he, H,
    climbS_period (S:=S),copyS_period (S:=S),fixS_period (S:=S)]
  let M := Equiv.refl (Lines G c 1); let X:=unitSplit G S 1; let Y := unitSplit G S 0; let W := Equiv.refl (Lines G c 0)
  let I:=tensor G (hiker S T); let J:=tensor G (rootAt S.ratio); let D:=tensor G (fixRoot S)
  have ht : tensor G (straighten S T A)= I * tensor G A - J * (D * tensor G A) := by
    unfold D T J I; rw [UVNext.PricedKernels.factor_tree,Matrix.sub_mul,Matrix.mul_assoc _ (fixRoot S),← tensor_mul,← tensor_mul,← tensor_mul]; ext i j; simp [tensor]; split <;> simp; rfl
  erw [← repack_multiply Y X M I, ← repack_multiply W X M D, ← repack_multiply Y W M J, ht]; rfl

lemma horizon_step (A : Levels G) (m N : ℕ) (hm:m<N) (c f:Side) (hc : f.val=c.val*(loose A m).L.val) :
    let S : StepData c f := ⟨loose A m,A.clock.kernel,hc⟩
    Inputs S (installed S.ratio (predictionA A N m)) ((freeForms A N (m+1)).acts f) ((freeForms A N m).acts c) := by
  intro S
  have hh := (Flight.tangent (destination A N m) A.clock.kernel (A.clock.adm m) hc (c:=c) (f:=f)).1
  unfold freeForms; rw [loc_land A N m hm]; exact hh

def conditional (A:Levels G) (N m:ℕ) := gamma G (loose A m) A.clock.kernel (freeForms A N (m+1))
def feedA (A:Levels G) (N m:ℕ) : CoarseMean G (loose A m) := meanA G _ A.clock.kernel.penalty (conditional A N m)

lemma cond_laws (A : Levels G) (m N : ℕ) :
    let H := freeForms A N (m+1)
    (∀ (c f:Side) (hc:f.val=c.val*(loose A m).L.val), let S : StepData c f := ⟨loose A m,A.clock.kernel,hc⟩; IsUnit (treeMatrix G S (repeatF S) H).det) ∧
      Whole (conditional A N m) ∧ WickLine (loose A m) G A.clock.kernel H (conditional A N m) := by
  intro H
  obtain ⟨σ,hσ,h⟩ := actually_gamma A.clock.kernel G _ (A.clock.adm (m+1))
  obtain ⟨C,hC,Q⟩ := h (loose A m) rfl (A.blocks m 0).branches
  obtain ⟨hR,hT,hE⟩ := Q (location A N (m+1)); exact ⟨hR,⟨σ,C,hσ,hT⟩,hE⟩

lemma feed_period (A:Levels G) (N m:ℕ) (hm:m<N) (c f:Side) (hc:f.val=c.val*(loose A m).L.val) :
    let S:StepData c f := ⟨loose A m,A.clock.kernel,hc⟩
    (feedA A N m).acts c=repackM (unitSplit G S 1) (Equiv.refl _) (tensor G (extracted S (repeatF S) (installed S.ratio (predictionA A N m)))) := by
  classical
  intro S
  let k:=A.clock.kernel
  let H:=freeForms A N (m+1)
  have ⟨hx,⟨σ,B,hσ,hB⟩,he⟩ := cond_laws A m N
  have hr := meanA_period S hB hσ.le
  have hv := he c f hc
  let V:= unitSplit G S 1
  let Z:=repackM V V (covariance G S (repeatF S) H)
  let M:=Equiv.refl (Lines G c 1)
  have hy : (feedA A N m).acts c= (conditional A N m).acts c* (show Matrix (Co c (Co (loose A m).L (PAC G 1))) (Lines G c 1) ℝ from repackM V M (k.penalty • (tensor G (probe S))ᵀ) ) := hr
  rw [hy, show (conditional A N m).acts c=Z from hv]; unfold Z
  erw [← repack_multiply V V M]; exact congr_arg (repackM V M) (mean_map G S (repeatF S) H _ _ (horizon_step A m N hm c f hc) (hx c f hc))

end YM.WilsonCoeffUV
