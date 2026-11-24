import YM.Contacts.Milling.Dock
/-! Finite physical data for jets and their covariance Wick. -/
noncomputable section
namespace YM.Contacts.Milling.Spark
open Filter Function Set Finset Lattice RG Wilson Bid Exterior Precision Tree Matrix
open Bloch Stationary Garf Pulse Spine Larch PertExtension.Series
open PertExtension.GaussianScore FreeResolvent PhysicalNext.RankCovariance
open scoped Topology ContDiff BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G:Gauge}{c f n: Side}{S:StepData c f}
def spindle (G:Gauge)(n:Side)(B:FreeResolvent.FaceRow): Matrix (Lines G n 1) (Lines G n 1) ℝ:= tensor G (Precision.K (B.acts n))
def flax (G:Gauge)(S:StepData c f):= tensor G (probe S)
local notation "T" => planting S.ratio S.patch.odd_side
local notation "κ" => (AxisChart G T)
local notation "Ξ"=> insertion (plant T (G:=G))
local notation "FV" => Link G f
local notation "CV" => Link G c
local notation "Γ" => Active G T
local notation "β" => S.kernel.penalty
local notation "Γθ" => House.Dir Γ
abbrev Astro (_G: Gauge)(S:StepData c f):= Matrix (Body 1 f) (Body 1 c) ℝ
def atr (G:Gauge)(S:StepData c f) (P:Astro G S):= tensor G (extracted S (planting S.ratio S.patch.odd_side) P)
variable {A:Astro G S}{P H:FreeResolvent.FaceRow}{b:ℝ}
structure Beam (S:StepData c f) (G:Gauge) (A:Astro G S)(P H:FreeResolvent.FaceRow) (b:ℝ): Prop where
   light : Larger (G:=G) S
   gapV : 0<b
   gap : Gap (P.acts f) b
   sym_eq : (P.acts f)ᵀ=P.acts f
   units : Inputs S A (P.acts f) (H.acts c)
variable (h:Beam S G A P H b)
section
include h
local notation "Kθ" =>treeMatrix G S T P
lemma gapθ : Gap Kθ (treeFare G S.patch S.kernel b):= tree_gap _ _ _ h.light h.gapV h.gap
lemma gapLaw : Kθᵀ=Kθ:= by unfold treeMatrix; rw [transpose_submatrix,full_symmetric P h.sym_eq]
lemma fence_laws : treeInverse G S T P 0 * Kθ=1∧ Kθ*treeInverse G S T P 0=1:= by simpa using tree_laws T P h.light h.gapV h.gap (u:=0) le_rfl
lemma traceθ : ∀ v, Ξ *ᵥ (reduce G S T *ᵥ (atr G S A *ᵥ v))= atr G S A *ᵥ v:= by
   intro v; apply projects; intro i; rw [atr,component_mul]; exact stays T A _
lemma beamθ : fullMatrix G S P* atr G S A=β • (flax G S)ᵀ ∧ flax G S*atr G S A=1-β⁻¹ • spindle G c H := by
   obtain ⟨hl,hp⟩:= stationed T A (P.acts f) (H.acts c) h.units; have H1: flax G S* atr G S A=1-β⁻¹ • spindle G c H := by unfold flax atr spindle; rw [← promote_prod,hl,promote_diff,promote_coeff,promote_one]
   refine ⟨?_,H1⟩; unfold flax atr fullMatrix; rw [tensor_transpose, ← promote_prod, ← promote_coeff]; apply congr_arg; unfold baseMatrix; rw [Matrix.add_mul,hp, Matrix.smul_mul, Matrix.mul_assoc (probe S)ᵀ,hl, Matrix.mul_sub,Matrix.mul_smul,Matrix.mul_one,smul_sub,smul_smul,mul_inv_cancel₀ S.kernel.penalty_pos.ne',one_smul]; abel
omit h in
lemma chief (x y:FV)(v w:CV):
 (x ⬝ᵥ (spindle G f P *ᵥ y)) + β*((v-(flax G S) *ᵥ x) ⬝ᵥ (w - (flax G S) *ᵥ y)) = x ⬝ᵥ (fullMatrix G S P *ᵥ y) - (x ⬝ᵥ ( (β•(flax G S)ᵀ)*ᵥ w)) - (y ⬝ᵥ ( (β•(flax G S)ᵀ) *ᵥ v)) + β*(v ⬝ᵥ w):= by
   unfold spindle fullMatrix baseMatrix; rw [promote_sum,promote_coeff,promote_prod,← tensor_transpose]; simp only [flax, Matrix.smul_mulVec, Matrix.add_mulVec,← Matrix.mulVec_mulVec,dotProduct_add, sub_dotProduct,dotProduct_smul,smul_eq_mul,dotProduct_sub,dotProduct_transpose_mulVec]; simp only [dotProduct_comm]; ring
lemma shift_physical (x:CV)(d:Γθ) : let y:= atr G S A *ᵥ x+Ξ *ᵥ d; y ⬝ᵥ (spindle G f P *ᵥ y) + β*((x - flax G S *ᵥ y) ⬝ᵥ (x - flax G S *ᵥ y)) = d ⬝ᵥ (Kθ*ᵥ d) + x ⬝ᵥ (spindle G c H *ᵥ x):= by
   intro y; let τ:= atr G S A; let φ:=flax G S; let F:=fullMatrix G S P; let u:= τ *ᵥ x; let w:= Ξ *ᵥ d; let z:= (β• φᵀ) *ᵥ x; have hz: F *ᵥ u=z:= by unfold u; rw [Matrix.mulVec_mulVec]; exact congr_arg (fun M=> M*ᵥ x) (beamθ h).1
   have ht:u ⬝ᵥ (F*ᵥ w)=w ⬝ᵥ z:= by rw [←hz]; rw (occs:=.pos [1]) [← show Fᵀ= F from full_symmetric P h.sym_eq]; rw [dotProduct_transpose_mulVec]
   have hp:w ⬝ᵥ (F*ᵥ w)=d ⬝ᵥ (Kθ*ᵥ d):= insertion.dot_compress _ _ _ _
   have hu:u ⬝ᵥ z= β*(x ⬝ᵥ x) - x ⬝ᵥ (spindle G c H*ᵥ x):= by unfold z φ u τ; rw [ Matrix.smul_mulVec,dotProduct_smul,dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,(beamθ h).2,Matrix.sub_mulVec,Matrix.one_mulVec,dotProduct_sub,Matrix.smul_mulVec,dotProduct_smul]; simp only [smul_eq_mul]; field_simp [S.kernel.penalty_pos.ne']
   rw [chief]; change (u+w) ⬝ᵥ (F *ᵥ (u+w))-(_ ⬝ᵥ z)-(_ ⬝ᵥ z)+_= _; change (u+w) ⬝ᵥ (F *ᵥ (u+w))-((u+w) ⬝ᵥ z)-((u+w) ⬝ᵥ z)+_= _; simp only [Matrix.mulVec_add,dotProduct_add,add_dotProduct,hz,ht,hp,hu]; ring
end
-- chart map & discipline
noncomputable def tribe (S:StepData c f)(F:Forest S.ratio) : (AxisChart G F)≃L[ℝ] (House.Dir (Active G F)):= LinearEquiv.toContinuousLinearEquiv { toFun:=active F, invFun:=profile F, left_inv:=fun _=>rfl,right_inv:=fun _=>rfl,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
def stash (S:StepData c f)(F:Forest S.ratio): AxisChart G F →L[ℝ] Link G f := (LinearMap.toContinuousLinearMap (insertion (plant F)).mulVecLin).comp (tribe S F).toContinuousLinearMap
def course (S:StepData c f)(F:Forest S.ratio)(A: Astro G S) : Link G c →L[ℝ] AxisChart G F := (tribe S F).symm.toContinuousLinearMap.comp (LinearMap.toContinuousLinearMap ((reduce G S F *tensor G (extracted S F A)).mulVecLin))
lemma stash_drape (S:StepData c f)(F:Forest S.ratio)(x:AxisChart G F) : input G f (stash S F x)= F.drape (PertExtension.Chart.expLinks _ _ x):= by
  funext ⟨z,j⟩; rw [encode_link]; let v:=(z,j); have hp: arm G f 1 ((stash S F) x)= stretch (S:=S) F (0,x):= by have ht: (stash S F) x= _ := chart_flow S F x; rw [ht]; rfl
  rw [hp]; have hx:= Work.F01.collect_vertical (S:=S) F x v; calc
    _ = G.lieExp (collect G (Bid.stretch F (0,x)) v):= rfl
    _ = _ := by by_cases h:v∈F.trunks; · rw [hx,dif_pos h,show G.lieExp 0=1 by simp]; exact (F.on_tree (PertExtension.Chart.expLinks G _ x) ⟨v,h⟩).symm
                rw [hx,dif_neg h]; exact (F.off_tree (PertExtension.Chart.expLinks G _ x) ⟨v,h⟩).symm
lemma gather_flow (h:Beam S G A P H b)(v:CV): stash S T (course S T A v)=atr G S A *ᵥ v:= by change Ξ *ᵥ ((reduce G S T * atr G S A) *ᵥ v) = _; rw [← Matrix.mulVec_mulVec]; exact traceθ h _
-- s release bound little polynomial
def collar {X:Type*}[Fintype X] (M: Matrix X X ℝ)(x y:X→ℝ):ℝ:= x ⬝ᵥ (M*ᵥ y)
def order (S:StepData c f)(Z:Forest S.ratio)(P:FreeResolvent.FaceRow): AxisChart G Z→ₗ[ℝ] Module.Dual ℝ (AxisChart G Z) where
  toFun x:={
    toFun y:= collar (treeMatrix G S Z P) (tribe S Z y) (tribe S Z x)
    map_add' _ _:= by simp_rw [collar,map_add,add_dotProduct]
    map_smul' _ _:= by simp_rw [collar,map_smul,smul_dotProduct]; rfl }
  map_add' x y:= by apply LinearMap.ext; intro a; change (_ ⬝ᵥ ( _*ᵥ (tribe S Z (x+y))))= (_ ⬝ᵥ (_ *ᵥ tribe S Z x))+(_ ⬝ᵥ (_ *ᵥ tribe S Z y)); rw [map_add,Matrix.mulVec_add,dotProduct_add]
  map_smul' k x:= by apply LinearMap.ext; intro a; change (_ ⬝ᵥ ( _*ᵥ tribe S Z (k • x)))= k • (_ ⬝ᵥ (_*ᵥ _)); rw [map_smul,Matrix.mulVec_smul,dotProduct_smul]
def court (h: Beam S G A P H b): Law κ where
 P:= order S T P
 turns x y:= by change _ ⬝ᵥ ( _ *ᵥ _) = _ ⬝ᵥ (_ *ᵥ _); rw (occs:=.pos [1]) [← gapLaw h]; rw [dotProduct_transpose_mulVec]
 slope := by
   let t:= T; let a:= treeFare G S.patch S.kernel b; refine ⟨a/2,half_pos (treeFare_pos _ _ _ h.gapV),fun v=> ?_⟩; change (a/2)*‖v‖^2≤ _ ⬝ᵥ ( _ *ᵥ _) /2; have hc:= treeFare_pos G S.patch S.kernel h.gapV; let u:=active t v; have he:= (gapθ h).lower u; change _ ≤ u ⬝ᵥ (_*ᵥ u) / 2; suffices hx: ‖v‖^2 ≤ u ⬝ᵥ u by nlinarith only [he,mul_le_mul_of_nonneg_left hx hc.le]
   unfold u; simp_rw [active_dot, real_inner_self_eq_norm_sq]; let r:= ∑ i:t.Free, ‖v i‖^2; have hr:0≤ r:=sum_nonneg (fun i _=>sq_nonneg _); have hx : ‖v‖ ≤ Real.sqrt r:= (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun j=> by nlinarith only [Real.sq_sqrt hr, Real.sqrt_nonneg r, single_le_sum (f:=fun i:t.Free=> ‖v i‖^2) (fun i _=>sq_nonneg _) (mem_univ j), norm_nonneg (v j)])
   exact (pow_le_pow_left₀ (norm_nonneg v) hx _).trans_eq (Real.sq_sqrt hr) -- arguments
 smooth := by
   let F := tribe S T (G:=G); let M:= treeMatrix G S T P; change Continuous (fun v:κ=> F v ⬝ᵥ (M *ᵥ F v)); unfold dotProduct Matrix.mulVec; unfold dotProduct; fun_prop
local notation "Λ" => ( FV )
def attend (S:StepData c f)(Z:Forest S.ratio)(i:Lines G f 1): Module.Dual ℝ (AxisChart G Z):= ((ContinuousLinearMap.proj i).comp (stash S Z)).toLinearMap
lemma attendance (i: Lines G f 1): tribe S T ((court h).inverse (attend S T i))=(treeInverse G S T P 0 *ᵥ (reduce G S T *ᵥ Pi.single i 1)):= by
   let M:= treeMatrix G S T P; let B:=treeInverse G S T P 0; let V : κ:= (tribe S T).symm (B *ᵥ (reduce G S T *ᵥ Pi.single i 1))
   suffices hp : (court h).P V=attend S T i by rw [←hp,Law.solves]; exact (tribe S T).apply_symm_apply _
   apply LinearMap.ext; intro v; change (tribe S T v) ⬝ᵥ (M *ᵥ tribe S T V) = (Ξ *ᵥ tribe S T v) i; rw [(show tribe S T V=_ from (tribe S T).apply_symm_apply _), Matrix.mulVec_mulVec _ M B, (show M*B=1 from (fence_laws h).2), Matrix.one_mulVec]; rw [show reduce G S T=Ξᵀ from rfl,dotProduct_transpose_mulVec,dotProduct_comm,dotProduct_single,mul_one]
lemma wick_rises (i j: Lines G f 1): (court h).wick (attend S T i) (attend S T j)= covariance G S T P i j:= by
  change (Ξ *ᵥ tribe S T _) j=_; rw [attendance h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]; let R:= covariance G S T P; change (R*ᵥ Pi.single i 1) j=R i j; rw [mulVec,dotProduct_single,mul_one]; exact congr_fun (congr_fun (covariance_symmetric T P h.sym_eq) i) j
end YM.Contacts.Milling.Spark
