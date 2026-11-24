import YM.OPE.Compatible.Porch.Mesa
/-! # Halo slopes noise -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Zeph
open Function Filter Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Matrix Bloch Precision Exterior Tree
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra GaussianScore Metric Push Push.AbsoluteSums
variable {G:Gauge}{c f:Side}
attribute [local instance] Gauge.frobInner
open Radial Flume.Virgin
open PhysicalNext.Repeat.Aroma
open YM.AnalyticNext.QuarticMatch Radius Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom Estimate Sheets Model
open Woody Next.Free Finset Work.F03 Progress.StationaryScenes AnalyticNext.QuarticMatch.Local
variable {t r R B b:ℝ}{m:ℕ}
variable (S:StepData c f) (F: Forest S.ratio)
local notation "Q" =>(Bid.Dir G c × AxisChart G F)
namespace Dew
noncomputable def lane (p:Edge (Site c)): Q→L[ℝ] (G.Color × Bid.Dir G (native S.patch)) := ((ContinuousLinearMap.proj (R:=ℝ) (p.1, coord p.2)) ∘L (ContinuousLinearMap.fst ..)).prod (Model.pick S p.1 ∘L PinW S F G)
lemma lane_small (p:Edge (Site c))(x:Q):‖lane S F p x‖≤‖x‖:=by
    rw [Prod.norm_def, lane,ContinuousLinearMap.prod_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply]; simp only [ContinuousLinearMap.proj_apply]; exact max_le ((norm_le_pi_norm x.1 _).trans (le_max_left ..)) ((Model.fits_token S p.1 _).trans (pinUnit S F x))
lemma laneAct (p:Edge (Site c)) (ht:0<t)(hb:0≤b)(v:Q)(hp:On S F G t (S.ratio.embed p.1) v b): ‖lane S F p v‖ ≤ Real.exp (t*Model.capacity S.patch)*b:= by
       rw [Prod.norm_def, lane,ContinuousLinearMap.prod_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply]; simp only [ContinuousLinearMap.proj_apply]; refine max_le (?_) (Model.token S p.1 _ _ _ (LightOn S F v _ hp hb) ht.le hb); have hs:= hp.1 (p.1,coord p.2); change ‖v.1 _‖ ≤ b*Green.wt _ (S.ratio.embed p.1) (S.ratio.embed p.1) at hs; simp only [Green.wt,separation_self,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] at hs; exact hs.trans (le_mul_of_one_le_left hb (Real.one_le_exp (by positivity)))
open Radius
variable (H: Sheds G S.patch S.kernel)
noncomputable def Bone (p: Edge (Site c)):Q →ℝ:= Articles.noise (stepAt S.patch S.kernel (Model.marker S.patch)) H.tag (0,p.2) ∘ (lane S F p)
lemma boneLive (e:Edge (Site c))(x:Q)(t:S.Choices)(hq:S.patch.Branches S.kernel G) (hp:‖x‖< H.b): S.kernel.penalty*G.price ((represent x.1) e *(S.prediction (fieldF F x.2) t e)⁻¹)= Bone S F H e x:=by
       have hz:=Articles.issued S hq t H e (x.1 (e.1,coord e.2),PinW S F G x) ((pinUnit S F x).trans hp.le); rw [represent_link,_root_.mul_comm] -- error
       rw [← Pines S F x,_root_.mul_comm]; exact hz.2.2
lemma boneRate {x:Q}(hp: ‖x‖ < H.b)(e:Edge (Site c)):ContDiffAt ℝ ω (Bone S F H e) x:= (H.jet (lane S F _ x) ((lane_small S F e x).trans hp.le) e.2).comp x (lane S F e).contDiff.contDiffAt
noncomputable def fieldCost {P:Patch}{K:KernelChoices}(H:Sheds G P K)(v:Axis)(t:ℝ)(m:ℕ):ℝ:= ∑ i∈ range (m+1), H.norms i v*(Real.exp (t*capacity P))^i
lemma fieldPos {P:Patch}{K:KernelChoices}(H:Sheds G P K)(v:Axis):0 ≤ fieldCost H v t m:=sum_nonneg fun i _=> mul_nonneg (zero_le_one.trans (H.priced i v)) (pow_nonneg (Real.exp_nonneg _) _)
private lemma fieldProductBound {i m : ℕ} (hi : i ≤ m) (h : ℕ → ℝ) (hh : ∀ n, 0 ≤ h n)
    (z : ℝ) (hz : 0 ≤ z) (a b : Fin i → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hab : ∀ j, a j ≤ z * b j) :
    h i * ∏ j, a j ≤ (∑ n ∈ range (m+1), h n * z^n) * ∏ j, b j := by
  calc
    _ ≤ h i * ∏ j, z * b j :=
      mul_le_mul_of_nonneg_left (prod_le_prod (fun j _ => ha j) (fun j _ => hab j)) (hh i)
    _ = (h i * z^i) * ∏ j, b j := by
      rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (single_le_sum (fun n _ => mul_nonneg (hh n) (pow_nonneg hz n))
        (mem_range.mpr (by omega) : i ∈ range (m+1)))
      (prod_nonneg fun j _ => hb j)

private lemma fineLinearBound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : StepData c f) (J : Articles.Fine G T) (a : Axis) (ticket : X → ℝ → Prop)
    (L : X →L[ℝ] (G.Color × Bid.Dir G f)) (x : X) (hL : ‖L x‖ ≤ J.b)
    {i m : ℕ} (hi : i ≤ m) (z : ℝ) (hz : 0 ≤ z)
    (scale : ∀ d b, 0 ≤ b → ticket d b → ‖L d‖ ≤ z*b) :
    Costs ticket (Radius.Polish.budget ℝ) (Articles.noise T J.tag (0,a) ∘ L) x i
      (∑ n ∈ range (m+1), J.norms n a * z^n) := by
  intro d b hb
  let field := Articles.noise T J.tag (0,a) (G:=G)
  unfold Radius.Polish.budget
  rw [lin_rate_at field L x (J.jet (L x) hL a) i d]
  apply ((iteratedFDeriv ℝ i field (L x)).le_opNorm _).trans
  apply (mul_le_mul_of_nonneg_right (J.cost i a (L x) hL) (prod_nonneg fun _ _ => norm_nonneg _)).trans
  exact fieldProductBound hi (fun n => J.norms n a) (fun n => zero_le_one.trans (J.priced n a))
    z hz (fun j => ‖L (d j)‖) b (fun _ => norm_nonneg _) (fun j => (hb j).1)
    (fun j => scale _ _ (hb j).1 (hb j).2)

lemma boneCharge {x:Q}(hp: ‖x‖ < H.b)(ht:0<t)(e:Edge (Site c)): ∀ i, i ≤ m → Costs (On S F G t (S.ratio.embed e.1)) (Radius.Polish.budget ℝ) (Bone S F H e) x i (fieldCost H e.2 t m):=by
  intro i hi
  let T : StepData (marker S.patch) (native S.patch) := stepAt S.patch S.kernel (marker S.patch)
  let L : Q →L[ℝ] (G.Color × Bid.Dir G (native S.patch)) := lane S F e
  let ticket : Q → ℝ → Prop := On S F G t (S.ratio.embed e.1)
  let z : ℝ := Real.exp (t * Model.capacity S.patch)
  have hL : ‖L x‖ ≤ H.b := (lane_small S F e x).trans hp.le
  have scale : ∀ (d : Q) (b : ℝ), 0 ≤ b → ticket d b → ‖L d‖ ≤ z * b := by
    intro d b hb ht'
    with_reducible exact laneAct S F e ht hb d ht'
  unfold Bone fieldCost
  with_reducible
    exact fineLinearBound (X:=Q) (c:=marker S.patch) (f:=native S.patch) (G:=G) (m:=m) (i:=i)
      T H e.2 ticket L x hL hi z (Real.exp_nonneg (t * Model.capacity S.patch)) scale

noncomputable def bandsP (p: Site f): Q→ℝ:= let y:= S.ratio.parent p; if S.ratio.embed y=p then ∑ i:Axis,Bone S F H (y,i) else 0
lemma bandH (p:Site c):bandsP S F H (S.ratio.embed p)=∑ i:Axis,Bone S F H (p,i):=by unfold bandsP; rw[S.ratio.embed_parent,if_pos rfl]
lemma Bandage (hq:S.patch.Branches S.kernel G)(ht:0<t)(u:S.Choices): Pile S F H.b (∑ i:Axis, fieldCost H i t m) t m (fun x:Q=>noiseTaylor S (represent x.1) (fieldF F x.2) u) (bandsP S F H):=by
       refine ⟨fun {x} hx=> ?_,fun j x hp=>?_,fun j x hp i h=> ?_⟩
       · let Z: Finset (Site f):= image S.ratio.embed univ; rw [← sum_subset (subset_univ Z) (fun i _ hi=>?_)] -- may apply noise as sum first?
         · unfold noiseTaylor; rw [mul_sum,sum_image,Fintype.sum_prod_type]; refine sum_congr rfl (fun i _=>?_); rw [bandH, Finset.sum_apply]; exact sum_congr rfl fun j _=> boneLive S F H (i,j) x u hq hx
           intro i _ j _; exact fun h=> (show S.ratio.parent (S.ratio.embed i)=S.ratio.parent (S.ratio.embed j) from congr_arg _ h) |> fun p=> by rwa [S.ratio.embed_parent,S.ratio.embed_parent] at p
         unfold bandsP; rw [if_neg (fun h=>hi (mem_image.mpr ⟨_,mem_univ _,h⟩))]; rfl
       · unfold bandsP; dsimp only; split
         · simp_rw [show ∀ l, (∑ k:Axis, Bone S F H (l,k))=(fun a=>∑ k:Axis, Bone S F H (l,k) a) from fun l=> funext fun i=> Finset.sum_apply ..]; exact ContDiffAt.sum (fun v _=> boneRate S F H hp _)
         exact contDiffAt_const
       intro d c hc; unfold bandsP; dsimp only; split
       next hh=> rw [iteratedFDeriv_sum_apply (fun v _=>(boneRate S F H hp _).of_le le_top), _root_.sum_apply]; apply (norm_sum_le ..).trans; rw [sum_mul]; refine sum_le_sum (fun j' _=> boneCharge S F H hp ht (_,j') i h _ c ?_); exact hh.symm ▸ hc -- binder annotation
       unfold Radius.Polish.budget; have he: ‖iteratedFDeriv ℝ i (0:Q→ℝ) x d‖=0:=by
            by_cases hy:i=0; · subst i; rw [iteratedFDeriv_zero_apply]; exact norm_zero
            rw [show iteratedFDeriv ℝ i (0:Q→ℝ)= (0:_) from iteratedFDeriv_const_of_ne hy (c:= (0:ℝ)), Pi.zero_apply, _root_.zero_apply,norm_zero]
       rw [he]; exact mul_nonneg (sum_nonneg (fun i _=>fieldPos H i)) (prod_nonneg (fun i _=>(hc i).1))
end Dew
end YM.OPE.Zeph
