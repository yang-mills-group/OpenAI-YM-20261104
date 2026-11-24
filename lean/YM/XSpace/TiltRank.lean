import YM.XSpace.OffAxis
import YM.XSpace.Photo
/-!
# Pivoting for odd charges, even before H symmetrization. Compact rank scopes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.AxesTangent
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick Normalize Structure1 Cirrus Future Photo
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {d n:ℕ} (A:FieldEnd G d)
def passT : FieldEnd G d:= (2:ℂ)⁻¹ • (A+((-1:ℂ) • Twos A))
lemma passL (p:Sec G d): passT A p=(2:ℂ)⁻¹ • (A p-hinge d (A (hinge d p))):=by unfold passT; simp only [LinearMap.smul_apply,LinearMap.add_apply,Twos,LinearMap.comp_apply, neg_one_smul, sub_eq_add_neg]
lemma pass_in (h:A∈ Tri G d): passT A∈Odd d:=by
  refine ⟨Submodule.smul_mem _ _ (Submodule.add_mem _ h (Submodule.smul_mem _ _ ?_)),fun p=>?_⟩
  · rw [tri_may]; exact ⟨by unfold Twos; simp only [LinearMap.comp_apply,hinge_leaf,(tri_may A).1 h|>.1,map_zero],fun l hl p hp=> mirror_ok _ (((tri_may A).1 h).2 l hl _ (mirror_ok _ hp))⟩
  unfold Twos; rw [LinearMap.comp_apply,LinearMap.comp_apply,passL,map_smul,hinges_back,map_sub,hinges_back,passL]; simp only [smul_sub]; abel
def SlotOdd (p:Tags G d n): Prop:= ∀ F:Point G d n,F (hinge d ∘ p)= -F p
lemma pass_into (u:Tags G d n)(F:Point G d n)(h:∀ x,F (hinge d ∘ x) =F x) : lot F (Twos A) u= lot F A (hinge d ∘ u):= by
  rw [lots,lots]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [← h]; apply congr_arg; funext j; by_cases ht:j=i; subst j; simp [Twos,hinges_back]; simp [ht]
lemma pass_even (u:Tags G d n)(F:Point G d n)(h:∀ x,F (hinge d ∘ x)=F x)(H:SlotOdd u): lot F A u=lot F (passT A) u:=by rw [passT,map_smul,map_add,map_smul, smul_apply,add_apply,smul_apply,pass_into _ u F h,H, smul_eq_mul, smul_eq_mul]; ring

variable (g:G.Simple)(hd:4≤d)
structure PotLin (G:Gauge)(d:ℕ) where
  n:ℕ
  p : Tags G d n
  w : Points n
  h : w∈conf n

abbrev Odds (G:Gauge)(d:ℕ):= ↥(Odd (G:=G) d)
instance : AddCommGroup (Odds G d):= @Submodule.addCommGroup ℂ (FieldEnd G d) _ _ _ _
instance : FiniteDimensional ℂ (Odds G d) := by exact FiniteDimensional.of_injective (V₂:= Module.End ℂ (Sec G d)) ((Odd d).subtype : (Odds G d)→ₗ[ℂ] FieldEnd G d) Subtype.val_injective

def meters (T:PotLin G d)(Q:Point G d T.n): Module.Dual ℂ (Odds G d) where
  toFun F:= lot Q F.val T.p
  map_add' F X:= by change lot Q (F.val+X.val) _= _+_; rw [map_add]; rfl
  map_smul' c X := by change lot Q (c • X.val) _= c • _; rw [map_smul]; rfl
abbrev showCase (T: PotLin G d):= meters T (scene T.w d)
structure Manages (c:Shade.Cut)(G: Gauge)(d:ℕ) : Prop where
  budget : ∃ (s:Finset (PotLin G d))(u:s→Odds G d), (∀ p:Odds G d,p=∑ i:s, showCase i.val p • u i) ∧ ∀ i:s,i.val.w∈ Good c i.val.n

include g hd in
lemma budgeting (V:Store G)(r:ℝ)(ha:0<r):∃ c:Shade.Cut,c.rOut<r ∧Granted V d c ∧ Manages c G d :=by
  obtain ⟨s,u,h⟩:= bought (showCase (d:=d) (G:=G)) (by
    intro x hx; apply Subtype.ext; refine odd_hush x.property g hd ?_; intro n z hz; ext1 p; exact hx (⟨n,p,z,hz⟩))
  obtain ⟨y,hr,hv,hX,hY⟩:=(show ∀ᶠ t:ℝ in nhdsWithin 0 (Ioi (0:ℝ)),(∀ i:Fin (V.survey d).n, tsupport ((V.survey d).scope i).t ⊆ Beyond t ((V.survey d).scope i).n) ∧ (∀ i:s,i.val.w∈ Beyond t i.val.n) ∧ (0<t) ∧ t<r from by
    have hi : ∀ i:s,∀ᶠ t:ℝ in nhdsWithin 0 (Ioi (0:ℝ)),i.val.w∈ Beyond t i.val.n:= fun i=> by simp_rw [← singleton_subset_iff]; exact wishes isCompact_singleton (singleton_subset_iff.mpr i.val.h)
    filter_upwards [eventually_all.mpr (fun i=> let t:= ((V.survey d).scope i).t; wishes (K:=tsupport t) t.hasCompactSupport t.tsupport_subset),eventually_all.mpr hi,self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0),eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds ha)] with i hi hu ht kv; exact ⟨hi,hu,ht,kv⟩).exists
  let c: Shade.Cut:=⟨y/2,y,by positivity,half_lt_self hX⟩; exact ⟨c,hY,hr,⟨s,u,h,hv⟩⟩

private lemma medium_limit {I:Type} [Fintype I] {ι:Type} {L:Filter ι} {E: Type} [AddCommGroup E][Module ℂ E][FiniteDimensional ℂ E]
    (b:I→ E)(p:I→Module.Dual ℂ E) (U:∀ x:E,(∑ i,p i x • b i)=x) (s:ι→ I→ Module.Dual ℂ E)(T:ι→ E) (H:∀ v i,Tendsto (fun j=> s j i v) L (𝓝 (p i v))) (hx:∀ i,Likely L (fun j=> s j i (T j))): Still ℂ L T:=by
  let F:= Fin (Module.finrank ℂ E)→ℂ; let e: E ≃ₗ[ℂ] F:=(Module.finBasis ℂ _).equivFun; let W (p:I→Module.Dual ℂ E)(i:I): F→L[ℂ] ℂ:= LinearMap.toContinuousLinearMap (p i ∘ₗ e.symm.toLinearMap); let Fm(p:I→Module.Dual ℂ E): F→L[ℂ] F:= ∑ i,(W p i).smulRight (e (b i))
  have ht(p:I→Module.Dual ℂ E)(x:E): Fm p (e x)=e (∑ i,p i x • b i):=by simp [Fm,W]
  have he : ∀ i,Tendsto (fun j=> W (s j) i) L (𝓝 (W p i)):=by
    let B:=Module.finBasis ℂ F; let y(k):= (B.coord k).toContinuousLinearMap; have h(f:F→L[ℂ]ℂ): f=∑ k, (f (B k)) • y k:= by
      ext1 x; conv_lhs=> rw [← B.sum_repr x,map_sum]; skip
      rw [ContinuousLinearMap.sum_apply]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [map_smul, ContinuousLinearMap.smul_apply]; exact mul_comm ..
    intro i; rw [h (W p i)]; conv => arg 1; ext j; rw [h (W (s j) i)]
    apply tendsto_finsetSum; intro k _; apply Tendsto.smul_const; exact H (e.symm (B k)) i -- simplify apply smul cos
  have hp : Tendsto (fun j=> Fm (s j)) L (𝓝 1):=by
    have h0:Fm p=1:=by
      ext1 x; obtain ⟨t,rfl⟩:=e.surjective x; rw [ht,U];rfl
    rw [← h0]; apply tendsto_finsetSum; intro i _; exact (ContinuousLinearMap.smulRightL ℂ F F|>.flip (e (b i))).continuous.continuousAt.tendsto.comp (he i) -- API
  let M:= Fm ∘ s; choose t hX using hx; let x:=∑ i,t i • b i
  have hj:Tendsto (fun j=> M j (e (T j))) L (𝓝 (e x)):= by simp_rw [M,Function.comp_apply,ht,map_sum,map_smul]; unfold x; rw [map_sum]; simp_rw [map_smul]; exact tendsto_finsetSum _ fun i _=> (hX i).smul_const _
  have hj0 : (1:F→L[ℂ]F).IsInvertible:=⟨ContinuousLinearEquiv.refl ℂ _,rfl⟩; have hm : Tendsto (fun i=> (M i).inverse) L (𝓝 1):=by
    rw [← show (1:F→L[ℂ]F).inverse = 1 from ContinuousLinearMap.inverse_equiv (.refl ℂ F)]; -- rewrites input? Tendsto
    exact ((hj0.contDiffAt_map_inverse (n:=1)).continuousAt).tendsto.comp hp
  have he': Tendsto (fun j=> e (T j)) L (𝓝 (e x)):=by
    have h: Tendsto (fun j=> (M j).inverse (M j (e (T j)))) L (𝓝 (e x)):= (Continuous.clm_apply continuous_fst continuous_snd).continuousAt (x:=((1:F→L[ℂ]F),e x))|>.tendsto.comp (hm.prodMk_nhds hj); apply h.congr'
    filter_upwards [hp.eventually (Units.isOpen.mem_nhds (show IsUnit (1:F→L[ℂ]F) from isUnit_one))] with i hi
    have he:= ContinuousLinearMap.isUnit_iff_bijective.mp hi; have hz : (M i).IsInvertible:=⟨ContinuousLinearEquiv.ofBijective (M i) (LinearMap.ker_eq_bot.mpr he.1) (LinearMap.range_eq_top.mpr he.2),rfl⟩; exact hz.inverse_apply_eq.mpr rfl
  refine ⟨x,fun L=>?_⟩; have h:= (L ∘ₗ e.symm.toLinearMap).continuous_of_finiteDimensional.continuousAt.tendsto.comp he'; simpa [Function.comp_def] using h

lemma Earned {ι:Type} {L:Filter ι}{K:Shade.Cut}(hm: Manages K G d)(T:ι→Odds G d)(s: (p:PotLin G d)→ι→Point G d p.n) (hs:∀ p,p.w∈Good K p.n→∀ w,Tendsto (fun i=>s p i w) L (𝓝 (scene p.w d w)))(he:∀ p,p.w∈Good K p.n→ Likely L fun i=> lot (s p i) (T i).val p.p): Still ℂ L T:=by -- vpassL
  obtain ⟨r,u,h,H⟩:= hm.budget; exact medium_limit (I:=r) u (fun i=> showCase i.val) (fun i=>(h _).symm) (fun i j=> meters j.val (s _ i)) T (fun T i=> by simp only [meters,LinearMap.coe_mk, AddHom.coe_mk,lots,showCase]; exact tendsto_finsetSum _ fun _ _=> hs i.val (H _) _) (fun i=>he i.val (H _))
end YM.XSpace.AxesTangent
