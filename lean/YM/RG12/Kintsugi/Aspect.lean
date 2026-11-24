import YM.RG12.Kintsugi.Cup
/-!
# Tensor pencils in exact d=4 field spaces: finite detecting curls
-/
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 250000
namespace YM.RG12.Kintsugi
open Function Filter Finset Set Analysis Spec Org Climb Table Next.UVStress UVNext.FreeStress Work.A01 Maxwell MeasureTheory
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{L:Register G}{S:Table L}(H:S.RealSpin)
-- repair export syntax for later mass-control. The free norm cost only at endpoints.
def linespace : Submodule ℝ (Auspect S) where
   carrier := {x|Peal H x}
   zero_mem' := ⟨fun _ _=>rfl, fun _ _ _=> (star_zero _).symm, fun _ _ _ _=> (smul_zero _).symm,fun _=> Finset.sum_const_zero (M:=ℂ)⟩
   add_mem' {A B} hA hB:=by
     obtain ⟨ha,hb,hc,hd⟩ := (show Peal H A from hA)
     obtain ⟨ma,mb,mc,md⟩ := (show Peal H B from hB)
     constructor
     · intro i j; exact congr_arg₂ (fun a b: S.Field 4→L[ℂ] ℂ=>a+b) (ha i j) (ma i j)
     · intro i j v; simp only [Pi.add_apply,_root_.add_apply,hb i j v,mb i j v,star_add]
     · intro k i j v; simp only [Pi.add_apply,_root_.add_apply,hc k i j v,mc k i j v,smul_add]
     intro v; simp only [Pi.add_apply,_root_.add_apply,sum_add_distrib,hd v,md v,add_zero]
   smul_mem' c {A} hA:=by
     obtain ⟨ha,hb,hc,hd⟩ := (show Peal H A from hA)
     constructor
     · intro i j; exact congr_arg (c • ·) (ha i j)
     · intro i j v; simp only [Pi.smul_apply,_root_.smul_apply,hb i j v]; simp [Complex.real_smul]
     · intro k i j v; simp only [Pi.smul_apply,_root_.smul_apply,hc k i j v]; exact smul_comm ..
     intro v; simp only [Pi.smul_apply,_root_.smul_apply,← Finset.smul_sum,hd v,smul_zero]

abbrev Rarity (f:Auspect S)(i j:Axis) : S.Field 4 →ₗ[ℝ] ℝ:=Complex.reCLM.toLinearMap.comp ((f i j).restrictScalars ℝ).toLinearMap
variable {C:Family G}(T:MaxwellData C)
local notation "B!"=>Bel C.book
local notation "F!"=>C.book.grid
set_option quotPrecheck false
local notation "V!"=>(B!).Field 4
local notation "h!"=>T.hT.spin

lemma means {L:Register G}{W:Table L}(h:W.Hierarchy){X:W.Stress}(hX:RawTensor h.spin X)(hs:∑ i:Axis,X i i=0) (a b:Axis): expectation W 4 (X a b)=0:=by
   have h0 (x:W.Field 4)(k:Signed) : expectation W 4 (W.mirror h.spin 4 k x)=expectation W 4 x:=by
      have hc:= mirror_center h x k
      rw [value_center,value_center,map_sub,map_smul,W.mirror_unit,sub_right_inj] at hc
      exact (smul_left_injective ℂ (W.alive 4 h.laws) hc).symm
   have h1:=on_scalar (E:=ℂ) (fun i j=>expectation W 4 (X i j)) (fun k i j=>by
      rw [← h0 (X i j) k,tensor_column hX,map_smul,Complex.coe_smul]) (by rw [← map_sum,hs,map_zero])
   exact congr_fun (congr_fun h1 a) b
lemma traced_light (hG:G.Simple) {W:(B!).Stress}(hW:W∈SymSpace (h!))(h₁:∑ i:Axis,W i i=0) (a b:Axis):∃ t:ℝ,W a b = t • (canonicalStress (F!) a b):=by
   let X : KernelSpace (h!) :=⟨W,kernel_mem.mpr ⟨hW,means T.hT (sym_mem.mp hW).2.2 h₁⟩⟩
   obtain ⟨x,hx⟩:= (mixed_space (F!) (h!) hG T.T.W T.lit.pales T.lit.hers).2 X
   have hu : W=x.1 • east (F!) + x.2.1 • west (F!) + x.2.2 • UVNext.FreeStress.across (F!):=
     Eq.symm (congr_arg Subtype.val hx)
   rcases eq_or_ne a b with rfl|h₀
   · have hg : (∑ i:Axis,W i i) =(x.1+2*x.2.1) • (total (F!)):=by rw [hu]; exact Trace.paint_sum (C:=C) ..
     have ht := Trace.total_ne_zero (C:=C) hG
     have he:x.1 + 2*x.2.1 = 0:= (smul_eq_zero.mp (h₁ ▸ hg.symm)).resolve_right ht
     refine ⟨2*x.1,?_⟩ -- x.2.1=-x.1/2. total = 2near+far, canonical = near/2-far/4 -> W=x.1*(near -far/2) = 2*x.1*canonical
     rw [hu,show x.2.1=-x.1/2 from by linarith only [he],canonicalStress,east,west,total_at _ a];
     simp only [Pi.add_apply,Pi.smul_apply,splitDiag,UVNext.FreeStress.across,if_true,near,smul_zero,add_zero,RCLike.real_smul_eq_coe_smul (K:=ℂ)];push_cast;module
   rw [hu]; exact ⟨x.2.2,by simp [h₀,east,west,UVNext.FreeStress.across,splitDiag,canonicalStress]⟩
variable (hG:G.Simple)
include hG
lemma arcs {A:Auspect (B!)} (h:Peal (h!) A) (he:∀ i j a b,(A i j) (canonicalStress (F!) a b)=0): A=0:=by
   choose v hv using fun i j=> (china_full T).2 (Rarity A i j)
   have hr(i j:Axis)(x:V!): china T (v i j) x=((A i j) x).re:=DFunLike.congr_fun (hv i j) x
   have ha : v ∈ SymSpace (h!):=by
      let m:= china T
      apply sym_mem.mpr
      refine ⟨fun i j=> (china_full T).1 (by rw [hv,hv]; unfold Rarity; rw [h.sym i j]), fun i j=> (china_full T).1 (LinearMap.ext (fun x=> ?_)),?_⟩
      · rw [swivels,hr,hr,h.were];simp
      apply column_tensor
      intro s i j
      rw [Complex.coe_smul]  -- goal
      apply (china_full T).1; apply LinearMap.ext; intro x
      rw [(china T).map_smul,LinearMap.smul_apply,scales,hr,hr,h.bars];simp [Complex.real_smul]
   have h₁ : ∑ i:Axis, v i i=0:=by
      refine (china_full T).1 (LinearMap.ext (fun x=>?_))
      rw [map_zero,LinearMap.zero_apply,map_sum,LinearMap.sum_apply]; simp_rw [hr,← Complex.re_sum _ _]; rw [h.track];rfl
   have ho i j:v i j=0:=by
      obtain ⟨t,hT⟩:=traced_light T hG ha h₁ i j
      by_contra! hU
      have hT':= ruby T hU
      rw [hr] at hT'
      exfalso
      rw [hT, (show ∀ u, A i j (t • u)= t • A i j u from fun u=> ((A i j).restrictScalars ℝ).map_smul t u), he,smul_zero,Complex.zero_re] at hT'; exact lt_irrefl _ hT'
   funext i j; apply ContinuousLinearMap.ext; intro x
   have hh(x):((A i j) x).re=0:=by rw [← hr,ho,map_zero,LinearMap.zero_apply]
   have hm:=hh (Complex.I • x);rw [map_smul,smul_eq_mul] at hm
   apply Complex.ext; exact hh x
   simpa using hm
-- moving prices: exact energy-sector representation cost measured in free angular apertures
variable (X : Scaling S){M:S.Hierarchy}
-- normalize physical row transported Y, only evaluate the *invariant* test family in exact energy positions.
def scope (J:(B!).Stress):linespace (h!)→ₗ[ℝ] (Axis→Axis→Axis→Axis→ℂ):={
   toFun A i j a b:=A.val i j (J a b)
   map_add' := by intro; intros; rfl
   map_smul' := by intro; intros; rfl }
lemma scope_suffices : Function.Injective (scope T (canonicalStress (F!))) := by
   intro x y hw
   have hh : scope T (canonicalStress (F!)) (x-y)=0:= ((scope T (canonicalStress (F!))).map_sub x y).trans (hw ▸ (sub_self _))
   exact sub_eq_zero.mp (Subtype.ext (arcs T hG (x-y).property (fun i j a b=>congr_fun (congr_fun (congr_fun (congr_fun hh i) j) a) b)))
end YM.RG12.Kintsugi
