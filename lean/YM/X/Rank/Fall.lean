import YM.X.Rank.Zoom
import YM.PertExtension.QuadraticSpan
import YM.X.Rank.Yield
/-!
Equality of all moments on real Wick basis generates exp(tX) stabilizer up to an orthogonal color change. `Frozen` all d.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.PositionX
open Pert Pert.Position Maxwell Wick Maxwell.Free Function Set Filter
open scoped Topology BigOperators Classical
variable {G : Gauge} (F: Labels.Frames G) {d : ℕ} (B:Buffer F d)
abbrev RealE (d : ℕ) := ↥(PertExtension.Quadratic.realField F (hierarchy F) d)
local notation "V" => RealE F d
set_option quotPrecheck false
instance {d}: NormedSpace ℝ (RealE F d):= by exact @Submodule.normedSpace ℝ ℝ _ _ _ (E F d) _ _ _ _ (PertExtension.Quadratic.realField F (hierarchy F) d)
local notation "C" => (Model F).conj (hierarchy F).spin d
instance {d} : CompleteSpace (RealE F d):= (PertExtension.Quadratic.realField F (hierarchy F) d |>.closed_of_finiteDimensional|>.completeSpace_coe)

def realop : V →L[ℝ] V :=
   let L:=PertExtension.Quadratic.realField F (hierarchy F) d
   (B.val.toLinearMap.comp L.subtype|>.codRestrict L (fun p=>show C (B.val p.val)=B.val p.val from (B.property.2.2.1 _).trans (congr_arg B.val p.property))).toContinuousLinearMap
lemma realop_eq (v:RealE F d) : (realop F B v).val=B.val v.val:= rfl

local instance : NormedRing (V →L[ℝ] V) := by exact ContinuousLinearMap.toNormedRing (𝕜:=ℝ) (E:=V)
local instance : NormedAlgebra ℝ (V→L[ℝ] V) := by exact ContinuousLinearMap.toNormedAlgebra (𝕜:=ℝ) (E:=V)
local instance : CompleteSpace (V→L[ℝ] V) := by infer_instance
def grad (v:V) (t:ℝ) := NormedSpace.exp (t • realop F B) v
@[simp] lemma grad_zero (v:V): grad F B v 0=v:= by unfold grad; rw [show (0:ℝ) • realop F B=0 from ContinuousLinearMap.ext (fun w=> by exact zero_smul ℝ (realop F B w)),NormedSpace.exp_zero]; rfl
lemma grad_move (v:V) (t:ℝ): HasDerivAt (grad F B v) (realop F B (grad F B v t)) t:=
   ((ContinuousLinearMap.apply ℝ (RealE F d) v).hasFDerivAt).comp_hasDerivAt t (hasDerivAt_exp_smul_const' (realop F B) t)
lemma grad_auto {v:V}(h:B.val v.val=0) (t:ℝ): grad F B v t=v:= by
   have hh : realop F B v=0:= Subtype.ext h
   have he (t:ℝ) : HasDerivAt (grad F B v) 0 t:= by
      convert! ((ContinuousLinearMap.apply ℝ (RealE F d) v).hasFDerivAt).comp_hasDerivAt t (hasDerivAt_exp_smul_const (realop F B) t) using 1
      change 0 = NormedSpace.exp (t • realop F B) (realop F B v); rw [hh,map_zero]
   exact (is_const_of_deriv_eq_zero (fun x=> (he x).differentiableAt) (fun x=> (he x).deriv) t 0).trans (grad_zero ..)
variable (h:Still F B)
def exposes {n d : ℕ} (x:Points n) : ContinuousMultilinearMap ℂ (fun _ : Fin n=>E F d) ℂ:=
   ⟨ visible F d x, by
      let W:=visible F d x; let X:=baring F d
      have he(p:Fin n→E F d): W p=∑ z:Fin n→ChartIx F d,(∏ i,X.coord (z i) (p i))* W (fun i=> X (z i)) := by
         conv_lhs=> rw [← funext fun j=> X.sum_equivFun (p j)]
         rw [MultilinearMap.map_sum_finset,Fintype.piFinset_univ]; exact Finset.sum_congr rfl fun i _ => MultilinearMap.map_smul_univ ..
      change Continuous (fun p=> W p); conv => arg 1; intro p; rw [he] -- potential loop he
      refine continuous_finset_sum _ (fun z _=> ?_); refine Continuous.mul_const ?_ _; exact continuous_finset_prod _ fun i _=> ((X.coord (z i)).toContinuousLinearMap.continuous.comp (continuous_apply i)) ⟩
include h
lemma grad_same {n} (p:Fin n→ V) (x:Points n)(hx:x∈conf n)(t:ℝ): visible F d x (fun i=> (grad F B (p i) t).val) = visible F d x (fun i=> (p i).val) := by
   let m:= (exposes F (d:=d) x).restrictScalars ℝ; let w(t:ℝ)(i:Fin n):=(grad F B (p i) t).val
   have hw t : HasDerivAt w (fun i=>B.val (w t i)) t:= by
      apply hasDerivAt_pi.mpr; intro i; let ht : RealE F d →L[ℝ] E F d:= (PertExtension.Quadratic.realField F (hierarchy F) d).subtypeL; exact ht.hasFDerivAt.comp_hasDerivAt (F:=V) t (grad_move F B (p i) t)
   have hz(t:ℝ):HasDerivAt (m ∘ w) 0 t:= by
      have he:= (m.hasFDerivAt _).comp_hasDerivAt t (hw t); rw [ContinuousMultilinearMap.linearDeriv_apply] at he; convert! he using 1; exact (h n _ x hx).symm
   have he:= is_const_of_deriv_eq_zero (fun t=> (hz t).differentiableAt) (fun t=> (hz t).deriv) t 0; change visible F d x _ = visible F d x (w 0) at he
   simpa only [w,grad_zero] using he

lemma fall (hd:4≤d)(hg:G.Simple) : B=0:= by
   have hZ : zoom F hd B=0:= Rigid.frozen_four F hg (zoom F hd B) (still_pre F hd h)
   let Z:= address F d
   let R (t:ℝ) (p q:WickPol G) := ∃ v:V,Z v.val=p∧ Z (grad F B v t).val=q
   have hr (t:ℝ) : Rank.Relation (R t):= by
      constructor
      · intro v; let p4 := team G v v; let a4 := (fields F 4).symm ⟨p4,team_label _ _ (by omega)⟩ -- uses `..`
        let a : E F d:= up F hd a4; have ha:Z a=p4:= (address_rise F _ hd a4).trans (congr_arg Subtype.val ((fields F 4).apply_symm_apply _))
        let p : V:=⟨a,show C a=a from address_inj F d ((address_star F a).trans (by unfold Z at ha; rw [ha]; exact realTeam ..))⟩
        refine ⟨p,ha,?_⟩; rw [grad_auto]; exact ha; change B.val (up F hd a4)=_; rw [← zoom_eq,hZ,show (0:Buffer F 4).val a4= (0:E F 4) from rfl,map_zero]
      · intro n x p q hx he; choose P hP he using he
        calc
          _ = moment G x (address F d ∘ fun i=> (P i).val) := congr_arg _ (funext fun i=> (hP i).symm)
          _ = _ := (visible_eq F _ x).symm.trans ((grad_same F B h P x hx t).symm.trans ((visible_eq F _ x).trans (congr_arg _ (funext he))))
   obtain ⟨u,hu⟩:= (@Filter.exists_seq_tendsto ℝ (𝓝[≠] (0:ℝ)) _ _) -- check
   let p (v:V):= Z v.val; let q n (v:V):= p (grad F B v (u n)); have hp (v:V): Painted (p v)∧realForm (p v)=p v := ⟨(sector.mp (address_in ..)).2,(address_star F v.val).symm.trans (congr_arg Z v.property)⟩
   have ht : ∃ᶠ n:ℕ in atTop,q n=p := by
      apply Rank.freezes (R:=fun n=>R (u n)) hg p hp q (fun n v=>⟨(hp (grad F B v _)).1,(hp (grad F B v _)).2,v,rfl,rfl⟩) (fun n=> hr (u n))
      intro v A; let L:= ((Rank.helps A).toLinearMap.comp Z).toContinuousLinearMap
      exact ((L.continuous.continuousAt (x:=v.val)).tendsto).comp ((continuous_subtype_val.continuousAt (x:=v)).tendsto.comp ((show Tendsto (grad F B v) _ (𝓝 v) from (by simpa only [grad_zero] using! (HasDerivAt.continuousAt (F:=V) (grad_move F B v 0)).tendsto)).comp (hu.mono_right nhdsWithin_le_nhds)))
   have hR(v:V) : realop F B v=0:= by
      have hz:= (HasDerivAt.tendsto_slope (F:=RealE F d) (f:=grad F B v) (grad_move F B v 0)).comp hu; rw [grad_zero] at hz; apply tendsto_nhds_unique_of_frequently_eq hz (show Tendsto (fun _ : ℕ=> (0:V)) _ (𝓝 0) from tendsto_const_nhds); apply ht.mono; intro n h; have h': grad F B v (u n)=v:= Subtype.ext (address_inj F d (congr_fun h v)); simp [slope,h']
   have hf (v:E F d) (hv:C v=v) : B.val v=0:= congr_arg Subtype.val (hR ⟨v,hv⟩)
   ext1; ext1 v; change B.val v=0
   let a:= C v; have ha : C a=v:=Table.reflect_star ..
   have hh := hf (v+a) (by rw [map_add,ha,add_comm]); have ht:=hf (Complex.I • (v-a)) (by simp only [map_smulₛₗ,map_sub,ha,Complex.conj_I];change (-Complex.I) • (a-v)=_;rw [neg_smul, ← smul_neg,neg_sub])
   rw [B.property.2.2.2.2] at ht; replace ht:= (smul_eq_zero.mp ht).resolve_left Complex.I_ne_zero; rw [map_sub] at ht; rw [map_add,←sub_eq_zero.mp ht,← two_smul ℂ] at hh; exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
omit B h
/-- Infinitesimal stabilizer of separated free correlations = zero, all horizons. -/
lemma frozen (d : ℕ) (h : G.Simple) : Pert.Position.Frozen F d :=
   if H:4≤d then fun B b=> fall F B b H h else Rigid.first_frozen F h (not_le.mp H)
end YM.PositionX
