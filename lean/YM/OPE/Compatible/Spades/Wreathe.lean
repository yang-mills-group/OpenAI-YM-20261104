import YM.OPE.Compatible.Spades.Kame
import YM.OPE.Compatible.Anchor.Rook
/-!
# Wick coefficients for any smooth test with cut and grow
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Jargon
open MeasureTheory Function Set Finset Filter Module
open scoped Topology BigOperators Classical ContDiff ENNReal
open PertExtension Series Libra Stranded ScriptJ GaussianScore Flock Radial Silt Tensor Cloud
variable {E F X Y:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup X][NormedSpace ℝ X]{I J:Type}{i j k r:ℕ}{p q:E→ℝ}
local notation "Zw"=> Radial.zone (E:=E)
section
variable [FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E] (A:Law E)(μ:Measure E)[μ.IsAddHaarMeasure]
lemma RiseC (p:E→ℝ)(h:Bond p)(x:Fin k→E)(v:E) : iteratedFDeriv ℝ k (Dawn μ A p) v x=A.average μ (fun z=>Fline p x (z+v)):=by
       induction k generalizing p with
       | zero=> rw[iteratedFDeriv_zero_apply,Fline_zero];rfl
       | succ k ih=>
               let a:=x 0; let q:=Fin.tail x; rw[← Fin.cons_self_tail x]; rw [Analysis.cons_inner ((dawnB μ A h).smooth.of_le le_top |>.contDiffAt),dawnP μ A h,ih (pointD a p) (h.amount a) q]; exact congr_arg (A.average μ) (funext fun i=>Eq.symm (Analysis.cons_inner ((h.smooth.of_le le_top).contDiffAt) _ _)) -- order syntax
set_option linter.unusedSectionVars true in
lemma lane {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} {p : E → ℝ}
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (A : Law E) (μ : Measure E) [μ.IsAddHaarMeasure] [DecidableEq (Fin k)](h:Stature p k)(v:Fin k→E)(i:Fin k)(r s:E):Vas A μ p (update v i (r+s))=Vas A μ p (update v i r)+Vas A μ p (update v i s):=by
       let f(a):= Fline p (update v i a); have he:f (r+s)=f r+f s:=funext fun x=> (iteratedFDeriv ℝ _ p x).map_update_add ..; change A.average μ (f _) = _; rw [he,duneAdd A μ (runsV r) (runsV s)] ; rfl -- inspect
where runsV r': RunsG A μ (Fline p (update v i r')) := burlV A μ h le_rfl
lemma Soap (h:Stature p k): ∃ P:Pole E k,Sym P∧∀ x: Fin k→E,P x=Vas A μ p x:=by
       let V: MultilinearMap ℝ (fun _:Fin k=> E) ℝ:={toFun:=Vas A μ p,map_update_add':=lane A μ h,map_update_smul':=fun v i c x=> (show A.average μ _= _ from by rw [show Fline p _ = c • Fline p (update v i x) from funext fun x=> (iteratedFDeriv ℝ _ p x).map_update_smul ..,scooted];rfl)}
       obtain ⟨P,hp⟩:=Variance.wireEF (fun i:Fin k=>E) V; have he(x):P x=Vas A μ p x:=DFunLike.congr_fun hp x; refine ⟨P,fun x i=>?_,he⟩; rw [he,he]; exact congr_arg (A.average μ) (funext fun y=>Analysis.sym_Jet (h.smooth.contDiffAt) x i)
noncomputable def parcelW (h:Stature p k)(i:ℕ):Pole E i:= if hi:i≤k then ((i.factorial:ℝ)⁻¹) • (Soap A μ (h.mono hi)).choose else 0
lemma RootFib (h:Stature p k)(i:ℕ)(hi:i≤k)(x:Fin i→ E): parcelW A μ h i x=((i.factorial:ℝ)⁻¹)*Vas A μ p x:=by
       unfold parcelW; rw [dif_pos hi]; exact congr_arg (((i.factorial:ℝ)⁻¹)*·) ((Soap A μ (h.mono hi)).choose_spec.2 _)
lemma parcel_fit (h:Stature p k): parcelW A μ h ∈ harmon E k:=by
       refine ⟨fun i hi=>?_,fun i v s=>?_⟩; · unfold parcelW; rw[dif_neg (by omega)]
       unfold parcelW; by_cases hV:i ≤ k; · rw [dif_pos hV]; exact congr_arg (((i.factorial:ℝ)⁻¹) • ·) ((Soap A μ (h.mono hV)).choose_spec.1 v s)
       rw [dif_neg hV]; rfl
lemma veronica (p:E→ℝ)(hp:Bond p)(v:Fin i→E): coeff (Dawn μ A p) i 0 v=((i.factorial:ℝ)⁻¹)*Vas A μ p v:=by
       unfold coeff; simp only [smul_apply, RiseC A μ p hp v 0,add_zero];rfl
variable [Fintype I]
-- PAVER cq.E
open Cascade.Paver
lemma roster (L:Law (PAD I))(ν:Measure (PAD I))[ν.IsAddHaarMeasure](f:PAD I→ℝ)(hf:Stature f k) :
       let X:= Silt.chamber L (ContinuousLinearMap.id ℝ (PAD I)); let S:= parcelW L ν hf
       let g:=Strike k (Expire X S k); Haven ν L (k+1) (f-g):=by
       intro X S g; let R:=ContinuousLinearMap.id ℝ (PAD I)
       let F:= Expire X S k; have hs:S∈ harmon (PAD I) k:= parcel_fit ..; have he:F∈ harmon (PAD I) k:= peak _ _ _ _ hs; have hg:= sailCost F k; let T:=Stature.poly hg.cost k; apply (corresponding L ν k (hf.sub T)).2; intro i hi x; unfold Vas; rw[FlSub ((hf.mono hi).smooth) ((T.mono hi).smooth),duneSub L ν (burlV L ν hf hi) (burlV L ν T hi)]; apply sub_eq_zero.mpr; apply mul_left_cancel₀ (show ((i.factorial:ℝ)⁻¹)≠0 from by positivity)
       have hz:= under ν L R F he; change Dawn ν L g= (Strike k (LiftV X F k)) at hz; change ((i.factorial:ℝ)⁻¹)*Vas L ν f x=((i.factorial:ℝ)⁻¹)*Vas L ν g x; rw [←veronica L ν g hg.cost,hz,vigil _ _ hs, gradeC hs]; exact (RootFib L ν hf i hi x).symm
end
end YM.OPE.Jargon
