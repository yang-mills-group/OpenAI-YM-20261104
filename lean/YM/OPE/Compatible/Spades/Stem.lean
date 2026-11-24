import YM.OPE.Compatible.Spades.Wreathe
import YM.OPE.Compatible.Stamen.Thor
/-!
# Wick shrink singular support and exterior tangent transport
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Jargon
open MeasureTheory Function Set Finset Filter Module
open scoped Topology BigOperators Classical ContDiff ENNReal
open PertExtension Series Libra Stranded ScriptJ GaussianScore Flock Radial Silt Tensor Cloud
variable {E F X Y:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
variable {I J:Type}{i j k r:ℕ}{p q:F→ℝ}
local notation "Z!"=> Radial.zone (E:=E)
section
variable [FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E] (A:Law E)(μ:Measure E)[μ.IsAddHaarMeasure](S:E→L[ℝ] F)
noncomputable def stroll (p:F→ℝ)(x:F):= A.average μ (fun y=>p (x+S y))
lemma stC (h:Bond p): Bond (stroll A μ S p):=by
       apply Shift.retake μ A (p:=p ∘ (LinearMap.fst ℝ F E+S.toLinearMap ∘ₗ (LinearMap.snd ℝ F E))); exact h.compLinear _
lemma BigV (h:Bond p) (u:F):pointD u (stroll A μ S p)=stroll A μ S (pointD u p):=by
       funext x; let t(z:ℝ):=x+z • u; let f(y:ℝ × E):=p (t y.1+S y.2); have hp:Bond f:= h.comp (w:=fun y:ℝ×E=>t y.1+S y.2) fun a=>(by change Bond (fun i:ℝ×E=> a ((x+ i.1 • u)+S i.2)); simp_rw[map_add,map_smul]; exact ((Bond.keep _).add ((Bond.glyph (LinearMap.fst ℝ ℝ E)).mul (Bond.keep _))).add (Bond.glyph ((a.comp S.toLinearMap).comp (LinearMap.snd ℝ ℝ E))))
       have ht:=Silt.hotrod μ A f hp 0; have hh:HasDerivAt t u 0:=by simpa only [one_smul] using! HasDerivAt.const_add x ((hasDerivAt_id' (0:ℝ)).smul_const u)
       have hz:t 0=x:=by simp [t]
       have he(y:E): deriv (fun z:ℝ=> f (z,y)) 0= pointD u p (x+S y):=by convert! (((h.smooth.differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt 0 (hh.add_const (S y))).deriv using 1; unfold pointD; rw [hz]
       have hk:= ((stC A μ S h).smooth.differentiable (by simp) (t 0)).hasFDerivAt.comp_hasDerivAt 0 hh; rw [hz] at hk; simp_rw [he] at ht; exact hk.unique ht
abbrev taxA (p:F→ℝ)(x:Fin i→ F):ℝ:=A.average μ (Fline p x ∘ S)
lemma Soul (p:F→ℝ)(h:Bond p)(x:Fin k→F)(v:F) : iteratedFDeriv ℝ k (stroll A μ S p) v x=A.average μ (fun z=>Fline p x (v+S z)):=by
       induction k generalizing p with
       | zero=> rw[iteratedFDeriv_zero_apply,Fline_zero];rfl
       | succ k ih=>
               let a:=x 0; let q:=Fin.tail x; rw [← Fin.cons_self_tail x, Analysis.cons_inner ((stC A μ S h).smooth.of_le le_top|>.contDiffAt), show Analysis.D a (stroll A μ S p)= _ from BigV A μ S h a,ih (pointD a p) (h.amount a) q]; exact congr_arg (A.average μ) (funext fun i=>Eq.symm (Analysis.cons_inner ((h.smooth.of_le le_top).contDiffAt) _ _))
lemma boundY (p:F→ℝ)(hp:Bond p)(v:Fin i→F): coeff (stroll A μ S p) i 0 v=((i.factorial:ℝ)⁻¹)*taxA A μ S p v:=by
       unfold coeff; simp only [smul_apply,Soul A μ S p hp v 0,zero_add]; rfl
omit [FiniteDimensional ℝ F] in
lemma exil (h: Stature p k)(x:Fin k→F):RunsG A μ (Fline p x ∘ S):=A.integrable_entry μ (CarriedL (h.card le_rfl x) S) ((h.pic le_rfl).comp S.continuous)
omit [FiniteDimensional ℝ F] in
lemma popL [DecidableEq (Fin k)](h: Stature p k)(x:Fin k→F)(i:Fin k)(u v:F):taxA A μ S p (update x i (u+v))= taxA A μ S p (update x i u)+taxA A μ S p (update x i v):=by
       let f(y):=Fline p (update x i y) ∘ S; rw [show taxA A μ S p (update x i (u+v))=A.average μ (f u+f v) from congr_arg (A.average μ) (funext fun w=> (iteratedFDeriv ℝ k p _).map_update_add ..)]; exact duneAdd A μ (exil A μ S h _) (exil A μ S h _)
lemma StampG (h:Stature p k):∃ P:Pole F k,Sym P ∧∀ x,P x=taxA A μ S p x:=by
       let U: MultilinearMap ℝ (fun _:Fin k=> F) ℝ:={toFun:=taxA A μ S p,map_update_add':=popL A μ S h,map_update_smul':=fun v i c x=> (show A.average μ _= _ from by rw [show Fline p (update v i _) ∘ S= c • (Fline p (update v i x) ∘ S) from funext fun y=> (iteratedFDeriv ℝ _ p (S y)).map_update_smul ..,scooted];rfl)}
       obtain ⟨P,hp⟩:=Variance.wireEF (fun _:Fin k=> F) U; have he(x): P x=taxA A μ S p x:=DFunLike.congr_fun hp x; refine ⟨P,fun x i=>?_,he⟩; rw[he,he]; exact congr_arg (A.average μ) (funext fun y=>Analysis.sym_Jet (x:=S y) h.smooth.contDiffAt x i)
noncomputable def FarG (h:Stature p k)(i:ℕ):Pole F i:= if hi:i≤k then ((i.factorial:ℝ)⁻¹) • (StampG A μ S (h.mono hi)).choose else 0
lemma SemG (h:Stature p k)(i:ℕ)(hi:i≤k)(x:Fin i→ F): FarG A μ S h i x=((i.factorial:ℝ)⁻¹)*taxA A μ S p x:=by
       unfold FarG; rw [dif_pos hi]; exact congr_arg (((i.factorial:ℝ)⁻¹)*·) ((StampG A μ S (h.mono hi)).choose_spec.2 _)
lemma WealthF (h:Stature p k): FarG A μ S h ∈ harmon F k:=by
       refine ⟨fun i hi=>?_,fun i v s=>?_⟩; · unfold FarG; rw[dif_neg (by omega)]
       unfold FarG; by_cases hV:i ≤ k; · rw [dif_pos hV]; exact congr_arg (((i.factorial:ℝ)⁻¹) • ·) ((StampG A μ S (h.mono hV)).choose_spec.1 v s)
       rw [dif_neg hV]; rfl
end
end YM.OPE.Jargon
