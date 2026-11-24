import YM.OPE.Compatible.Fathom.Chuck
import YM.OPE.Compatible.Straws.Stoop
/-!
# Polynomial test degree and scalar IBP. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cloud
open MeasureTheory Function Set Finset Filter Module
open scoped Topology BigOperators Classical ContDiff
open PertExtension Series Libra Stranded ScriptJ GaussianScore Flock Radial Silt
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {I J:Type}{i j k r:ℕ}
local notation "V!"=> Module.Dual ℝ E
variable {p q z:E→ℝ}
open Tensor Analysis ContinuousMultilinearMap
variable [MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E]
variable (μ:Measure E) [μ.IsAddHaarMeasure] (A:Law E)
def Dawn (f:E→ℝ)(x:E):ℝ:= A.average μ fun v=>f (v+x)
omit [μ.IsAddHaarMeasure][FiniteDimensional ℝ E][BorelSpace E] in
lemma dawn0 (f:E→ℝ): Dawn μ A f 0=A.average μ f:=by simp only [Dawn,add_zero]
lemma dawnB (h:Bond p):Bond (Dawn μ A p):=by
      apply Shift.retake μ A (p:=fun x:E×E=>p (x.2+x.1)); exact h.compLinear (LinearMap.snd ℝ E E+LinearMap.fst ℝ E E)
lemma dawnP (h:Bond p)(u:E):Analysis.D u (Dawn μ A p)=Dawn μ A (pointD u p):=by
      funext i; let f(x:ℝ×E):= p (x.2+(i+x.1 • u)); have hp: Bond f:=h.comp (w:=fun x:ℝ×E=> x.2+(i+x.1 • u)) fun a=>(by simp_rw[map_add,map_smul]; exact ((Bond.glyph (a.comp (LinearMap.snd ℝ ℝ E))).add ((Bond.keep _).add ((Bond.glyph (LinearMap.fst ℝ ℝ E)).mul (Bond.keep _)))))
      have ht:= hotrod μ A f hp 0; let L:=fun t:ℝ=>i+t • u; have hh(x:ℝ):HasDerivAt L u x:=by simpa [L] using! HasDerivAt.const_add i ((hasDerivAt_id' x).smul_const u)
      have hz:L 0=i:=by simp only [L,zero_smul,add_zero]
      have he(t:E): deriv (fun x:ℝ=>f (x,t)) 0= pointD u p (t+i):=by convert! (((h.smooth.differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt 0 ((hh 0).const_add t)).deriv using 1; unfold pointD; rw [← hz]
      simp_rw [he] at ht; have hk:= ((dawnB μ A h).smooth.differentiable (by simp) (L 0)).hasFDerivAt.comp_hasDerivAt 0 (hh 0); rw [hz] at hk; exact hk.unique ht
lemma prior (h:Bond p): Husk μ A j p ↔ ∀ k:ℕ,k < j→ coeff (Dawn μ A p) k 0=0:=by
       induction j generalizing p with
       | zero=> exact ⟨fun _ _ h=>by omega,fun _=>⟨h,by intro i hi;omega⟩⟩
       | succ j ih=>
           constructor
           · intro hp k hk; ext1 u; cases k with
             | zero=> rw [coeff_apply_zero]; erw [dawn0,hp.zeroH];rfl
             | succ k=>
                have ht:= (ih (p:=pointD (u 0) p) (h.amount _)).mp (hp.deriv (u 0)) k (by omega); rw [← Fin.cons_self_tail u, coeff_apply_cons ((dawnB μ A h).smooth.of_le le_top |>.contDiffAt), dawnP _ _ h,ht]; simp
           intro hp; apply Husk.foster h
           · have hh:= coeff_apply_zero (f:= Dawn μ A p) (x:=0) (fun _:Fin 0=>0); rw [hp 0 (by omega),dawn0] at hh; exact hh.symm
           intro a; apply (ih (h.amount a)).mpr; intro k hk; ext1 v; have hz:= DFunLike.congr_fun (hp (k+1) (by omega)) (Fin.cons a v); rw [coeff_apply_cons ((dawnB μ A h).smooth.of_le le_top |>.contDiffAt), dawnP _ _ h] at hz; change _*_=0 at hz; exact (mul_eq_zero.mp hz).resolve_left (by positivity)
end YM.OPE.Cloud
