import YM.OPE.Compatible.Juniper.Carve
/-!
# W costs independent of frame dim. explicit
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}{C:KernelChoices}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin
local notation "Fλ"=> fieldX (Shade G)
section
variable [NormedAddCommGroup E][NormedSpace ℝ E]
variable {p:E→ℝ}(v:JetS E)
noncomputable def Jpiece (p:E→ℝ): JetS ℝ := ⟨p v.s, Stranded.pointD v.l p v.s, Stranded.pointD v.h p v.s + 1/2* Stranded.pointD v.l (Stranded.pointD v.l p) v.s⟩
noncomputable def wheelD (v:JetS E)(t:ℝ) := v.l+(2*t) • v.h
lemma Jline (t:ℝ) : HasDerivAt v.atK (wheelD v t) t:=by
       unfold JetS.atK wheelD; convert! (((hasDerivAt_const t v.s).add ((hasDerivAt_id' t).smul_const _)).add (((hasDerivAt_id' t).pow 2).smul_const v.h)) using 1; simp
lemma Wwheel (t:ℝ): iteratedDeriv 2 v.atK t=(2:ℝ) • v.h:=by
       rw[show iteratedDeriv 2 v.atK=deriv (iteratedDeriv 1 v.atK) from iteratedDeriv_succ ..,funext (show ∀ t:ℝ, iteratedDeriv 1 v.atK t=wheelD v t from fun i=>by rw[iteratedDeriv_one,(Jline v i).deriv])]; exact HasDerivAt.deriv (by simpa only [mul_one] using! (((hasDerivAt_id' t).const_mul 2).smul_const v.h).const_add v.l)
lemma kernelS: ContDiff ℝ ⊤ v.atK:=contDiff_iff_contDiffAt.mpr fun _=> (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)).add ((contDiffAt_id.pow 2).smul contDiffAt_const)
lemma brightX (h:ContDiff ℝ 2 p)(q:Phase): WardBin.leading q.val (p ∘ v.atK)= (Jpiece v p).seq q.val:=by
       have hy : v.atK 0=v.s:= by simp [JetS.atK]
       have hp: wheelD v 0=v.l:=by simp [wheelD]
       fin_cases q
       · simp [WardBin.leading,hy];rfl
       · change (↑((1:ℕ).factorial):ℝ)⁻¹ • iteratedDeriv 1 (p ∘ v.atK) 0=Stranded.pointD v.l p v.s; rw [iteratedDeriv_one, show deriv (p ∘ v.atK) _= _ from (((h.differentiable (by norm_num) _).hasFDerivAt).comp_hasDerivAt 0 (Jline v _)).deriv,hy,hp]; simp [Stranded.pointD]
       change (↑((2:ℕ).factorial):ℝ)⁻¹ *iteratedDeriv 2 (p ∘ v.atK) 0=_; rw[iteratedDeriv_vcomp_two h.contDiffAt ((kernelS v).contDiffAt.of_le le_top), (Jline v _).deriv,Wwheel,hy,hp,map_smul]
       have he: iteratedFDeriv ℝ 2 p v.s (fun _=>v.l)=Stranded.pointD v.l (Stranded.pointD v.l p) v.s:=by
            let q:=fun _ : Fin 1=> v.l; rw [show (fun _:Fin 2=>v.l)=Fin.cons v.l q from (by funext i;fin_cases i <;> rfl), Analysis.cons_inner (f:=p) (j:=1) (by exact_mod_cast h.contDiffAt),iteratedFDeriv_one_apply]; rfl -- names
       rw [he]; change _= Stranded.pointD v.h p v.s + 1/2* _ ; norm_num [Nat.factorial, Stranded.pointD];ring
omit v
lemma paceT (f:ℝ→ℝ)(t:ℝ)(ht:0<t)(k:ℕ)(hf:ContDiff ℝ (k+1:ℕ) f)(C:ℝ)(hh:0≤C)(hp:∀ v∈Icc 0 t,‖iteratedDeriv (k+1) f v‖≤C):
    ‖f t- ∑ i∈range (k+1), t^i * WardBin.leading i f‖ ≤ C*t^(k+1):=by
         have he(i:ℕ)(hi:i≤k+1)(x:ℝ)(hx:x∈Icc (0:ℝ) t): iteratedDerivWithin i f (Icc 0 t) x=iteratedDeriv i f x:=by rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Icc ht) ((hf.of_le (Nat.cast_le.mpr hi)).contDiffAt) hx,← iteratedDeriv_eq_iteratedFDeriv]
         have hg:= taylor_mean_remainder_bound (n:=k) (f:=f) ht.le hf.contDiffOn (right_mem_Icc.mpr ht.le) (C:=C) fun i hi=>by rw [he _ le_rfl _ hi]; exact hp i hi
         have hz:taylorWithinEval f k (Icc 0 t) 0 t=∑ i∈range (k+1), t^i* WardBin.leading i f:=by rw [taylor_within_apply]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [he _ (mem_range.mp hi|>.le) 0 (left_mem_Icc.mpr ht.le),sub_zero]; simp only [smul_eq_mul,WardBin.leading]; ring
         rw [← hz]; rw [sub_zero] at hg; exact hg.trans ((div_le_iff₀ (by exact_mod_cast k.factorial_pos)).mpr (le_mul_of_one_le_right (by positivity) (by exact_mod_cast k.factorial_pos)))
end
end YM.OPE.Spells
