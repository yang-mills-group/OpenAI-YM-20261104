import YM.Integration.WilsonSeparatedPrefixMovingExteriorTranslation
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Lac
import Mathlib.Analysis.Calculus.Taylor

/-! Moving the center on an admitted exterior costs a finite-order spatial
Taylor remainder on all entries of its original held test volume. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingExteriorTaylor
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonCoeffUV.Layout
open WilsonIndependentFittedExteriorProfile (home)
open WilsonIndependentMatchedCoverProfile (word)

open Set
open scoped ContDiff
variable {D k j:ℕ}

def sectionAt (φ:Rarity (D+k+1)):Rarity D where
  ψ:=⟨φ.ψ.val,scribble φ.ψ (by omega)⟩
  radius:=φ.radius
  markG:=φ.markG
  support:=φ.support

def jet (g:Point4→ℝ)(x v:Point4)(k:ℕ):ℝ:=
  taylorWithinEval (fun τ:ℝ=>g (x+τ • v)) k (Icc 0 1) 0 1

private theorem ray {f:Point4→ℝ}(k:ℕ)(x v:Point4)(s:ℝ)(smooth:ContDiffAt ℝ k f (x+s • v)):
    iteratedDeriv k (fun t:ℝ=>f (x+t • v)) s=iteratedFDeriv ℝ k f (x+s • v) (fun _=>v):=by
  let L:=ContinuousLinearMap.toSpanSingleton ℝ v
  let g:=fun z:Point4=>f (x+z)
  have shifted:ContDiffAt ℝ k g (L s):=smooth.comp (L s) (contDiffAt_const.add contDiffAt_id)
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ k (g ∘ L) s (fun _=>1)=_
  rw [YM.ConnectedActivityE6.Blaze.linear_pull L shifted]
  simp [g,L,ContinuousMultilinearMap.compContinuousLinearMap_apply,iteratedFDeriv_comp_add_left]

private theorem line (g:Point4→ℝ)(smooth:ContDiff ℝ (k+1:ℕ) g)(M:ℝ)(pos:0≤M)
    (bill:∀x,‖iteratedFDeriv ℝ (k+1) g x‖ ≤ M)(x v:Point4):
    ‖g (x+v)-jet g x v k‖ ≤ M*‖v‖^(k+1):=by
  let F:=fun t:ℝ=>g (x+t • v)
  have sf:ContDiff ℝ (k+1:ℕ) F:=smooth.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hb (t:ℝ)(ht:t∈Icc (0:ℝ) 1):
      ‖iteratedDerivWithin (k+1) F (Icc 0 1) t‖ ≤ M*‖v‖^(k+1):=by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one) sf.contDiffAt ht,
      show iteratedDeriv (k+1) F t=_ from ray _ x v t smooth.contDiffAt]
    apply ((iteratedFDeriv ℝ (k+1) g (x+t • v)).le_opNorm _).trans
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      (mul_le_mul_of_nonneg_right (bill (x+t • v)) (pow_nonneg (norm_nonneg v) (k+1)))
  have h:=taylor_mean_remainder_bound (n:=k) zero_le_one sf.contDiffOn
    (right_mem_Icc.mpr (zero_le_one: (0:ℝ)≤1)) hb
  simp only [sub_zero,one_pow,mul_one] at h
  simpa only [F,one_smul,jet] using h.trans (div_le_self (mul_nonneg pos
    (pow_nonneg (norm_nonneg v) _)) (by exact_mod_cast k.factorial_pos))

theorem wallet (φ:Rarity (D+k+1)):
    ∃ M:ℝ,0≤M ∧ ∀(j:ℕ)(_hj:j ≤ D)(axes:Fin j→Axis),
      ContDiff ℝ (k+1:ℕ) (crease φ.ψ axes) ∧ ∀x,‖iteratedFDeriv ℝ (k+1) (crease φ.ψ axes) x‖≤M:=by
  classical
  have individual (v:Knob D):∃M:ℝ,0≤M ∧ ContDiff ℝ (k+1:ℕ) (crease φ.ψ v.2) ∧
      ∀x,‖iteratedFDeriv ℝ (k+1) (crease φ.ψ v.2) x‖≤M:=by
    let g:=crease φ.ψ v.2
    have smooth:ContDiff ℝ (k+1:ℕ) g:=
      (ContinuousMultilinearMap.apply ℝ (fun _:Fin v.1.val=>Point4) ℝ (Embroider.dot ∘ v.2)).contDiff.comp
        ((scribble φ.ψ le_rfl).iteratedFDeriv_right (by exact_mod_cast (show k+1+v.1.val ≤ D+k+1 by omega)))
    have src:tsupport g⊆Metric.closedBall 0 φ.radius:=
      (closure_minimal (fun x hx=>φ.support (crestShelter x hx)) Metric.isClosed_closedBall)
    have compact:HasCompactSupport g:=(isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) src
    have cont:=smooth.continuous_iteratedFDeriv (m:=k+1) le_rfl
    have hsup:HasCompactSupport (iteratedFDeriv ℝ (k+1) g):=compact.iteratedFDeriv (k+1)
    obtain ⟨A,cap⟩:=hsup.exists_bound_of_continuousOn cont.continuousOn
    refine ⟨max 0 A,le_max_left ..,smooth,fun x=>?_⟩
    by_cases zero:iteratedFDeriv ℝ (k+1) g x=0
    · change ‖iteratedFDeriv ℝ (k+1) g x‖≤_;rw [zero,norm_zero];exact le_max_left ..
    exact (cap x (subset_closure zero)).trans (le_max_right ..)
  choose M nn smooth held using individual
  refine ⟨∑v,M v,Finset.sum_nonneg (fun v _=>nn v),?_⟩
  intro j hj a
  let v:Knob D:=⟨⟨j,Nat.lt_succ_of_le hj⟩,a⟩
  exact ⟨smooth v,fun x=>(held v x).trans (Finset.single_le_sum (fun u _=>nn u) (Finset.mem_univ v))⟩

theorem original (φ:Rarity (D+k+1)):
    ∃ M:ℝ,0≤M ∧ ∀j,∀hj:j≤D,∀(axes:Fin j→Axis)(ε y:ℝ)(_positive:0≤ε)(_fine:ε≤1)
      (root:Cover)(z o u:CellR),let x:=Mer.address ε y o root u.val
      let v:=-(y • (z.val-o.val))
      let page:=wheelC ε y root (sectionAt φ).ψ z
      ‖page.val ⟨⟨j,Nat.lt_succ_of_le hj⟩,axes⟩ u-ε^j*jet (crease φ.ψ axes) x v k‖≤M*|y|^(k+1):=by
  obtain ⟨M,nn,paid⟩:=wallet φ
  refine ⟨M,nn,?_⟩
  intro j hj axes ε y pos fine root z o u x v page
  obtain ⟨smooth,bill⟩:=paid j hj axes
  have distance:‖z.val-o.val‖≤1:=(norm_sub_le _ _).trans (by linarith [c_norm z,c_norm o])
  have nv:‖v‖≤|y|:=by
    dsimp only [v];rw [norm_neg,norm_smul,Real.norm_eq_abs];exact mul_le_of_le_one_right (abs_nonneg _) distance
  change ‖crease (sonal ε y z root (sectionAt φ).ψ) axes u.val-ε^j*jet _ _ _ _‖≤_
  rw [currentP _ _ _ _ _ _ hj]
  change ‖ε^j*crease φ.ψ axes (Mer.address ε y z root u.val)-ε^j*jet _ _ _ _‖≤_
  have moved:Mer.address ε y z root u.val=x+v:=by dsimp only [x,v,Mer.address,Mer.position];module
  rw [moved,←mul_sub,norm_mul,Real.norm_of_nonneg (pow_nonneg pos j)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ pos fine)).trans
    ((line _ smooth M nn bill x v).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) nv _) nn))

end YM.Integration.WilsonSeparatedPrefixMovingExteriorTaylor
