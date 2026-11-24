import YM.Integration.WilsonMarkedCompensatedReplant
import YM.Integration.WilsonPointChildCenteredCampaign
import YM.WilsonCoeffUV.Marked.Capture.LogCost

/-! The full ordinary deposited word is priced at capture before it is moved
into its one-name slot. The width may be narrowed to fit the actual cable. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMarkedOrdinaryCableSalary
open Function Filter Finset Lattice Wilson RG
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Soil WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas Stationary
open scoped Classical BigOperators
variable {G:Gauge}{ι:Type}[DecidableEq ι]{h k:ι→ℕ}

def wallet (S:Finset ι)(wage:Finset ι→ℝ):ℝ:=1+∑J∈S.powerset,|wage J|

def tariff (G:Gauge)(h k:ι→ℕ)(S:Finset ι)(E:ℕ):ℝ:=(formalO G h k S E).choose

theorem ordinary (S:Finset ι)(P:family G h)(auth:Eu k P)(empty:P ∅=0)(E:ℕ)
    (y:ι→ Cover)(wage:Finset ι→ℝ){w s D:ℝ}(wit:0 ≤ s)(strip:s ≤ w)(radius:0 ≤ D)
    (cable:∀a∈S,(terrain.gap 0 (y a):ℝ) ≤ D)
    (priced:∀J⊆S,∀e ≤ E,∀r,Wig terrain y w (wage J) J ((P J).2 e r))(e r:ℕ)(cap:e ≤ E):
    Cork terrain 0 s (tariff G h k S E*(wallet S wage*Real.exp (s*D))^S.card) ((levelsO P S).2 e r):=by
  let B:=wallet S wage*Real.exp (s*D)
  have expCost:1 ≤ Real.exp (s*D):=Real.one_le_exp (mul_nonneg wit radius)
  have floor:1 ≤ wallet S wage:=by simp only [wallet,le_add_iff_nonneg_right];positivity
  have large:1 ≤ B:=(one_mul (1:ℝ)).symm.le.trans (mul_le_mul floor expCost zero_le_one (zero_le_one.trans floor))
  apply (formalO G h k S E).choose_spec.2 B s (by linarith) wit P auth _ e cap r
  intro J sub d hd t
  by_cases active:J.Nonempty
  · obtain ⟨a,paid⟩:=active
    have pocket:|wage J| ≤ ∑i∈S.powerset,|wage i|:=Finset.single_le_sum (fun i _=>abs_nonneg (wage i)) (Finset.mem_powerset.mpr sub)
    have cover:wage J ≤ wallet S wage:=(le_abs_self _).trans (by dsimp [wallet];linarith)
    have root:=cLeaf y paid (cable a (sub paid)) wit ((priced J sub d hd t).shave strip)
    have budget:wage J*Real.exp (s*D) ≤ B:=mul_le_mul_of_nonneg_right cover (Real.exp_pos _).le
    exact root.cost (budget.trans (le_self_pow₀ large (by exact ne_of_gt (Finset.card_pos.mpr ⟨a,paid⟩))))
  · have zero:J=∅:=Finset.not_nonempty_iff_eq_empty.mp active
    subst J
    rw [empty]
    exact Cork.zero.cost (by simp)

theorem tested (S:Finset ι)(P:family G h)(f:Pen h S→L[ℝ]ℝ)(C:Era G ℝ)
    (s B A:ℝ)(e r:ℕ)(positive:Cork terrain 0 s B ((levelsO P S).2 e r))
    (subtrahend:Cork terrain 0 s A (C.2 e r)):
    Cork terrain 0 s (‖f‖*B+A) ((tuftV f (levelsO P S)-C).2 e r):=by
  have applied:Cork terrain 0 s (‖f‖*B) ((tuftV f (levelsO P S)).2 e r):=by
    refine ⟨mul_nonneg (norm_nonneg f) positive.1,?_⟩
    intro z
    change ‖f _‖ ≤ _
    exact (f.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (positive.2 z) (norm_nonneg f)).trans_eq (by ring))
  exact applied.sub subtrahend

end YM.Integration.WilsonMarkedOrdinaryCableSalary
end
