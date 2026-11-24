import YM.Integration.WilsonSeparatedPrefixMovingExteriorVolume
import Mathlib.Algebra.Order.Round

/-! The signed difference between the translated exterior and its retained
Cartesian profiles is a genuine compact Rarity with its full smooth income. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingExteriorRemainder
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical ContDiff
open WilsonCoeffUV.Layout
open WilsonSeparatedPrefixMovingExteriorTaylor (sectionAt)
open WilsonSeparatedPrefixMovingCenterMoments (monomial)
open WilsonSeparatedPrefixMovingProfileDerivatives (cut)
open WilsonSeparatedPrefixMovingExteriorVolume (printed layer)
open WilsonSeparatedPrefixMovingExteriorTranslation (moved)
variable {D k:ℕ}
def folded (φ:Rarity D)(hf:ContDiff ℝ ∞ φ.ψ.val)(y:ℝ)(z o:CellR)(L:ℕ):Scroll D:=
  ∑n∈Finset.range (L+1),((n.factorial:ℝ)⁻¹*(-y)^n) •
    ∑w:Fin n→Axis,monomial o w z • (cut φ hf w).ψ
private def point (x:Point4):Scroll D→ₗ[ℝ]ℝ where
  toFun:=fun f=>f.val x
  map_add':=by intros;rfl
  map_smul':=by intros;rfl
private theorem stretch (φ:Rarity D)(y:ℝ)(z o:CellR):φ.radius≤(moved φ y z o).radius:=by
  change φ.radius ≤ max 1 (‖y • (z.val-o.val)‖+φ.radius*1)
  rw [mul_one]
  exact (le_add_of_nonneg_left (norm_nonneg _)).trans (le_max_right ..)
def remainder (φ:Rarity D)(hf:ContDiff ℝ ∞ φ.ψ.val)(y:ℝ)(z o:CellR)(L:ℕ):Rarity D where
  ψ:=(moved φ y z o).ψ-folded φ hf y z o L
  radius:=(moved φ y z o).radius
  markG:=(moved φ y z o).markG
  support:=by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    by_contra outside
    have absent:(point x) (moved φ y z o).ψ=0:=by
      by_contra live;exact outside ((moved φ y z o).support (subset_closure live))
    have gone (n:ℕ)(w:Fin n→Axis):point x (cut φ hf w).ψ=0:=by
      by_contra live
      exact outside ((Metric.closedBall_subset_closedBall (stretch φ y z o)) ((cut φ hf w).support (subset_closure live)))
    change point x (_-folded φ hf y z o L)≠0 at hx
    simp [map_sub,folded,map_sum,map_smul,gone,absent] at hx
private def look (ε y:ℝ)(root:Cover)(o:CellR):Scroll D→ₗ[ℝ]Scroll D where
  toFun:=sonal ε y o root
  map_add':=by intros;apply Subtype.ext;rfl
  map_smul':=by intros;apply Subtype.ext;rfl
theorem registered (φ:Rarity D)(hf:ContDiff ℝ ∞ φ.ψ.val)(ε y:ℝ)(root:Cover)(z o:CellR)(L:ℕ):
    wheelC ε y root (remainder φ hf y z o L).ψ o=wheelC ε y root φ.ψ z-printed φ hf ε y root z o L:=by
  let P:Scroll D→ₗ[ℝ]Volume D:=(page D).comp (look ε y root o)
  change P ((moved φ y z o).ψ-folded φ hf y z o L)=_
  rw [map_sub,WilsonSeparatedPrefixMovingExteriorTranslation.wheel φ ε y root z o]
  unfold folded printed layer
  simp only [map_sum,map_smul];rfl
theorem location (x:Point4)(y:ℝ)(o:CellR):
    ∃(site:Cover)(u:CellR),Mer.address 1 y o site u.val=x:=by
  let atHome:=x+y • o.val
  let site:Cover:=fun a=>round (atHome a)
  let u:=atHome-Mer.actualW site
  have small:‖u‖≤(2:ℝ)⁻¹:=by
    apply (pi_norm_le_iff_of_nonneg (by norm_num:(0:ℝ)≤2⁻¹)).mpr
    intro a;change |atHome a-(round (atHome a):ℤ)|≤_
    simpa only [one_div] using abs_sub_round (atHome a)
  refine ⟨site,⟨u,Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using small)⟩,?_⟩
  unfold Mer.address Mer.position
  dsimp only [u,atHome];simp only [one_smul];module
theorem original (φ:Rarity (D+k+1))(hf:ContDiff ℝ ∞ φ.ψ.val):
    ∃M:ℝ,0≤M ∧ ∀(y:ℝ)(z o:CellR),Amplitude (remainder (sectionAt φ) hf y z o k) (M*|y|^(k+1)):=by
  obtain ⟨M,hm,receipt⟩:=WilsonSeparatedPrefixMovingExteriorVolume.original φ hf
  refine ⟨M,hm,?_⟩
  intro y z o;refine ⟨mul_nonneg hm (pow_nonneg (abs_nonneg _) _),?_⟩
  intro j hj a x
  obtain ⟨site,u,found⟩:=location x y o
  have bought:=receipt 1 y zero_le_one le_rfl site z o
  rw [←registered] at bought
  have sensed:=registry (wheelC 1 y site (remainder (sectionAt (D:=D) (k:=k) φ) hf y z o k).ψ o)
    ⟨⟨j,Nat.lt_succ_of_le hj⟩,a⟩ u
  change ‖crease (sonal 1 y o site _) a u.val‖≤_ at sensed
  rw [currentP _ _ _ _ _ _ hj,found,one_pow,one_mul] at sensed
  exact sensed.trans bought
theorem radius (φ:Rarity D)(hf:ContDiff ℝ ∞ φ.ψ.val)(y:ℝ)(z o:CellR)(L:ℕ):
    (remainder φ hf y z o L).radius≤φ.radius+|y|:=by
  change max 1 (‖y • (z.val-o.val)‖+φ.radius*1)≤_
  have bound:‖z.val-o.val‖≤1:=(norm_sub_le _ _).trans (by linarith [c_norm z,c_norm o])
  rw [norm_smul,Real.norm_eq_abs,mul_one]
  exact max_le (by linarith only [φ.markG,abs_nonneg y])
    (by linarith only [mul_le_of_le_one_right (abs_nonneg y) bound])
end YM.Integration.WilsonSeparatedPrefixMovingExteriorRemainder
