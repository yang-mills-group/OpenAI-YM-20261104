import YM.Integration.WilsonCommonConditionalGaussian
import YM.Integration.MSFixedRatioSaddleWick

/-! Finite conditional cubature in the original complex Gaussian reader,
with the entire translated marked source and the correct observing period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedOffsetGaussian
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Matrix Bloch
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Orb FormalBulk08.Series FormalBulk08.Reef
open FormalBulk08.Wick FormalBulk08.Kemp FormalBulk08.Lava FormalBulk08.Mesa
open Next.Free RG.Supply Work.F03 Work.F05 Work.F08 PowerSeries
open Planned.PrimaryIntegral295 Place Film Carrier Source Labels
open scoped BigOperators Classical Matrix

variable {G : Gauge} {K : KernelChoices} {D j t : ℕ}
    (P : Flight j t) (L : Lodge P.patch) (W : Pot G) (ρ : ChartRatio G)
    (branches : P.patch.Branches K G) (block : 2 ≤ P.L.val)

/-- All offset terms in the independently normalized marked step evaluated
by the original Gaussian used in the marked Wilson expansion. No support
or derivative directions have been identified across different torus sides. -/
theorem numerator (Y : Anthem D G) (h l : ℕ) (f : Dawn.Studio D) (n : Side)
    (tag : (primary P.patch K n).Choices) (B : wire G n → ℝ) (e : ℕ)
    (ratio : LocalRatio ρ) (order : 4 ≤ t)
    (leading : coeff 0 (Mesa.stone W (n*P.L)) = crunch (kernelP G K.penalty P.wing _)) :
    let H := Reef.ferry P branches L n
    let F := Reef.floor K P L n
    let U := Reef.flush F tag ρ (Mesa.stone W _)
    let T := WilsonFormalMarkedCubature.finiteTransfer P L W ρ branches block Y h l f n tag
    (MvPolynomial.eval B (coeff e (Orb.vocal H U * T)) : ℂ) =
      (Kemp.aven P.L h : ℂ) * ∑ x : Site P.L,
        Cumulants.Cloud.wick H.saddle.q (by ext i j; exact H.saddle.ok j i) 0
          (MvPolynomial.map Complex.ofRealHom (MvPolynomial.map (MvPolynomial.eval B)
            (coeff e (Series.expan (Orb.positive H U) * Orb.toInk H (Reef.seat F
              (Kemp.resite (wrap _ (lift x)) (Kemp.banner l (Y (Dawn.throughW x D block f)) _))))))) := by
  intro H F U T
  have h := WilsonMarkedFiniteWickDefect.numerator P L W ρ branches block Y h l f n tag ratio order leading
  change (MvPolynomial.eval B (coeff e (Orb.vocal H U * T)) : ℂ) = _
  rw [show Orb.vocal H U * T = _ from h,PowerSeries.coeff_C_mul,map_mul,MvPolynomial.eval_C,
    Complex.ofReal_mul]
  congr 1
  rw [map_sum,map_sum,Complex.ofReal_sum]
  apply sum_congr rfl
  intro x _
  exact (MSFixedRatioSaddleWick.coefficient H.saddle B _ e).symm

private theorem common {c s : Side} (S : StepData c s) (P : Flight j t)
    (L : Lodge P.patch) (b : P.patch.Branches K G) (hp : S.patch=P.patch)
    (hk : S.kernel=K) (row : PoleRows S.patch) (matchRows : HEq row (P.duo K.penalty).A0)
    (tag : (primary P.patch K c).Choices) :
    ∃ (F : Forest S.ratio) (a : S.Choices), HEq F (Reef.floor K P L c) ∧ HEq a tag ∧
      HEq (Flat.rawMean G S F (Bloch.installed S.ratio row))
        (Reef.pMean G K P c (Reef.floor K P L c)) ∧
      HEq ((Flat.testPrecision G S F P.wing)⁻¹) (Reef.ferry P b L c).saddle.q := by
  rcases S with ⟨p,k,hs⟩
  change p=P.patch at hp
  change k=K at hk
  subst p
  subst k
  have hs' : s=c*P.patch.L := Subtype.ext hs
  subst s
  obtain rfl := eq_of_heq matchRows
  let F := Reef.floor K P L c
  refine ⟨F,tag,HEq.rfl,HEq.rfl,HEq.rfl,heq_of_eq ?_⟩
  let T := Flat.testPrecision G (primary P.patch K c) F P.wing
  have ht := Reef.honey P b L c
  exact left_inv_eq_right_inv (Matrix.nonsing_inv_mul T (isUnit_iff_ne_zero.mpr ht.1.det_pos.ne')) ht.2

/-- For the independently prescribed forest and tag, exhibit the matching
original physical forest and tag on the actual observing mesh. Its covariance
in the formal coordinates is the literal saddle occurring in every offset
of the independently prescribed numerator above. -/
theorem onRun (R : Run G) (N i per : ℕ) (hi : i<N)
    (L : Lodge ((R.family.path.levels.clock.op i 0).patch))
    (tag : (R.family.path.levels.clock.op i per).Choices) :
    let V := R.family.path.levels
    let S := V.clock.op i per
    let P := destination V N i
    let n := R.family.S.side i per
    let b := (V.blocks i 0).branches
    let F₀ := Reef.floor V.clock.kernel P L n
    ∃ (F : Forest S.ratio) (a : S.Choices), HEq F F₀ ∧ HEq a tag ∧
      HEq (Flat.rawMean G S F (Bloch.installed S.ratio (P.duo V.clock.kernel.penalty).A0))
        (Reef.pMean G V.clock.kernel P n F₀) ∧
      HEq ((((RunFormalChain.fromRun R).step N i per hi).covariance F a).submatrix
        (Reef.pines F).symm (Reef.pines F).symm) (Reef.ferry P b L n).saddle.q := by
  intro V S P n b F₀
  obtain ⟨F,a,hF,ha,mean,cov⟩ := common (G:=G) S P L b rfl rfl (P.duo V.clock.kernel.penalty).A0 HEq.rfl tag
  refine ⟨F,a,hF,ha,mean,?_⟩
  let T := Flat.testPrecision G S F P.wing
  let E := Reef.pines (G:=G) F
  have inv : (T.submatrix E E)⁻¹ = T⁻¹.submatrix E E := by simp
  rw [WilsonCommonConditionalGaussian.covariance R N i per hi F a]
  change HEq (((T.submatrix E E)⁻¹).submatrix E.symm E.symm) _
  rw [inv,Matrix.submatrix_submatrix]
  simpa only [Equiv.self_comp_symm,Matrix.submatrix_id_id] using cov

end YM.Integration.WilsonMarkedOffsetGaussian
