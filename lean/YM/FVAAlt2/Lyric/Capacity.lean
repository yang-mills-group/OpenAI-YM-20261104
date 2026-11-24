import YM.RegulatorIR.Binding.Rafter
import YM.Comparison.RG02.Assembly.Core
/-!
# Padded Gaussian bank.L. Allows native φ direction counting in passport,
 including singular covariance on full finite torus. No infinite-volume.
 New file adapting from `YM/RG02/Needle/Imagine` with arbitrary insertion matrix and soft burn uses public RegulatorIR.Diagram.Wick (using real Laplace.From Canon elsewhere)
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Lyric.Capacity
open Function Filter Set MeasureTheory Matrix Metric Lattice
open PertExtension PertExtension.Series GaussianScore
open Next.SectorChange Next.SectorChange.Gaussian
open Diagram -- Gaussian collisions
open scoped Topology Classical Matrix.Norms.Frobenius BigOperators ContDiff ENNReal Matrix PowerSeries
variable {I X:Type}[Fintype I][DecidableEq I]
-- linear support
variable (A:Matrix I I ℝ)(hA:A.PosDef)
def scored : (I→ℝ) →ₗ[ℝ] Module.Dual ℝ (I→ℝ) := {
    toFun y:= { toFun x:= dotProduct y (A *ᵥ x), map_add' a b:=by rw [Matrix.mulVec_add,dotProduct_add], map_smul' z x:= by rw [Matrix.mulVec_smul,dotProduct_smul]; rfl }
    map_add' y x:= by ext z; exact add_dotProduct ..
    map_smul' z x:=by ext a; exact smul_dotProduct .. }
lemma smooth_score : Continuous (fun i=> scored A i i):=by
    change Continuous fun i:I→ℝ=> ∑ k:I, i k * ∑ j:I, A k j * i j; fun_prop
include hA
private lemma light : ∃ c>0,∀ x, c*‖x‖^2 ≤ scored A x x/2 :=by
    by_cases h : Nonempty I
    · obtain ⟨i⟩:=h
      let L(x:I→ℝ):= scored A x x/2
      have hv : Continuous L := (smooth_score A).div_const _
      obtain ⟨x,hx,ht⟩:= (isCompact_sphere (0:I→ℝ) 1).exists_isMinOn (show (sphere (0:I→ℝ) 1).Nonempty from ⟨Pi.single i 1,by simp [Pi.norm_single]⟩) hv.continuousOn
      have h' : x≠0:= fun t=>by rw [t] at hx; simp at hx
      have hl : 0 < L x := half_pos (show 0 < scored A x x from (by simpa only [scored,LinearMap.coe_mk,AddHom.coe_mk, star_trivial] using (posDef_iff_dotProduct_mulVec.mp hA).2 h'))
      refine ⟨L x,hl,?_⟩
      intro y; by_cases hy:y=0; · simp [hy]
      have he:= norm_pos_iff.mpr hy
      have ha : ‖y‖⁻¹ • y ∈ sphere (0:I→ℝ) 1 := by simp [norm_smul,inv_mul_cancel₀ he.ne']
      have hL : L x ≤ L (‖y‖⁻¹ • y):=ht ha
      rw [show L (‖y‖⁻¹ • y)= L y/‖y‖^2 from ?_] at hL; swap
      · unfold L; simp only [map_smul,LinearMap.smul_apply, smul_eq_mul]; field_simp
      exact (le_div_iff₀ (by positivity)).mp hL
    refine ⟨1,zero_lt_one,fun x=>?_⟩
    have hx:x=0:= funext fun i=>False.elim (h ⟨i⟩); simp [hx]

def origin : Law (I→ℝ) where
    P:=scored A⁻¹
    turns x y:= by
      have hv := dotProduct_transpose_mulVec A⁻¹ x y
      change x ⬝ᵥ (A⁻¹*ᵥ y)= y ⬝ᵥ (A⁻¹*ᵥ x)
      rw [show A⁻¹.transpose=A⁻¹ from Matrix.isHermitian_iff_isSymm.mp hA.inv.isHermitian] at hv; rw [hv]
    slope:=light _ hA.inv
    smooth:=smooth_score _
local notation "L"=> (origin A hA)
lemma levy (x:I→ℝ): (L).kern x=Real.exp (- Next.SectorChange.Gaussian.force A x/2):=rfl
lemma garden (F: (I→ℝ)→ℝ) : (∫ x,F x ∂cloud A)= (∫ x,F x*(L).kern x) / coat A := by
    rw [cloud_formula hA,integral_withDensity_eq_integral_toReal_smul (( measurable_ratio A).ennreal_ofReal) (Eventually.of_forall (fun _=> ENNReal.ofReal_lt_top))]; simp_rw [ENNReal.toReal_ofReal (ratio_pos hA _).le];
    simp_rw [ smul_eq_mul, Next.SectorChange.Gaussian.ratio]; simp_rw [levy]; rw [ ← integral_div ]; apply integral_congr_ae; filter_upwards with x; ring
lemma full_price : (∫ x,(L).kern x)= coat A:= by
   have h:= garden A hA (fun _=>1); simp only [one_mul, integral_const, probReal_univ,smul_eq_mul] at h; exact(div_eq_iff (coat_pos hA).ne').mp (by simpa using h.symm) |>.trans (one_mul _)
lemma borne (F: (I→ℝ)→ℝ): (∫ x,F x ∂cloud A)= (L).average volume F:=by unfold Law.average; rw [garden A hA, full_price]; rfl

omit hA
def direction (D:Matrix X I ℝ)(x:X) : Module.Dual ℝ (I→ℝ):= LinearMap.proj x ∘ₗ D.mulVecLin
include hA
lemma sensed (D:Matrix X I ℝ) (i j:X): Diagram.Gaussian.bond L (direction D) i j = (D*A*Dᵀ) i j:=by
   unfold Diagram.Gaussian.bond; let p:= direction D; let q:= D i; have hv:= isUnit_iff_ne_zero.mpr hA.det_pos.ne'
   have ht: (L).P (A *ᵥ q)= p i:=by apply LinearMap.ext; intro x;change _ = D i ⬝ᵥ x;rw [(L).turns]; change x ⬝ᵥ (A⁻¹ *ᵥ (A*ᵥ q))=_; rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hv,one_mulVec,dotProduct_comm]
   change p j ( (L).inverse (p i) )= dotProduct ((D*A) i) (D j); rw [ ← ht, Law.solves ]; change dotProduct (D j) (A *ᵥ q)=_; rw [dotProduct_comm]; refine congr_arg (fun z:I→ℝ=> dotProduct z (D j)) ?_
   calc
      _ = q ᵥ* A:=by rw [← Matrix.mulVec_transpose, show Aᵀ=A from Matrix.isHermitian_iff_isSymm.mp hA.isHermitian]
      _ = _:= rfl
variable [Fintype X]
open Diagram Diagram.Gaussian PowerSeries
lemma harvest (D:Matrix X I ℝ)(W:PowerSeries (Diagram.Jet X))(x:X→ℝ)(e:ℕ) : coeff e (burn L (direction D) volume W x)= ∫ i, MvPolynomial.eval (x+D*ᵥ i) (coeff e W) ∂cloud A :=by
    rw [borne A hA (fun i=> _) ,burn,PowerSeries.coeff_mk];rfl
end YM.RegulatorIR.FVAAlt2.Lyric.Capacity
