import YM.FormalOPE.RG10.OpenSlots.Passenger
import YM.FormalOPE.RG10.Routes.Episode
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Stein
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Basis.SMul
/-!
 # Kernel serialisation: manufacture the Row grammar on true open-field steps

 No Gram bounds asserted by this identity. Chart over real coordinates ***not*** det-one;
 to identify normalization do divide cost ratios before comparing. Layout copied into Card.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Sync
open Filter Topology MeasureTheory Measure Function
open PertExtension.GaussianScore MultiGauge MultiGauge.Splice MultiGauge.Papers
open YM.Multi.Vacuum.Gauss
open scoped Classical ContDiff Topology BigOperators ENNReal
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (Γ:Law E)
abbrev Space (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] := Fin (Module.finrank ℝ E)
local notation "Z"=> Space E

lemma unit_basis : ∃ a: Module.Basis Z ℝ E, ∀ i j, Γ.P (a i) (a j) = if i=j then 1 else 0:= by
 let Q: LinearMap.BilinForm ℝ E:=Γ.P
 have hu:LinearMap.IsSymm Q:= ⟨Γ.turns⟩
 obtain ⟨W,hW⟩:= LinearMap.BilinForm.exists_orthogonal_basis hu
 let s (i:Z):= Real.sqrt (Q (W i) (W i))
 have he (i:Z):0 < Q (W i) (W i):= by obtain ⟨a,ha,H⟩:= Γ.slope; specialize H (W i); have hp:= norm_pos_iff.mpr (W.ne_zero i); change 0 < Γ.P (W i) (W i); linarith [mul_pos ha (pow_pos hp 2)]
 have hs i:0<s i:= Real.sqrt_pos.2 (he i)
 have hk i: IsUnit ((s i)⁻¹):= by have hx:= hs i; exact isUnit_iff_ne_zero.mpr (inv_pos.mpr hx).ne'
 refine ⟨W.isUnitSMul hk,fun i j=> ?_⟩; change Q _ _=_
 simp only [Module.Basis.isUnitSMul_apply, _root_.map_smul, LinearMap.smul_apply,smul_eq_mul]; split
 · rename_i h; subst j; rw [←Real.sq_sqrt (he i).le]; change (s i)⁻¹*((s i)⁻¹*(s i)^2)=1; have hh:= hs i; field_simp
 · rename_i h; rw [show Q (W i) (W j)=0 from hW h]; ring

 def bank : Module.Basis Z ℝ E:= (unit_basis Γ).choose
 def pave : Row Z≃ₗ[ℝ] E:= (bank Γ).equivFun.symm
lemma biunit (x y : Row Z): Γ.P (pave Γ x) (pave Γ y)= crossed x y:= by
 unfold pave; simp_rw [Module.Basis.equivFun_symm_apply,_root_.map_sum, LinearMap.sum_apply,_root_.map_smul,LinearMap.smul_apply, smul_eq_mul, show ∀ i j, Γ.P (bank Γ i) (bank Γ j)= if i=j then 1 else 0 from (unit_basis Γ).choose_spec]
 simp [crossed,mul_comm] -- inspect sums
lemma repr (f:Module.Dual ℝ E)(x:Row Z): f (pave Γ x)= crossed (fun i : Z=> f (bank Γ i)) x:= by unfold pave; simp_rw [Module.Basis.equivFun_symm_apply, _root_.map_sum, _root_.map_smul, smul_eq_mul, crossed]; exact Finset.sum_congr rfl fun i _=> mul_comm ..
lemma dual (f g:Module.Dual ℝ E): Γ.wick f g=crossed (fun i:Z=> f (bank Γ i)) (fun i:Z=> g (bank Γ i)):= by
 let u:= (pave Γ).symm (Γ.inverse f)
 have he (x): Γ.P (pave Γ u) (bank Γ x)= u x:= by
    let a:Row Z:= (pave Γ).symm (bank Γ x); rw (occs:=.pos [1]) [← (pave Γ).apply_symm_apply (bank Γ x), biunit]; unfold pave; simp [crossed,Module.Basis.equivFun_self]
 have hk (x:Z):u x = f (bank Γ x):= (he x).symm.trans (by unfold u; simp)
 unfold Law.wick; rw [←(pave Γ).apply_symm_apply (Γ.inverse f),repr,show (pave Γ).symm (Γ.inverse f)=_ from funext hk, Primitives.GCC.crossed_comm]

variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[Measure.IsAddHaarMeasure μ]
lemma acceptance (f:E→ℝ): Γ.average μ f=∫ x,f (pave Γ x) ∂standard Z:= by
 let D:=pave Γ; let P:= Measure.map D volume; let z:= addHaarScalarFactor P μ; letI: IsAddHaarMeasure P:= D.toContinuousLinearEquiv.isAddHaarMeasure_map _
 have hz:0<(z:ℝ):= addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
 have hp(f:E→ℝ): (∫ x,f (D x)) = (z:ℝ) * ∫ x,f x ∂μ:= by
     rw [show (∫ x,f (D x))=∫ x,f x ∂P from (integral_map_equiv D.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv f).symm, show P=z • μ from isAddLeftInvariant_eq_smul _ _,integral_smul_nnreal_measure]; rfl
 let K:= (Next.SectorChange.Gaussian.coat (1 : Next.SectorChange.Gaussian.Table Z))⁻¹
 have he(x):Primitives.GCC.skin Z x= K* Γ.kern (D x):= by unfold K Law.kern D; rw [Primitives.GCC.skin_apply,biunit,Primitives.GCC.crossed_self]; ring_nf
 have hr (f : E→ℝ): (∫ x,f (D x) ∂standard Z) = K*(z:ℝ) * ∫ x, (f*Γ.kern) x ∂μ:= by
    rw [(Primitives.GCC.cash (fun x=> f (D x))).2]
    simp_rw [he, smul_eq_mul, mul_assoc, mul_comm (Γ.kern _), integral_const_mul] -- test
    change K*(∫ x, (f*Γ.kern) (D x))=_; rw [hp]
 have h1:= hr (fun _=>1); change (∫ _ : Row Z,(1:ℝ) ∂ standard Z)= _ at h1; simp only [integral_const, probReal_univ, smul_eq_mul,mul_one,show (fun _:E=> (1:ℝ))=(1:E→ℝ) from rfl,one_mul] at h1
 rw [hr]; unfold Law.average; rw [div_eq_iff (positive Γ μ).ne',mul_right_comm,← h1, one_mul]
end YM.FormalOPE.RG10.Sync
