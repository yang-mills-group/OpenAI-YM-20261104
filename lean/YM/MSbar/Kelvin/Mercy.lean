import YM.MSbar.Kelvin.Mount
import YM.SectorNext.RECONNECTED_LOCALITY.Gram
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Kelvin
open Function Filter MeasureTheory Cacao PowerSeries Finset Whisk
open scoped Topology BigOperators Classical
open Lattice Matrix Further.GaussianScalar SectorNext.Reconnect.Window
variable {ι σ τ: Type}[Fintype σ][Fintype ι][Fintype τ][DecidableEq σ] [DecidableEq ι]
    {n:Side} {l:σ→ Site n}{k:Matrix σ σ ℝ}
    (u:ι→σ) (h:Injective u) (K:k.PosDef)
-- equality of measures via characteristic.Pin syntax with matrix products.
local notation "ι!"=>imbed u
local notation "e!"=> extendM u
local notation "P"=> pinch u k
local notation "H"=> View σ
local notation "F"=> View ι
local notation "v!"=> vanish u k
local notation "p!"=> (fieldLaw k⁻¹)
local notation "d!"=>fieldLaw P⁻¹
lemma cpass (A : Matrix σ ι ℝ)(C : Matrix ι ι ℝ)(y:Measure (View ι))(h : Says y C) : Says (Measure.map (fun v:View ι=>A*ᵥ v) y) (A*C*A.transpose):=by
    rw [show (fun v:View ι=> A *ᵥ v)=run A from funext (fun x=>by funext i; unfold Matrix.mulVec dotProduct run; exact sum_congr rfl fun j _=> mul_comm ..)]
    have he : (A*C*A.transpose)=pushed A C:=by ext i j; unfold pushed; simp_rw [Matrix.mul_apply, Finset.sum_mul,transpose_apply]; rw [Finset.sum_comm]; exact sum_congr rfl fun i _=>sum_congr rfl fun j _=>by ring
    exact he ▸ h.image A
-- Sum via Osc
lemma spar {A : Matrix σ ι ℝ}{B : Matrix σ τ ℝ}{μ : Measure (View ι)}{ν : Measure (View τ)} [IsProbabilityMeasure μ][IsProbabilityMeasure ν]{C : Matrix ι ι ℝ}{D:Matrix τ τ ℝ}(hc : Says μ C)(hd : Says ν D) : Says (Measure.map (fun p:View ι × View τ=> A*ᵥp.1 + B*ᵥp.2) (μ.prod ν)) (A*C*A.transpose+B* D*B.transpose) :=by
   let a(v:View ι):=A*ᵥ v; let b(v:View τ):= B*ᵥ v; let q(p:View ι×View τ):= a p.1+b p.2
   have ha:Measurable a:= (toLin' A|>.continuous_of_finiteDimensional.measurable); haveI: DecidableEq τ:= Classical.decEq _; have hb :Measurable b := (toLin' B|>.continuous_of_finiteDimensional.measurable)
   have hp : Measurable q:= (ha.comp measurable_fst).add (hb.comp measurable_snd)
   refine ⟨Measure.isProbabilityMeasure_map hp.aemeasurable,fun t=> ?_⟩
   let ψ(v:View σ):=osc (sumPair v t); have hψ:Measurable ψ:= osc_meas.comp (pair_meas _); have he(v w:View σ):ψ (v+w)=ψ v*ψ w:=by
       unfold ψ osc sumPair; rw [←Complex.exp_add]; apply congr_arg; simp_rw [Pi.add_apply,add_mul,sum_add_distrib];push_cast;ring
   have h:said (Measure.map q (μ.prod ν)) t=said (Measure.map a μ) t * said (Measure.map b ν) t:=by
       unfold said; rw [integral_map hp.aemeasurable hψ.aestronglyMeasurable, integral_map ha.aemeasurable hψ.aestronglyMeasurable,integral_map hb.aemeasurable hψ.aestronglyMeasurable]
       change (∫ v,ψ (q v)∂ μ.prod ν) = _; unfold q; simp_rw [he]; exact integral_prod_mul (μ:=μ) (ν:=ν) (ψ∘a) (ψ∘b)
   change said _ _ = _; rw [h,(cpass A C μ hc).response, (cpass B D ν hd).response]
   unfold bell act; rw [← Complex.exp_add]; apply congr_arg; simp_rw [Matrix.add_apply,mul_add,sum_add_distrib]; push_cast; ring
noncomputable def momentum (u:ι→σ)(k:Matrix σ σ ℝ):View σ× View ι→ View σ:=fun p=> vanish u k *ᵥp.1+imbed u*ᵥ p.2
include h K
lemma host : MeasurePreserving (momentum u k) ((fieldLaw k⁻¹).prod (fieldLaw (pinch u k)⁻¹)) (fieldLaw k⁻¹) := by
    let A:= k⁻¹; let B:= (pinch u k)⁻¹; have hb: B.PosDef:= (K.submatrix h).inv; let g:= momentum u k
    have he:= spar (A:=v!) (B:=ι!) (show Says (fieldLaw A) A from mathlib_says (K.inv.posSemidef)) (show Says (fieldLaw B) B from mathlib_says (hb.posSemidef)); have hp:=wince u h K
    unfold extendM at hp; change _ = k⁻¹ at hp
    refine ⟨?_,Says.unique (C:=A) ?_ (mathlib_says K.inv.posSemidef)⟩
    · exact (((toLin' (v!)|>.continuous_of_finiteDimensional.measurable).comp measurable_fst).add ((toLin' (ι!)|>.continuous_of_finiteDimensional.measurable).comp measurable_snd))
    change Says (Measure.map g _) _ at he
    change Says _ (show Cov σ from A); refine (Eq.mp ?_ he); exact congr_arg _ hp -- cast
end YM.MSbar.Kelvin
