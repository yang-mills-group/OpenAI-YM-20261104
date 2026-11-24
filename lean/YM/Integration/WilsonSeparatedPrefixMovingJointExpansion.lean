import YM.Integration.WilsonSeparatedPrefixMovingJointWindow
import YM.Integration.WilsonSeparatedPrefixMovingJointWaves

/-! A real signed projective expansion of the original mixed-position test. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJointExpansion
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonCoeffUV.Layout
open WilsonIndependentFittedExteriorProfile (home)
open WilsonIndependentMatchedCoverProfile (word)
variable {G:Gauge}{D:ℕ}



open Set
open scoped ContDiff
open WilsonSeparatedPrefixMovingAddressInk (writer)


open MeasureTheory
open scoped ContDiff SchwartzMap
open WilsonSeparatedPrefixMovingJointSpectrum (Euclid character physical)
open WilsonSeparatedPrefixMovingJointWaves (wave sheet)
def angle (ξ:Euclid):Point4→L[ℝ]ℝ:=(2*Real.pi) • (innerSL ℝ ξ).comp physical.symm.toContinuousLinearMap
theorem price (ξ:Euclid):‖angle ξ‖≤(2*Real.pi*‖physical.symm.toContinuousLinearMap‖)*‖ξ‖:=by
  unfold angle
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤2*Real.pi)]
  have bound:‖innerSL ℝ ξ‖≤‖ξ‖:=((innerSL ℝ).le_opNorm ξ).trans
    (by simpa using mul_le_mul_of_nonneg_right (norm_innerSL_le (E:=Euclid) ℝ) (norm_nonneg ξ))
  calc
    _ ≤ (2*Real.pi)*(‖ξ‖*‖physical.symm.toContinuousLinearMap‖):=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right bound (norm_nonneg _))
    _ = _:=by ring
def coefficient (z:ℂ):Bool→Bool→ℝ|false,false=>z.re|true,true=>z.re|false,true=> -z.im|true,false=>z.im
theorem coin (z:ℂ)(c d:Bool):|coefficient z c d|≤‖z‖:=by
  cases c <;> cases d <;> simp only [coefficient,abs_neg] <;>
    first | exact Complex.abs_re_le_norm _ | exact Complex.abs_im_le_norm _
private lemma realPart (z:ℂ)(ξ:Euclid)(p q:Point4):
    (z*(character ξ (-p)*character ξ q)).re=∑c:Bool,∑d:Bool,coefficient z c d*wave c (angle ξ p)*wave d (angle ξ q):=by
  have re (x:Point4):(character ξ x).re=Real.cos (angle ξ x):=Complex.exp_ofReal_mul_I_re _
  have im (x:Point4):(character ξ x).im=Real.sin (angle ξ x):=Complex.exp_ofReal_mul_I_im _
  simp only [Complex.mul_re,Complex.mul_im,re,im,map_neg,Real.cos_neg,Real.sin_neg,Fintype.sum_bool,coefficient,WilsonSeparatedPrefixMovingJointWaves.wave]
  ring
theorem declared {d k:ℕ}(φ:Rarity d)(ψ χ:Rarity k)(hf:ContDiff ℝ ∞ ψ.ψ.val)
    (window:∀p q:Point4,φ.ψ.val p*ψ.ψ.val (q-p)=φ.ψ.val p*(χ.ψ.val q*ψ.ψ.val (q-p))):
    ∃S:𝓢(Euclid,ℂ),S=WilsonSeparatedPrefixMovingJointSpectrum.transformed ψ hf ∧ (∀n:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^n)*‖S ξ‖)) ∧ ∀p q:Point4,
      φ.ψ.val p*ψ.ψ.val (q-p)=∫ξ:Euclid,∑c:Bool,∑e:Bool,coefficient (S ξ) c e*
        (sheet φ (angle ξ) c).ψ.val p*(sheet χ (angle ξ) e).ψ.val q:=by
  obtain ⟨S,identity,paid,read⟩:=WilsonSeparatedPrefixMovingJointSpectrum.declared ψ hf
  refine ⟨S,identity,paid,?_⟩
  intro p q
  let kernel:Euclid→ℂ:=fun ξ=>S ξ*(character ξ (-p)*character ξ q)
  have continuousChar (x:Point4):Continuous (fun ξ:Euclid=>character ξ x):=by unfold character;fun_prop
  have int:Integrable kernel:=by
    have nrm:Integrable (fun ξ:Euclid=>‖S ξ‖):=(show Integrable (S:Euclid→ℂ) from S.integrable).norm
    apply nrm.mono' (S.continuous.mul ((continuousChar (-p)).mul (continuousChar q))).aestronglyMeasurable
    filter_upwards [] with ξ
    simp [WilsonSeparatedPrefixMovingJointSpectrum.modulus]
  have trueReal:ψ.ψ.val (q-p)=∫ξ,(kernel ξ).re:=by
    rw [show (∫ξ,(kernel ξ).re)=(∫ξ,kernel ξ).re from integral_re int]
    exact congrArg Complex.re (read p q)
  rw [window,←mul_assoc,trueReal,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  change _*(S ξ*(character ξ (-p)*character ξ q)).re=_
  rw [realPart]
  simp only [Fintype.sum_bool,WilsonSeparatedPrefixMovingJointWaves.sheet,coefficient,WilsonSeparatedPrefixMovingJointWaves.wave]
  ring
theorem original {d k:ℕ}(φ:Rarity d)(ψ χ:Rarity k)(hf:ContDiff ℝ ∞ ψ.ψ.val)
    (window:∀p q:Point4,φ.ψ.val p*ψ.ψ.val (q-p)=φ.ψ.val p*(χ.ψ.val q*ψ.ψ.val (q-p))):
    ∃S:𝓢(Euclid,ℂ),(∀n:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^n)*‖S ξ‖)) ∧ ∀p q:Point4,
      φ.ψ.val p*ψ.ψ.val (q-p)=∫ξ:Euclid,∑c:Bool,∑e:Bool,coefficient (S ξ) c e*
        (sheet φ (angle ξ) c).ψ.val p*(sheet χ (angle ξ) e).ψ.val q:=by
  obtain ⟨S,_,data⟩:=declared φ ψ χ hf window
  exact ⟨S,data⟩
end YM.Integration.WilsonSeparatedPrefixMovingJointExpansion
