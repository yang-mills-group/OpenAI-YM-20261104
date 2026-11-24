import YM.Integration.WilsonOriginalPublicNodalBufferedCellProbe
import YM.Integration.WilsonPositionProgramTrialPublicJointKernel
import YM.Integration.WilsonSeparatedPrefixMovingJointWavePages

/-! The actual planted wheel jets vary jointly in the full Fourier frequency and the subcell displacement. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalFrequencyProbe
open Function Finset Lattice RG Wilson Labels MeasureTheory PhysicalNext.Repeat.Legato
open WilsonCoeffUV.Cosmos WilsonCoeffUV WilsonCoeffUV.Layout WilsonCoeffUV.Embroider WilsonCoeffUV.Mer
open WilsonPositionProgramTrialPublicCellPulse (placed)
open WilsonIndependentFittedExteriorProfile (jet)
open WilsonSeparatedPrefixMovingJointSpectrum (Euclid)
open WilsonSeparatedPrefixMovingJointWavePages (pulse)
open WilsonPositionProgramTrialPublicJointRoom (width big normalized marks)
open scoped Classical BigOperators Topology ContDiff
variable {n:ℕ}{D:Fin n → ℕ}

theorem coordinate (T:(i:Fin n) → Rarity (D i))(real:∀i,ContDiff ℝ ∞ (T i).ψ.val)
    (c:Fin n → Bool)(i:Fin n)(x y σ:ℝ)(sp:0<σ)(o:CellR)(z:Cover)(a:Knob (D i))(b:Chamber):
    Continuous fun w:Points n × Point4 =>
      (wheelC x y z (placed (normalized T w.1 c i) x y σ sp o w.2).ψ o).val a b:=by
  let gone:=fun ξ:Point4=>σ⁻¹ • (-(-(y • o.val)-x • ξ)+address x y o z b.val)
  let pin:=ContinuousMultilinearMap.apply ℝ (fun _:Fin a.1.val=>Point4) ℝ (Embroider.dot ∘ a.2)
  let ray:=fun w:Points n × Point4=>(w.1 i,gone w.2)
  have gm:Continuous gone:=by unfold gone;fun_prop
  have projection:Continuous (fun ν:Points n=>ν i):=(PiLp.proj (𝕜:=ℝ) 2 (fun _:Fin n=>E4) i).continuous
  have motion:Continuous ray:=(projection.comp continuous_fst).prodMk (gm.comp continuous_snd)
  have localJet:=WilsonSeparatedPrefixMovingJointPartial.original (pulse (T i) (c i))
    (WilsonSeparatedPrefixMovingJointWavePages.smooth (T i) (real i) (c i)) a.1.val
  have rate:Continuous (fun w:Points n × Point4=>(width w.1^D i)⁻¹):=
    (((show Continuous (width:Points n→ℝ) by unfold width;fun_prop).comp continuous_fst).pow _).inv₀
      (fun w=>(pow_pos (zero_lt_one.trans_le (big w.1)) _).ne')
  have cf:=pin.continuous.comp (localJet.comp motion)
  have native:Continuous (fun w:Points n × Point4=>x^a.1.val*(
    σ⁻¹^4*(σ⁻¹^a.1.val*((width w.1^D i)⁻¹*(pin ((iteratedFDeriv ℝ a.1.val
    (fun p=>pulse (T i) (c i) (w.1 i,p))) (gone w.2))))))):=
    continuous_const.mul (continuous_const.mul (continuous_const.mul (rate.mul cf)))
  apply native.congr
  intro w
  change _=crease (sonal x y o z (placed (normalized T w.1 c i) x y σ sp o w.2).ψ) a.2 b.val
  rw [currentP _ _ _ _ _ _ (Nat.le_of_lt_succ a.1.isLt),WilsonPositionProgramTrialPublicCellPulse.placed,
    jet _ _ sp _ _ (Nat.le_of_lt_succ a.1.isLt),normalized,marks _ _ (Nat.le_of_lt_succ a.1.isLt)]
  rfl

theorem jewel {G:Gauge}{d:ℕ}{F:Labels.Frame G d}
    (T:(i:Fin n) → Rarity (D i))(real:∀i,ContDiff ℝ ∞ (T i).ψ.val)
    (c:Fin n → Bool)(i:Fin n)(cut:d<D i)(x y σ:ℝ)(sp:0<σ)(o:CellR)(z:Cover)(a:Alma F):
    Continuous fun w:Points n × Point4 =>
      jewelBloom cut a (wheelC x y z (placed (normalized T w.1 c i) x y σ sp o w.2).ψ o):=by
  exact coordinate T real c i x y σ sp o z _ zeroC

end YM.Integration.WilsonOriginalPublicNodalFrequencyProbe
end
