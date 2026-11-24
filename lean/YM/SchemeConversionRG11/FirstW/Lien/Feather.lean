import YM.SchemeConversionRG11.FirstW.Lien.Effort
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Lattice Pert Align Topology Deck Maxwell Extra.FD RawLabels Position SchemeConversionRG11 SchemeConversionRG11.Horizon
open scoped BigOperators Classical
variable {G:Gauge} {F : Labels.Frames G} {S:Itinerary} {E:Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
private lemma helen_reim (a:ℕ→ℂ) (x:ℂ)(h:Tendsto (fun i=>(a i).re) atTop (𝓝 x.re))(hp:Tendsto (fun i=>(a i).im) atTop (𝓝 x.im)) : Tendsto a atTop (𝓝 x) := by
   have he:= (Complex.continuous_ofReal.continuousAt.tendsto.comp h).add ((Complex.continuous_ofReal.continuousAt.tendsto.comp hp).mul_const Complex.I); rw [Complex.re_add_im] at he; exact he.congr (fun i=> Complex.re_add_im _)
lemma gathering {I:Type*} (B:I→ E→ₗ[ℝ]ℂ)(p:E→ₗ[ℝ]ℂ) (h:∀ x,(∀ i,B i x=0)→ p x=0)(z:ℕ→E)(hp:∀ i,Helen (fun j=>B i (z j))): Helen (fun j=>p (z j)) := by
 let J := I×Low ℂ; let q (s : J) := s.2 ∘ₗ B s.1
 have ht: Book (fun j=>p (z j)) := by
    intro L; apply offbook (U:=E) (a:=z) q (q:=L ∘ₗ p)
    · intro v hv
      have e (i:I): B i v=0:=Complex.ext (hv ⟨i,Complex.reCLM.toLinearMap⟩) (hv ⟨i,Complex.imCLM.toLinearMap⟩)
      rw [LinearMap.comp_apply,h v e,map_zero]
    intro r; obtain ⟨x,hx⟩:=hp r.1; exact ⟨r.2 x,r.2.continuous_of_finiteDimensional.continuousAt.tendsto.comp hx⟩
 obtain ⟨w,H⟩:=ht.aims; exact ⟨w,helen_reim _ w (H Complex.reCLM.toLinearMap) (H Complex.imCLM.toLinearMap)⟩
lemma slicer {I:Type*} (B:I→E→ₗ[ℝ]ℂ)(q:Low E)(h:∀ x,(∀ i,B i x=0) → q x=0) (z:ℕ→E)(hp:∀ i,Tendsto (fun j=>B i (z j)) atTop (𝓝 0)):
    Tendsto (fun j=>q (z j)) atTop (𝓝 0) := by
 let A:= I × Low ℂ; let J (i:A) := i.2 ∘ₗ B i.1
 have H:= transmitted J (fun v hv => h v (fun i=>Complex.ext (hv ⟨i,Complex.reCLM.toLinearMap⟩) (hv ⟨i,Complex.imCLM.toLinearMap⟩)))
 clear h; induction H using Submodule.span_induction with
 | mem x hx=> obtain ⟨i,rfl⟩:=hx; have h:=i.2.continuous_of_finiteDimensional.continuousAt.tendsto.comp (hp i.1); rw [map_zero] at h; exact h
 | zero=>exact tendsto_const_nhds
 | add x y _ _ h g=> simpa only [LinearMap.add_apply,add_zero] using h.add g
 | smul r x _ ih=>simpa only [mul_zero,smul_eq_mul,LinearMap.smul_apply] using ih.const_mul r
end YM.RG11.FirstW
