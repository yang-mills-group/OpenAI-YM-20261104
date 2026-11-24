import YM.SignedWilsonExpansion.Chron.Older
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6FirstThermal
/-!
Physical F6 restore. Use full incident action (no short deletion). X for this tilt
 is *exterior*. When conditioning just on Older, use `Older` identities, both
 equal to these assembled rows with ALL relevant terms included (the two arguments
 have their own conditional laws). No changing X in the middle of tilting.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.Logwood
open Function Filter Finset Lattice RG Wilson MeasureTheory
open OPE.Therm
open scoped Topology ENNReal BigOperators Classical
open FVA1Physical.Exchange FVA1Physical.Exchange.F6Regular
open private finite_measurable from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6PhysicalScalarSeries
open private external original_envelope from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6OriginalMoments
variable {G:Gauge}{d i j N p:ℕ}{n: Side}{ε b:ℝ}{H:History G}
variable (A:History G)(I:Finset (Edge (Site n)))
abbrev ticketA (I:Finset (Edge (Site n)))(p:BudgetPoint)(ε:ℝ):ℝ:= ((halo 8 (I.image Prod.fst)).card:ℝ)*(2*Push.GridApprox.Attach.hitConstant p.B*ε)
variable {α:Type*}[MeasurableSpace α]{f:α→ℂ}
lemma splitRe (p:Envelope f): Envelope (fun i=>(f i).re):= ⟨Complex.measurable_re.comp p.meas,p.cost.choose, fun i=>(Complex.abs_re_le_norm _).trans (p.cost.choose_spec i)⟩
lemma splitIm (p:Envelope f): Envelope (fun i=>(f i).im):= ⟨Complex.measurable_im.comp p.meas,p.cost.choose, fun i=>(Complex.abs_im_le_norm _).trans (p.cost.choose_spec i)⟩
private lemma norm_mc (x:ℂ):‖x‖ ≤ |x.re|+|x.im|:=Complex.norm_le_abs_re_add_abs_im _
lemma env_join {f:α→ℂ}(he:Envelope (fun i=>(f i).re))(hi:Envelope (fun i=>(f i).im)):Envelope f:=by
   have hp : f=fun i=> Complex.ofReal ((f i).re)+ ↑((f i).im)*Complex.I:=funext (fun i=> ( Complex.re_add_im (f i)).symm); constructor
   · rw [ hp ];
     exact ( Measurable.add (Complex.measurable_ofReal.comp he.meas) ( (Complex.measurable_ofReal.comp hi.meas).mul_const _)) -- direction wrong
   exact ⟨_, fun i=>(norm_mc _).trans (add_le_add ( he.cost.choose_spec i ) ( hi.cost.choose_spec i))⟩

variable {F:Config G n→ℂ} (R:Rep G n)
/-- real and imaginary on the *same* tilt. -/
abbrev leaner (maker:(Config G n→ℝ)→ ({b:Edge (Site n)//b∉I}→G.El)→ℝ)(F:Config G n→ℂ)(o: {b:Edge (Site n)//b∉I}→G.El):ℂ:=⟨maker (Complex.re∘F) o,maker (Complex.im∘F) o⟩
abbrev remit (F) (d:ℕ) := leaner I (fun f=> finiteOne R I f d) F
abbrev remitG (F) := leaner I (originalOne R I) F
abbrev remitC (F) := leaner I (baseOne R I) F
abbrev remitS (F) := leaner I (patchInsertion R I (R.activities.additive R.p)) F
variable {σ C Λ ξ:ℝ}(law:R.Lawful σ C Λ ε ξ)(ps:∀U,0<R.eval U)
include law ps in
lemma remit_price (he : Envelope F) (b:ℝ)(hb:∀U,‖F U‖≤ b)(hv:1≤ R.p.supportExponent)(hl:ticketA I R.p ε ≤1/4) (d:ℕ):
    Envelope (remit I R F d) ∧ Envelope (remitG I R F) ∧ ∀ o,3/4≤ firstQuiet R I o ∧ remit I R F 1 o=remitC I R F o-(firstQuiet R I o)⁻¹ • remitS I R F o ∧
        ‖remit I R F d o- remitG I R F o‖≤ 16*b*ticketA I R.p ε ^(d+1):=by
   let Z:=ticketA I R.p ε; have h σ (x:Envelope σ) (t:∀U,|σ U|≤b): Envelope (originalOne R I σ) ∧ Envelope (finiteOne R I σ d):=by
       let e:=8*b*Z^(d+1); have ho :=original_envelope R law ps I σ x
       exact ⟨ho,finite_measurable R law I σ x.meas d,_, fun o=> (norm_le_insert' _ (originalOne R I σ o)).trans (add_le_add (ho.cost.choose_spec o) (show _≤e from original_one_finite R law ps I hv σ x b t d o hl))⟩
   let A (u):=(F u).re; let B (u):=(F u).im; have hp u: |A u| ≤ b:=(Complex.abs_re_le_norm _).trans (hb u); have hq u:|B u| ≤ b:= (Complex.abs_im_le_norm _).trans (hb u); let x:Envelope A:= splitRe he; let y:Envelope B:=splitIm he; let D₁:=h A x hp; let D₂:=h B y hq
   refine ⟨env_join D₁.2 D₂.2, env_join D₁.1 D₂.1,?_⟩; intro o; let z:= firstQuiet R I o; have hx:= original_first_thermal R law ps I hv A x b hp o hl; have hy:=original_first_thermal R law ps I hv B y b hq o hl
   refine ⟨hx.1,?_ , (norm_mc _).trans ((add_le_add ( show |(remit I R F d o-remitG I R F o).re| ≤8*b*Z^(d+1) from original_one_finite R law ps I hv A x b hp d o hl ) ( show |( remit I R F d o-remitG I R F o).im| ≤8*b*Z^(d+1) from original_one_finite R law ps I hv B y b hq d o hl ) ).trans_eq (by unfold Z; ring))⟩
   have t p: p/z=z⁻¹*p:= by rw [div_eq_mul_inv,mul_comm]
   apply Complex.ext
   · rw [Complex.sub_re,Complex.real_smul]; simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; exact hx.2.1.trans (congr_arg _ (t _))
   rw [Complex.sub_im,Complex.real_smul]; simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,zero_add]; exact hy.2.1.trans (congr_arg _ (t _))
section
variable {S:History G}(pS:S.Selected) {N' j' p':ℕ} (hpS:j'≤N')(J:Finset (Edge (Site (S.S.side j' p'))))
include pS hpS
lemma PS_exterior : IsProbabilityMeasure (originalExterior S N' p' j' J):=by letI:=probability (p:=p') pS hpS; exact Measure.isProbabilityMeasure_map (external J).aemeasurable
variable {F':Config G (S.S.side j' p')→ℂ}
set_option linter.unusedSectionVars false in
lemma ret_the (x:Envelope F'){M:ℝ}(p:∀ i,‖F' i‖ ≤ M)(d:ℕ) (width:1≤ (S.rep N' p' j').p.supportExponent) (hl:ticketA J (S.rep N' p' j').p (S.levels.clock.allowance j') ≤1/4):
    let μ:= originalExterior S N' p' j' J; let R:= S.rep N' p' j'; let y:= scene S N' p' j'; Slate y F'= Slate μ (remitG J R F') ∧ ‖Slate μ ( remit J R F' d ) - Slate y F'‖ ≤ 16*M*ticketA J R.p ( S.levels.clock.allowance j') ^(d+1):=by
   intro μ R y; let _ : IsProbabilityMeasure y:= probability pS hpS; let _ : IsProbabilityMeasure μ:= PS_exterior pS hpS J
   obtain ⟨he,hx,hp⟩:=remit_price J R (pS.represents N' p' j' hpS).good (SectorNext.Vacuum.strictly _ pS _ _ _ hpS) x _ p width hl d; -- order
   have hz (f: Config G _ →ℝ) (h:Envelope f): ( ∫ x, originalOne R J f x∂μ)=∫ x,f x∂y:= by simpa only [one_mul] using physical_moment_disintegrates S pS hpS J f h (fun _=>1) (Envelope.const 1)
   have hy : Slate y F'=Slate μ (remitG J R F'):=by
       apply Complex.ext -- types
       · change RCLike.re (Slate y F') = RCLike.re (Slate μ (remitG J R F')); unfold Slate; rw [← integral_re (intE x y), ← integral_re (intE hx μ)]; exact (hz _ (splitRe x)).symm
       change RCLike.im (Slate y F') = RCLike.im (Slate μ (remitG J R F')); unfold Slate; rw [← integral_im (intE x y), ← integral_im (intE hx μ)]; exact (hz _ (splitIm x)).symm
   rw [hy]; refine ⟨rfl,?_⟩; unfold Slate; rw [←integral_sub (intE he μ) (intE hx μ)]; simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ:=μ) (Filter.Eventually.of_forall fun x=>(hp x).2.2)
end
end YM.Integration.Logwood
namespace YM.Integration.Logwood
open Function Filter Finset Lattice RG Wilson MeasureTheory
open OPE.Therm
open scoped Topology ENNReal BigOperators Classical
open FVA1Physical.Exchange FVA1Physical.Exchange.F6Regular
variable {G:Gauge}{d i j N p:ℕ}{n: Side}{ε b:ℝ}{S:History G}
variable (pS:S.Selected) {N' j' p':ℕ} (hpS:j'≤N')(J:Finset (Edge (Site (S.S.side j' p'))))
include pS hpS
lemma denominatorP (hl:ticketA J (S.rep N' p' j').p (S.levels.clock.allowance j') ≤1/4) (width:1≤(S.rep N' p' j').p.supportExponent) (d:ℕ)(o:({b:Edge (Site (S.S.side j' p'))//b∉J} → G.El)):
   let V:=fillPatch J o; 0<∫z,patchTaylorDensity (S.rep N' p' j') (V 1) d (V z)∂ Measure.pi (fun _:↥J=>G.probHaar):=by
    intro V; let H:= fun (i:Fin 3) (_:Config G (S.S.side j' p'))=>(0:ℂ); have he i:Envelope (H i):=⟨measurable_const,0,fun t=>norm_zero.le⟩; exact (actual_seven_thermal S pS hpS J width o d H he (fun _=>0) (fun _=>le_refl _) (fun _ _=>norm_zero.le) hl).1
end YM.Integration.Logwood
