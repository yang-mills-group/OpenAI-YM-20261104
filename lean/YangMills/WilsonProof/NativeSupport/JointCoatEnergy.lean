import YangMills.WilsonProof.NativeSupport.TaggedEnergy
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Profile

/-! The inserted transition energy on the actual vacuum sector, before the
shared tag or fine-field integrations. The same vacuum cost is retained for
every other vertex of the molecule. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointCoat
open Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset
open MeasureTheory Push Push.BetaTransport Push.AbsoluteSums Precision Exterior ConnectedActivityE6
open Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Mask Contract Work.F03
open Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse Coat Matter
open Itinerary Art Rotation
open Cells RGComparison.Core16
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {c f L : Side} {S : StepData c f} {F : Forest S.ratio}
    {T : Tube G S} {P : Teller G} {R : Rep G f} {W μ C : ℝ}
    {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}
variable (X : Coat T F)

def energy (u : Directions G f) (b : Bond c) : ℝ :=
  linkEnergy S (X.V b*(S.prediction (X.input u) X.k b)⁻¹)

theorem monetary_eq (u : Directions G f) (b : Bond c) :
    monetary S (S.prediction (X.input u) X.k) X.V b=energy X u b := by
  unfold monetary wire energy linkEnergy
  rw [G.chord_price]
  ring

theorem cell_eq {n : Side} (d : Descent n f) (t : (d.push S F).Tags)
    (x : Descent.Fields G (d.push S F)) (u : Directions G f) (b : Bond c)
    (tag : t.1=X.k) (view : x ∘ Sum.inl=X.view u) :
    WilsonUniformUnmarkedInletEnergySites.cell G (d.push S F) t X.V x (Sum.inl b)=
      energy X u b := by
  simp only [WilsonUniformUnmarkedInletEnergySites.cell,Sum.elim_inl,tag,view,energy,Coat.input]

theorem gauge_eq (z : Site c→G.El) (b : Bond c) (u : Directions G f)
    (hb : S.patch.Branches S.kernel G) :
    energy (Hues.sluice X z) (spinRow S z u) b=energy X u b := by
  unfold energy
  rw [Hues.banks]
  change linkEnergy S ((gauge z X.V) b*(S.prediction (gauge (constantGauge z S.ratio)
    (X.input u)) X.k b)⁻¹)=_
  rw [Hues.feed z (X.input u) X.k hb]
  have e (U V : Config G c) :
      (gauge z U) b *((gauge z V) b)⁻¹ = z b.1*(U b*(V b)⁻¹)*(z b.1)⁻¹ := by
    unfold Lattice.gauge; group
  rw [e,linkEnergy,G.price_conj]
  rfl

def lifted (β : ℝ) (b : Bond c) (v : F.Slice G × Air f G) : ℝ :=
  energy (X.wrapY v.1) ((X.wrapY v.1).liftA β v.2) b

theorem in_band (β : ℝ) (b : Bond c) (v : F.Slice G × Air f G) :
    lifted X β b v ∈ Set.Icc 0 (linkCap S) :=
  ⟨(link_estimate S).nonneg _,(link_estimate S).bound _⟩

variable (H : Cash W X.x μ L Q o C T R) (width : X.width=o.K)
include H width

theorem measurable_lifted (b : Bond c) : Measurable (lifted X R.beta b) := by
  let Z (u : F.Slice G × Air f G) := X.wrapY u.1
  let U (u : F.Slice G × Air f G) := (Z u).input ((Z u).liftA R.beta u.2)
  have hu : Measurable U := X.summon measurable_fst
    ((X.airwards (v:=Prod.snd) (width.symm ▸ H.laws.data.access)
      H.laws.intake.ready measurable_fst).2.2 R.beta measurable_snd)
  have hq := (measurable_pi_apply b).comp ((S.prediction_meas
    (funds_branch H.laws.intake.ready) X.k).comp hu)
  exact (link_estimate S).measurable.comp (measurable_const.mul hq.inv)

/-- A product of measurements of the actual bond energies shares the same frozen field,
predictor choices and Gaussian sample with every original body factor. Its absolute
component integral is priced before summing over sites or forming a normalized law. -/
theorem component (manifest : X.manifest) (k : Finset ℕ) (p : Molecule S)
    (J : Finset (Bond c)) (h : Bond c→ℝ→ℂ) (w : Bond c→ℝ)
    (hm : ∀ b∈J,Measurable (h b))
    (bounded : ∀ b∈J,∀ v∈Set.Icc 0 (linkCap S),‖h b v‖≤w b) :
    let D := (F.order G).prod X.dice
    let f := X.body R Q.table W o.a k Q.halo p
    Integrable (fun v => (∏ b∈J,h b (lifted X R.beta b v))*(f v : ℂ)) D ∧
    ∫ v, ‖(∏ b∈J,h b (lifted X R.beta b v))*(f v : ℂ)‖ ∂D ≤
      (∏ b∈J,w b)*∏ i∈p,H.text i := by
  intro D body
  have nn (b : Bond c) (bJ : b∈J) : 0≤w b :=
    (norm_nonneg _).trans (bounded b bJ 0 ⟨le_rfl,(link_estimate (G:=G) S).cap⟩)
  have nonneg := Finset.prod_nonneg nn
  have fi : Integrable body D := H.integrated X rfl width manifest k p
  have bound (v : F.Slice G × Air f G) :
      ‖(∏ b∈J,h b (lifted X R.beta b v))*(body v : ℂ)‖≤(∏ b∈J,w b)*‖body v‖ := by
    rw [norm_mul,norm_prod,Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun b bJ => bounded b bJ _ (in_band X _ b v))) (norm_nonneg _)
  have mf : Measurable body := X.body_b Q.table_exists H.laws.intake
    (width.symm ▸ H.laws.data.access) o.a k Q.halo p
  have mh : Measurable (fun v => ∏ b∈J,h b (lifted X R.beta b v)) :=
    Finset.measurable_fun_prod J fun b bJ => (hm b bJ).comp (measurable_lifted X H width b)
  refine ⟨(fi.norm.const_mul _).mono'
    (mh.mul (Complex.continuous_ofReal.measurable.comp mf)).aestronglyMeasurable
    (ae_of_all D bound),?_⟩
  calc
    _ ≤ ∫ v, (∏ b∈J,w b)*‖body v‖ ∂D := integral_mono_of_nonneg
      (ae_of_all D (fun _ => norm_nonneg _)) (fi.norm.const_mul _) (ae_of_all D bound)
    _ = (∏ b∈J,w b)*(∫ v, ‖body v‖ ∂D) := integral_const_mul ..
    _ ≤ _ := mul_le_mul_of_nonneg_left (H.statements X rfl width manifest k p) nonneg

end YM.Integration.InletSusceptibility.JointCoat
