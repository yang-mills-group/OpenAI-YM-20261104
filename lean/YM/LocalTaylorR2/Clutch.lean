import YM.LocalTaylorR2.Rinsing

/-!
# Qualitative analytic exchange for an E6 test

Mercury proof with local test arguments for log-perturbed and/or marked inputs.
(This alone does not construct Brush prices.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Port
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Bloch Laurent Channel Next.Foundations Progress.StationaryScenes.Green Census
variable {I : Finset (Bond f)} {j l:ℕ} {A B C' K' d v r b:ℝ} {U : Support c} {K : Test T} {χ : Chi}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config G c} {x : E} {X:Coat T F}
variable (hX : X.x=s) (hM : X.manifest) (hK : X.width=o.K) (htK : Kept H U K)
variable (hq : Glass P X V x j W) (hC : Canary G A b) (he : 8*o.a*Pressure.fiery G s L ≤ A/2)
include hX hM hK htK hq hC he
lemma periodExchange (I:Finset (Bond f)) :
    let m:=(F.order G).prod X.dice; let g v:= duoTilt R.beta I X (V v) A K
    Meristem g x m j ∧ ∀ᶠ y in 𝓝 x, Integrable (g y) m := by
  intro m g
  have heq:=H.laws.data; have hv := heq.funds.length_eq; rw [← hv,← hX] at he
  have hM :=heq.localP F X hX hK hM
  have ht:= (hX.symm ▸ H.laws.intake : Intake P T X.x R); have hh: ShellAccess S G X.x W X.width o.γ := by rw [hK,hX]; exact heq.access
  let A' := lensS I G; let U i:=circuit A' (vary X (V i)).relating; let V':= circuit A' X.relating
  have hx: U x=V' := by unfold U V'; rw [hq.lifts]; rfl
  have hF:= hM.sails.fullC; have hU' : V'.PosDef := hF.submatrix Subtype.val_injective
  have hV:= own_mat hM.sails I
  have hs : Bottom V'⁻¹ (1+payE o.eta o.gap o.ample (tubularPrice G L))⁻¹ := Control.lower_inverse hV.relented hV.weather.1.le hV.fuel hV.symmetry
    hV.ground hV.down.le hV.initial.1
  let X'(t:F.Slice G × Air f G):= X.wrapY t.1; let w t v:= course (X' t) A R.beta t.2 (V v)
  let z(t:F.Slice G×Air f G):= Pond.swim A' t.2; have hZ : MeasurePreserving z m (sweep V') := by
    have hs := (Pond.orbit hF.posSemidef A')
    apply hs.comp (show MeasurePreserving _ m X.dice from _); exact MeasureTheory.measurePreserving_snd
  let Z t i:= Pond.swim A' (w t i)
  obtain ⟨hΞ,hω⟩:= Glass.towers (U:=fun i:F.Slice G × Air f G=> i.2) (Y:=fun i=> i.1) hq hM.sails.room hC I ht.positive
  obtain ⟨B,hB,hk,hP⟩:= winglet (A:=U) (Z:=z) (V:=Z) (hx.symm ▸ hU') (hx.symm ▸ hs) (inv_pos.mpr hV.fuel)
    (fun i j=>hq.relate i.val j.val) hω
  let Φ i v:= K F (vary (X' i) (V v)) (w i v)
  have hax : 8*o.a*Pressure.fiery G s L ≤ A/2:= by rw [← hv,← hX]; exact he
  have hΨ : Zest Φ x j:= htK.clutch F X hX hK (by assumption) j A b E V x hq hC hax
  obtain ⟨J,hJ,hH⟩:= hΞ.post
  obtain ⟨K,h₁,h₂⟩:=hΨ.post
  refine Meristem.points g m ?_ ?_
  · let K' t:=(J*B (z t)*K)*(1+((1+1)+1))^j
    rw [hx] at hk
    have hb : Integrable (B ∘ z) m := (hZ.integrable_comp hB.aestronglyMeasurable).2 hk
    refine ⟨K',((hb.const_mul J).mul_const K).mul_const _,?_⟩
    filter_upwards [hH,h₂,hP] with i hi h hh s
    have hx' := hh s
    -- convert density origin
    rw [hx] at hx'
    exact (((hi s).paints hx').paints (h s)).trim
  obtain ⟨s,h⟩:= hq.sails; filter_upwards [nearby X hC hq.lifts h] with y hh'
  exact measurableTilt I X (V y) hC hh' hX hK htK measurable_fst measurable_snd

lemma slopes :
    let m:=(F.order G).prod X.dice; let I:=edgesM S U (radiusB s)
    (fun y=> average (vary X (V y)) (podium S G U (radiusB s)) K) =ᶠ[𝓝 x]
       fun v=>∫ y, duoTilt R.beta I X (V v) A K y ∂m := by
  intro m I; obtain ⟨_,ht⟩:= periodExchange hX hM hK htK hq hC he I
  obtain ⟨v,hv⟩:= hq.sails
  filter_upwards [ht,nearby X hC hq.lifts hv] with y hy hY
  rw [← chargedU U (radiusB s), integral_prod _ hy]
  apply recoilLaw _ X _ hC hY hX hK htK (H.laws.data.localP F X hX hK hM).sails.fullC
  change edgesM S _ _=edgesM S _ (radiusB X.x); rw [hX]

omit hX hM hK htK hq hC he

/-- Pre-mask PRICE, not a quantitative premise on the result of the step;
the local-order producer pays these through any finite requested log powers. -/
structure IntegrandCost (_H : Cash W s μ L Q o C T R) (U:Support c) (K:Test T) (j : ℕ) (A v e : ℝ) (χ : Chi) : Prop where
  bound : ∀ (F:Forest S.ratio) (X:Coat T F), X.x=s → X.width=o.K → X.manifest → X.χ=χ → Healthy (Pressure.temp s) U X.V →
    ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (V:E→ Config G c) (x:E),
    Mode V x j v → V x=X.V →
    let m:=(F.order G).prod X.dice; let I:=edgesM S U (radiusB s)
    ∃ f, Integrable f m ∧ (∫ t,f t ∂m) ≤ e ∧
      ∀ w, Brush j (f w) 1 (fun y=> duoTilt R.beta I X (V y) A K w) x
variable {Ξ : Utopia H j v d r C' χ}
include hX hM hK htK
lemma lands (hC : Oboe H j v B l A b Ξ) (hp:IntegrandCost H U K j A v K' χ)
    (hz:X.χ=χ) (hU:Healthy (Pressure.temp s) U X.V) (hV: Mode V x j v) (hx: V x=X.V):
    Brush j K' 1 (fun y=> average (vary X (V y)) (podium S G U (radiusB s)) K) x := by
  let I:= edgesM S U (radiusB s)
  let hq:=hC.flow F X hX hz hK hM E V x hx hV
  obtain ⟨f,hf,h,p⟩:= hp.bound F X hX hK hM hz hU E V x hV hx
  exact ((periodExchange hX hM hK htK hq hC.conduit hC.mode I).1.buds f hf zero_le_one h
    (Filter.Eventually.of_forall p)).shimmy (slopes hX hM hK htK hq hC.conduit hC.mode)


end YM.LocalTaylorR2.Port
