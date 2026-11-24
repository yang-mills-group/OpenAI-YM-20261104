import YM.RGLocalTaylor.Engine.Insert

/-!
# Brush integration of inserted log moments, I

Identity from change of variables in the *one* (full covariance)
graph-submatrix Gaussian integral. Generalizes `Shield.finbars`,
`Flux.transition`, parts of `Glass` etc. in CONNECTED_ACTIVITY_JETS_E6
to apertures which will split the actual integral into estimated pieces.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}

namespace Insert

/-- Analytic extension at this ONE roster. Use the gauge-averaged germ
when producing tracked coefficients. Like `bars`, not asserting integrability
at completely off-mask V arguments! -/
def onSlice (r : Insert T) (I : Finset (Tubular f G)) (X : Coat T F) : ℝ :=
  ∫ y, (∫ z, lens₀ (Pond.circuit I X.relating) z * r.value (X.wrapY y) (Pond.spill I z)) ∂F.order G

/-- Same marginal in the Scalp transform convention. -/
def onCourse (r : Insert T) (I : Finset (Bond f)) (A β : ℝ)
    (X : Coat T F) (V : Config G c) (z : Air f G) :=
  scalp I X V β A z * r.value (vary X V) (course X A β z V)

/-- Include the actual shared holding argument, ready for differentiation.
Y coordinates not approximated per factor. -/
def rhythmic (r : Insert T) (I : Finset (Bond f)) (A β : ℝ)
    (X : Coat T F) (V : Config G c) (z : F.Slice G × Air f G) :=
  r.onCourse I A β (X.wrapY z.1) V z.2

end Insert

namespace Fits
variable {I : Finset (Tubular f G)} {r : Insert T} {u : Support c} (h : Fits H r u j)
    (hX : X.x=s) (hK : X.width=o.K)
include h hX hK

lemma sliceBorel : Measurable fun y => r.onSlice I (vary X y) := by
  let E' := (Config G c × F.Slice G) × Body (↥I)
  let V (t:E') := t.1.1
  let Y (t:E') := t.1.2
  let f' (i:E') := lens₀ (Pond.circuit I (vary X (V i)).relating) i.2 * r.value (drive X (V i) (Y i)) (Pond.spill I i.2)
  have hv : Measurable V := measurable_fst.comp measurable_fst
  have he : Intake P T X.x R := hX.symm ▸ H.laws.intake
  have hh := c_measured X.shutter (A:=fun i => (vary X (V i)).plate) (fun i j => (Art.borel_plate X he.ready i j).comp hv)
  have hz : Measurable f' := (bulbB (fun i j => hh.1 i.val j.val : Borel fun i => Pond.circuit I (vary X (V i)).relating) measurable_snd).mul
    (h.along X hX hK E' hv (measurable_snd.comp measurable_fst) ((Pond.spill_m I).comp measurable_snd))
  exact ((hz.stronglyMeasurable.integral_prod_right' (ν:=volume)).integral_prod_right' (ν:=F.order G)).measurable

lemma slice_local {X' : Coat T F} {v : Support c} (ht : u ⊆ v) (hw : Village X X' v) :
    r.onSlice (podium S G v X.B) X = r.onSlice (podium S G v X.B) X' := by
  let I := podium S G v X.B
  have hr : Room P S T X.x := hX.symm ▸ H.laws.data.room
  have he : Pond.circuit I X.relating=Pond.circuit I X'.relating := by ext i j; exact hw.same_cov hr j.val j.property i.val
  change r.onSlice I X=r.onSlice I X'
  unfold Insert.onSlice; rw [he]
  apply integral_congr_ae; filter_upwards with q; apply integral_congr_ae; filter_upwards with y
  exact congr_arg (lens₀ _ _ *·) (h.regional (X.wrapY q) (X'.wrapY q) hX hK v _ _ ht
    ⟨hw.wrap q q (fun _ _=> rfl),fun _ _=> rfl,fun _ _=>Iff.rfl⟩)

variable (V : Config G c) (ha : Canary G A b) (hr : Drivable X A b V)
include V ha hr

lemma onCourse_meas (L : Finset (Bond f)) {E : Type} [MeasurableSpace E]
    {Y : E → F.Slice G} {z : E → Air f G} (he : Measurable Y) (hp : Measurable z) :
    Measurable fun i => r.rhythmic L A R.beta X V (Y i,z i) := by
  let P' i := X.wrapY (Y i)
  let f' x := course (P' x) A R.beta (z x) V
  have hR : Intake P T X.x R := hX.symm ▸ H.laws.intake
  have hΞ : ShellAccess S G X.x W X.width o.γ := by rw [hX,hK]; exact H.laws.data.access
  obtain ⟨hJ,hZ⟩:= Flux.steering L X ha V hr he hp hR.ready hΞ R.beta
  have hm (S : Coat T F) {_V : E → Body (↥(lensS L G))} (he:Measurable _V):=bulbB (fun _ _=> measurable_const : Borel fun i:E=> circuit (lensS L G) S.relating) he
  have hF : Measurable (fun x=> scalp L (P' x) V R.beta A (z x)) := hJ.mul ((show Measurable fun x=> lens₀ (circuit (lensS L G) (vary X V).relating)
      (Pond.swim _ (f' x)) from hm (vary X V) ((swim_m (lensS L G)).comp (show Measurable f' from hZ))).div (hm X ((swim_m (lensS L G)).comp hp)))
  exact hF.mul (h.along X hX hK E measurable_const he (show Measurable f' from hZ))

lemma slice_eq (hp : X.relating.PosDef) (Y : Support c) (hY : u ⊆ Y) :
    let I := edgesM S Y X.B
    r.onSlice (lensS I G) (vary X V)=∫ x, (∫ z,r.rhythmic I A R.beta X V (x,z) ∂X.dice) ∂F.order G := by
  intro I
  unfold Insert.onSlice; apply integral_congr_ae; filter_upwards with x
  let B:= lensS I G; let Z:= X.wrapY x; let A':= circuit B X.relating
  let J:= sweep A'; have hP : MeasurePreserving (swim B) X.dice J := Pond.orbit hp.posSemidef B
  let f' : Air f G → ℝ := r.onCourse I A R.beta Z V
  have hF : Measurable f' := h.onCourse_meas (Y:=fun (_:Air _ G)=> x) (z:=id) hX hK V ha hr I measurable_const measurable_id
  have hB : B=podium S G Y X.B := chargedU _ _
  have htZ := fun q => h.regional (vary Z V) (vary Z V) hX hK q
  have hf : confined (swim B) f' := by
    intro u v hh; unfold f' Insert.onCourse; rw [Flux.slab I Z V u v hh A]; apply congrArg
    have hp := congr_arg (pitch I Z A R.beta V) hh; rw [pitch_alt,pitch_alt] at hp
    exact htZ Y _ _ hY ⟨Village.refl ..,fun i hi=> (Pond.observe B).mp hp i (hB.symm ▸ hi),fun _ _=>Iff.rfl⟩
  have he: Drivable Z A b V := ⟨fun i=> hr.good i⟩
  let F' z:=lens₀ (circuit B (vary Z V).relating) z * r.value (vary Z V) (Pond.spill B z)
  have hb := H.laws.intake.positive
  change (∫ z,F' z) = ∫ z,f' z ∂X.dice
  rw [Pond.gathered (Pond.spill B) (spill_m B) hP (settled _) hf hF]
  change _ = ∫ z, f' (Pond.spill B z) ∂ sweep A'
  rw [gyre I Z ha hb V he F', Shield.recommends A' (show A'.PosDef from hp.submatrix Subtype.val_injective) _]
  apply integral_congr_ae; filter_upwards with y
  let z:= spill B y; let w:= course Z A R.beta z V; let b:=pitch I Z A R.beta V y; let E v:= r.value (vary Z V) v
  have hG : E (Pond.spill B b)=E w :=
    htZ Y _ _ hY ⟨Village.refl ..,fun i hi=> (observe B).1 (settled B b) i (hB.symm ▸ hi),fun _ _=>Iff.rfl⟩
  change jacL _ Z A R.beta V z*(lens₀ _ b*E _)=lens₀ A' y*(scalp I Z V R.beta A z* E w)
  have hh : scalp I Z V R.beta A z=jacL I Z A R.beta V z*(lens₀ (circuit B (vary Z V).relating) b/lens₀ A' y) := by
    unfold scalp; dsimp only; rw [show swim B z=y from settled ..]; rfl
  change jacL _ Z A R.beta V z*(lens₀ (circuit B (vary Z V).relating) b*E _)=lens₀ A' y*(scalp I Z V R.beta A z* E w)
  rw [hG,hh]; field_simp [ne_of_gt (fullFuel A' y)]

-- At a manifest scene, can also read the coefficients as actual moments,
-- no change of variables needed there. Need positivity, and marginal
-- compatibility (even when using only for formal readers of germs).
omit V ha hr in
lemma actual_slice (hp : X.relating.PosDef) (Y : Support c) (hY : u ⊆ Y) :
    r.onSlice (podium S G Y X.B) X=∫ x, (∫ z,r.value (X.wrapY x) z ∂X.dice) ∂F.order G := by
  let B:=podium S G Y X.B
  have hv : (circuit B X.relating).PosDef := hp.submatrix Subtype.val_injective
  unfold Insert.onSlice; apply integral_congr_ae; filter_upwards with y
  let g (z:Air f G):= r.value (X.wrapY y) z
  have hζ : Measurable g := h.along (V:=fun _=>X.V) (Z:=fun (_:Air f G)=>y) (z:=id) X hX hK (Air f G) measurable_const measurable_const measurable_id
  symm
  refine (Pond.gathered (spill B) (spill_m B) (Pond.orbit hp.posSemidef B) (Pond.settled B) ?_ hζ).trans (Shield.recommends _ hv (fun z=>g (Pond.spill B z)))
  intro u v hu
  exact h.regional (X.wrapY y) (X.wrapY y) hX hK Y u v hY
    ⟨Village.refl ..,(Pond.observe B).1 hu,fun _ _=>Iff.rfl⟩

end Fits
end YM.RGLocalTaylor
