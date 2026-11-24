import YM.LocalLTE.Fan.Dazzle
/-! Relative Bochner equalities and value transfer at B. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan.Bakers
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Pastel
variable {v z r W w s t y η γ B a μ: ℝ} {j n m N M : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
variable (X:Coat T F)
local notation "E"=> Disk G c
variable (D: Finset (Veil c f)) (I:Finset (Tubular f G))(p:Disk G c)(H:Cash W t μ L Q o a T R)(he:X.x=t)(hK:X.width=o.K)
include H he hK
lemma commerce (q: LevelsΛ D N): Measurable fun z=> Bakers.songP X R D Q.table I p z q:=by
  have ht i:= (vines_b X H he hK p i).comp (Pond.spill_m I)
  let f (x:E)(z:Body (↥I)):= lens₀ (planeQ X I (Vine.pass x)) z
  have he x : Measurable (f x):= bulbB (z:=id) (S:=fun _=> planeQ X I (Vine.pass x)) (fun _ _=> measurable_const) measurable_id
  exact (Measurable.div (he p) (show Measurable (f 0) from he _)).mul (Finset.measurable_fun_prod _ fun k _=> measurable_const.mul ((ht k.val).pow_const _))

section
variable (hi:(timeΛ X p).manifest)
include hi
lemma swapping (s:Set (Body (↥I)))(hp:MeasurableSet s)(g:Body (↥I)→ℝ) : ∫ z in s,g z ∂ Fan.pool I X p=∫ z in s, pledgeΛ X I z (Vine.pass p)*g z ∂ Fan.pool I X 0:=by
  let K:=Fan.pool I X p; let S:=Pond.circuit I (timeΛ X p).relating
  have hs: S.PosDef:=(H.laws.data.localP F (timeΛ X p) (show (timeΛ X p).x=t from he) (show (timeΛ X p).width=o.K from hK) hi).sails.fullC.submatrix Subtype.val_injective
  let V:=timeΛ X (0:E); have hv:V=X.blank:=by unfold V timeΛ Vine.pass dry; rw [show ((0:E).snd,(0:Directions G f)).1=0 from rfl,Work.G07.at_zero_increment]; rfl
  have hK' : V.relating.PosDef:= by rw [hv]; exact (H.laws.data.localP _ X.blank he hK (X.bowed (temp_nonneg _))).sails.fullC
  rw [←MeasureTheory.integral_indicator hp, ← MeasureTheory.integral_indicator hp]
  unfold Fan.pool; rw [recommends _ hs, recommends _ (show (Pond.circuit I (timeΛ X (0:E)).relating).PosDef from hK'.submatrix Subtype.val_injective)]
  refine integral_congr_ae (ae_of_all _ fun x=> ?_); dsimp only; by_cases he:x∈s
  · rw [Set.indicator_of_mem he, Set.indicator_of_mem he]; change lens₀ (circuit I (timeΛ X p).relating) x*g x = lens₀ (Pond.circuit I (timeΛ X (0:E)).relating) x*(lens₀ (Pond.circuit I (timeΛ X p).relating) x / lens₀ (Pond.circuit I (timeΛ X (0:E)).relating) x* _); field_simp [(fullFuel (Pond.circuit I (timeΛ X (0:E)).relating) x).ne']
  rw [Set.indicator_of_notMem he, Set.indicator_of_notMem he]; simp
variable {d:ℝ}(hp:d=postponement L t o)(hT:SliceRows.Stamp T)(x : Directions G c)(hP:p=(gStep R.beta,x))
include hp hT hP
lemma ancestry (q:LevelsΛ D N) : curlP X R D Q.table d I p q=∫ z in cabinet I d, lilies D (fun i=> Fan.vows X R Q o.a p (Pond.spill I z) i) q ∂Fan.pool I X p:=by
  rw [swapping X I p H he hK hi _ (alive I _)]; subst d; refine MeasureTheory.setIntegral_congr_fun (alive I _) fun x' hx => ?_
  have h: 0 ≤ postponement L t o:= by unfold postponement; have hf:= Delay.monitor_pos G L t; have hh:=o.rare; positivity
  unfold songP; rw [Fan.longing X H he hK hT x p hP hi (Pond.spill I x') (fur I hx h)] -- unfold during proof defeq
variable (hB:0<B)(f₀:Veil c f→ℝ)(w:Veil c f→ℝ)(hw:∀ i∈D,0≤f₀ i)(hw':∀ i∈D,f₀ i ≤ 1)(hZ:∀ i∈D,∀ b:Air _ _, |vows X R Q o.a p b i| ≤ f₀ i* B^(w i))
local notation "Z"=> ∏ i∈D,f₀ i
include hZ hw hB hw'
lemma taxing (q:LevelsΛ D N) : let P:= (∏ i∈D,f₀ i)*B^(tones D w q); let g z:= lilies D (fun i=>vows X R Q o.a p (Pond.spill I z) i) q
    (∀ b:Body (↥I), |g b| ≤ P) ∧ Integrable g (Fan.pool I X p) ∧ ‖curlP X R D Q.table d I p q‖ ≤ P:= by
  intro P g
  have hb:P≥0:= mul_nonneg (prod_nonneg hw) (Real.rpow_nonneg hB.le _)
  have hv (b:Body (↥I)): |g b| ≤ P:= (Bakers.valueL D (fun i=> f₀ i* B^(w i)) _ (fun i hi=>hZ i hi (Pond.spill I b)) q).trans (((pastel D _ _ hB q)).trans_le (mul_le_mul_of_nonneg_right (paid D f₀ hw hw' q|>.2) (Real.rpow_nonneg hB.le _)))
  have hI: Integrable g (Fan.pool I X p) := (integrable_const P).mono' (show Measurable g from Finset.measurable_fun_prod _ fun i _=> Measurable.mul measurable_const (((vow_b X H he hK _ p).comp (Pond.spill_m I)).pow_const ((q i).val+1))).aestronglyMeasurable (ae_of_all _ hv)
  refine ⟨hv,hI,?_⟩; rw [ancestry X D I p H he hK hi hp hT x hP q]; refine (MeasureTheory.norm_integral_le_integral_norm ..).trans ?_
  apply (integral_mono (hI.norm.integrableOn) (integrable_const P) hv).trans
  rw [setIntegral_const]; exact mul_le_of_le_one_left hb measureReal_le_one
lemma packed (n:ℕ): (∫ z in cabinet I d, Bakers.barge D X p n R Q o.a (Pond.spill I z) ∂ Fan.pool I X p)= ∑ q:LevelsΛ D n, curlP X R D Q.table d I p q:=by
    have ht (z : Body (↥I)): Bakers.barge D X p n R Q o.a (Pond.spill I z) = (∑ i:LevelsΛ D n, lilies D (fun i=> Fan.vows X R Q o.a p (Pond.spill I z) i) i):=fixture D _ _
    simp_rw [ht]; rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _=>(ancestry X D I p H he hK hi hp hT x hP i).symm
    exact fun i _=> (taxing X D I p H he hK hi hp hT x hP hB f₀ w hw hw' hZ i).2.1.integrableOn
end
end YM.LocalLTE.Fan.Bakers
