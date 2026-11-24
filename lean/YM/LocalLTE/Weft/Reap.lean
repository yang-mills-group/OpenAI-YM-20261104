import YM.LocalLTE.Weft.Market
/-! Budget continuity for μ push predictor. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Mask Matter Coat Frond
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Fan Brush Foramen Pastel
variable {v z r W w s t y η γ B a ε α : ℝ} {j n m N M : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open Weft AnalyticBridge.VerifiedReset FrameBox
variable {κ k₁:ℝ}
variable (X:Coat T F) (Φ:ℕ→ℝ→ Config G f→ℝ) {μ:ℝ}
local notation "E"=> Disk G c
lemma vines_t (H: Cash W t μ L Q o a T R)(hp:X.x=t)(hX:X.width=o.K)(p:Disk G c) (i: Veil c f)(s:ℝ)(hs:s∈clip)(Φ:ℕ→ℝ→ Config G f→ℝ)(u:ℕ→ℝ)(η:ℝ) 
     (hκ:Reliable G κ k₁) (J N M n:ℕ)(hf:labelGrade (c:=c) R κ Φ u N M J n η i): Measurable fun z=> coming Q.table (Fan.vest R Φ s) X p z i:=by
  let Z:=timeΛ X p; let u z :=switchΛ X z p
  have he : Measurable u:= measurable_const.add (Measurable.smul (measurable_const (a:=p.1)) (measurable_pi_lambda _ fun i=> (X.tale i).measurable))
  have h:Measurable fun z:Air f G=> inputΛ X z p:= by
    simp_rw [openingΛ]; apply Z.summon (Y:=fun _:Air f G=> Z.Y) measurable_const he
  let A:=-(s^2)⁻¹*orientation
  have ht {d:ℕ}(P:ℕ→Atom G d)(i:Trans f)(b:ℝ) : Measurable fun z=> atomΛ X P i b z p:= measurable_const.mul (((Atom.unmasked_cont ..).measurable).comp ((continuous_pull ..).measurable.comp h))
  have hM:=H.laws.data
  rcases i with i|i|i|i|i
  · obtain ⟨I,hI,V,he⟩:= (show CanX .. from hf).basis; exact ((he.beacon s hs hκ).comp h).neg
  · exact ht _ _ _
  · exact ht _ _ _
  · exact ht _ _ _
  rcases i with i|i|i
  · change Measurable fun z=> A*sourceΛ X i z p; apply Measurable.mul measurable_const
    have hh z: sourceΛ X i z p=Polar.rootface Z (u z) (Z.input (u z)) true i.1 i.2+ Vine.costs Z (voltage Z) i.1 i.2:= congr_arg (fun x=> x+Vine.costs Z (voltage Z) i.1 i.2) ((Vine.patch_rep X (Vine.pass p) (u z) i).symm)
    simp_rw [hh]; apply Measurable.add _ measurable_const; unfold Polar.rootface
    apply Measurable.sub; apply Shield.liftB hM.funds.funds measurable_const
    apply (continuous_pull ..).measurable.comp
    exact Z.summon (Y:=fun _:Air f G=> Z.Y) measurable_const he
    refine Finset.measurable_fun_sum _ fun i' _=> ?_; unfold Vine.pot; split; next=> exact ((((Shield.strains hM.funds.funds (V:=fun _:Air f G=>Z.V) measurable_const Z (Y:=fun _:Air f G=> Z.Y) measurable_const (show ShellAccess S G Z.x W Z.width o.γ from by change ShellAccess _ _ X.x W X.width _; rw [hp,hX]; exact hM.access) he _ i').norm).pow_const (2:ℕ)).div_const 2)
    exact measurable_const
  · exact measurable_const (a:=Z.undercurrent i)
  change Measurable fun z=> solar X z Q.table p i; unfold solar; split
  next h=> exact Real.measurable_log.comp (Q.table_exists.borel.comp ((measurable_pi_apply i).comp he)) -- edit
  exact measurable_const

open Bakers
variable (H:Cash W t μ L Q o a T R) (he:X.x=t) (hv:X.width=o.K) (hκ:Reliable G κ k₁) (J N M n:ℕ) (u:ℕ→ℝ)(D : Finset (Veil c f))(hf:∀ i∈D,labelGrade R κ Φ u N M J n η i)
include H he hv hκ hf in
lemma canvasT (s:ℝ)(hp:s∈clip)(z:Disk G c)(v: Bakers.LevelsΛ D j)(I : Finset (Tubular f G)): Measurable fun w => songP X (Fan.vest R Φ s) D Q.table I z w v :=by
    have ht i (hi:i∈D):=(vines_t X H he hv z i s hp Φ u η hκ J N M n (hf _ hi)).comp (Pond.spill_m I)
    let f (x:E)(z:Body (↥I)):= lens₀ (planeQ X I (Vine.pass x)) z
    have he x : Measurable (f x):= bulbB (z:=id) (S:=fun _=> planeQ X I (Vine.pass x)) (fun _ _=> measurable_const) measurable_id -- edit
    exact (Measurable.div (he z) (show Measurable (f 0) from he _)).mul (Finset.measurable_fun_prod _ fun k _=> measurable_const.mul ((ht k.val k.property).pow_const _))
lemma profileHex {EC:Type} {F:ℝ→EC→Veil c f→ℝ} (h:∀ i∈D,Hex J (fun s x=> F s x i)) (p:LevelsΛ D M) : Hex (J*M*D.card) (fun s x=> lilies D (F s x) p):= by
    apply Hex.invert; intro x
    have he i: Hex (J*M) (fun s=> ask (F s x (i:↥D)) (p i)):=by
       have ht:= (((h i i.property).use x).powers ((p i).val+1)).oneZ ((Nat.factorial ((p i).val+1):ℝ)⁻¹); exact ht.grow (Nat.mul_le_mul_left _ (p i).2)
    have hp:= Hex.product (Finset.univ:Finset D) (v:=fun s i=> ask (F s x i.val) (p i)) (fun i _=> he i); rw [card_univ,Fintype.card_coe] at hp; exact hp
lemma cargo (φ:Veil c f→ℝ){F:ℝ→E→Veil c f→ℝ}{p:E}{s:ℝ}(he:∀ i∈D,Brush j (φ i *w) 1 (fun x=>F s x i) p)(h:1≤w)(hφ:∀ i∈D,0≤φ i∧ φ i≤1)(m:ℕ)(U:LevelsΛ D m)(ht:D.card≤J): Brush j ((∏ i∈D,φ i)*(w^m)^J) (J*m) (fun x=> Bakers.lilies D (F s x) U) p:=by
    have hp:= Bakers.brushL (u:=fun i=>φ i*w) D (fun i hi=>he i hi) U
    refine hp.climb (le_trans (?_) (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_pow₀ h) ht) (prod_nonneg fun _ hi=> (hφ _ hi).1))) (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ht) (Nat.cast_nonneg m))
    unfold pact; simp_rw [mul_pow,Finset.prod_mul_distrib]; apply mul_le_mul (show pact D φ U≤ _ from (paid D φ (fun i hi=>(hφ i hi).1) (fun i hi=>(hφ i hi).2) U).2) _ (prod_nonneg (fun _ _=> by positivity)) (prod_nonneg (fun i hi=>(hφ i hi).1)); apply le_trans (b:=∏ _i:↥D,w^m) _ (le_of_eq (by simp)); exact prod_le_prod (fun i _=>pow_nonneg (zero_le_one.trans h) _) fun k _=> pow_le_pow_right₀ h (U k).2
end YM.LocalLTE.Fan
