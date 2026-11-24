import YM.LocalLTE.MarkPT.Crop

/-! The genuine finite signed Mayer wing, its common measured and reference apertures, and the polylogarithmic physical tariff. -/
set_option autoImplicit false

noncomputable section
namespace YM.Integration.WilsonLowMayerRoster
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
open PhysicalNext.Repeat.Brim
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height LocalLTE LocalLTE.Fan LocalLTE.Fan.Pastel
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
  {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
  {R : RG.Rep G f} {μ s α : ℝ} {ℓ : ℕ} {χ : Chi} {H : Cash W s μ L Q o α T R}

/-- Spark, the actual eligibility of each partner, and the original numeric cutoff suffice. -/
theorem retained (u : H.fragrances) (hx : ¬YM.PhysicalNext.Repeat.Height.tiredN H ℓ u)
    (hv : ∀i,Ac.Spark H.supportP (u.2 i).val ∧ troupe T R Q.halo (radiusB s) (u.2 i).val)
    (i : Option (Fin u.1)) (w : Head S) (hw : w∈(u.2 i).val) : w∈Set.range (Fan.elastic (S:=S)) := by
   have hi:=(YM.PhysicalNext.Repeat.Height.aged hv hx).1 i
   let p:=u.2 i
   let k:=Fan.elastic (S:=S)
   have hh w (hf:w∈p.val): w∈Set.range k := by
     rcases w with w|w
     · have hL:= mem_toLeft.mpr hf; rw [hi.unforced] at hL; exact (notMem_empty _ hL).elim
     have he' : Silica.hornN ℓ w < ℓ := by
        have h:Silica.hornN ℓ w ≤ acmeN H ℓ u:= le_trans (b:=pinsN ℓ S p.val) (single_le_sum (f:=Sum.elim _ _) (fun _ _=>Nat.zero_le _) hf) (single_le_sum (f:=fun j=> pinsN ℓ S (u.2 j).val) (fun _ _=> Nat.zero_le _) (mem_univ i))
        have hv:= lt_of_not_ge (not_or.mp hx).1; unfold degreeN at hv; omega
     rcases w with w|w|w
     · have hv: w∈ own (u.2 i).val:= mem_toLeft.mpr (mem_toRight.mpr hf); rw [hi.noK] at hv; exact (notMem_empty _ hv).elim
     · rcases w with w|w|w
       · rcases w with w|w|w|w|w|w
         · exact ⟨.inl w,rfl⟩
         · exact ⟨.inr (.inl w),rfl⟩
         · exact ⟨.inr (.inr (.inl w)),rfl⟩
         · exact ⟨.inr (.inr (.inr (.inl w))),rfl⟩
         all_goals exfalso; change ℓ+2<ℓ at he'; omega
       · exact ⟨.inr (.inr (.inr (.inr w))),rfl⟩
       exfalso; change ℓ+2<ℓ at he'; omega
     exfalso; change ℓ+2<ℓ at he'; omega
   exact hh w hw

/-- Independently signed true leaf selections and all unmarked spectator labels remain in this statement. -/
theorem marked {ι : Type} [Fintype ι] (M : ι→PhysicalNext.Repeat.Lotus.Leaf R)
    (u : H.fragrances) (D : Oscars M u) (U : Config G c)
    (live : ∀i,Captain.waltz H χ M (u.2 i) (D i) U≠0) (low : ¬YM.PhysicalNext.Repeat.Height.tiredN H ℓ u) :
    ∀i w,w∈(u.2 i).val→w∈Set.range (Fan.elastic (S:=S)) := by
  have h i:=Captain.silenced M (u.2 i) (D i) U (live i)
  exact retained u low (fun i=>⟨(h i).1,(h i).2.1⟩)

end YM.Integration.WilsonLowMayerRoster
end

noncomputable section
namespace YM.LocalLTE.Fan.MeasuredRows
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open YM.ConnectedActivityE6.Blaze.Silica
open Brush Foramen Pastel Polar Clutch Strokes
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}

/-- This is the actual `Cash` portfolio on all the original supports, including every original forced partner. -/
theorem purchased (H : Cash W s μ L Q o t T R) :
    (∀ i, 0 ≤ H.w i ∧ H.w i ≤ Q.goal L s) ∧
      ∀ (F : Forest S.ratio) (X : Coat T F), X.x=s → X.width=o.K →
        ∀ (p : Disk G c), (timeΛ X p).manifest → ∀ (i : Veil c f) (z : Air f G),
          |Fan.vows X R Q o.a p z i| ≤ H.w (Fan.chapter i) := by
  constructor
  · intro i
    let v : Alphabet c f := .inr (.inl i)
    have hrel : 0 ≤ Q.relative := by unfold Target.relative; linarith [Q.usable,Q.bound,Q.pos]
    exact ⟨H.fares.nonneg v,H.fares.atom hrel Q.usable.le v (show (roadway T R (radiusB s) Q.halo i).Nonempty from exChart ..)⟩
  intro F X hx hw p hmanifest i z
  let Y := timeΛ X p
  let b := worldZ Y R.beta z
  have hy : Y.x=s := hx
  have hr : Room P S T Y.x := hy.symm ▸ H.laws.data.room
  have hl : Y.liftA R.beta z=b := Vine.shine Y hr hmanifest _ _
  have healthy : Healthy (Pressure.temp Y.x) (roadway T R Y.B Q.halo (Fan.chapter i)) Y.V := by
    unfold Healthy
    rw [show RG.flags (Pressure.temp Y.x) Y.V=∅ from hmanifest.symm]
    simp
  have h := Polar.leisure Y o.a R Q.table hr hmanifest Q.buys z b hl (Fan.chapter i) healthy
  change Real.exp (Y.farLog R o.a Q.table z (Fan.chapter i))-1 = Real.exp (Fan.vows X R Q o.a p z i)-1 at h
  have hd := Real.exp_injective (sub_left_inj.mp h)
  rw [←hd]
  exact ((H.quotes F Y hy (show Y.width=o.K from hw) hmanifest).2.1 (Fan.chapter i) z).1

theorem logarithm (x : ℝ) (hx : |x| ≤ 1) : |x| ≤ Real.exp 1 * |Real.exp x - 1| := by
  by_cases hp : 0 ≤ x
  · have h := Real.add_one_le_exp x
    rw [abs_of_nonneg hp, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hp))]
    exact (show x ≤ Real.exp x - 1 by linarith).trans (le_mul_of_one_le_left
      (sub_nonneg.mpr (Real.one_le_exp hp)) (Real.one_le_exp zero_le_one))
  have hn : x ≤ 0 := le_of_not_ge hp
  have hv : -x ≤ 1 := (neg_le_abs x).trans hx
  have hh : 0 ≤ 1-Real.exp x := sub_nonneg.mpr (Real.exp_le_one_iff.mpr hn)
  rw [abs_of_nonpos hn, abs_of_nonpos (by linarith : Real.exp x - 1 ≤ 0), neg_sub]
  calc
    -x ≤ Real.exp (-x)-1 := by linarith [Real.add_one_le_exp (-x)]
    _ = Real.exp (-x)*(1-Real.exp x) := by
      rw [mul_sub, mul_one, ←Real.exp_add, neg_add_cancel, Real.exp_zero]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hv) hh

/-- Constant physical variations retain all original Gaussian coordinates. -/
theorem conductor (H : Cash W s μ L Q o t T R) {χ : Chi} {d v r C : ℝ}
    (Ξ : Utopia H j v d r C χ) (hd : 0 ≤ d) (hv : 0 ≤ v) (X : Coat T F)
    (hx : X.x=s) (hw : X.width=o.K) (hc : X.χ=χ) (p : Disk G c)
    (hm : (timeΛ X p).manifest) (i : Veil c f) (z : Air f G) :
    |Real.exp (Fan.vows X R Q o.a p z i) - 1| ≤ Ξ.fare (Fan.elastic (S:=S) i) := by
  let Y := timeΛ X p
  let u := worldZ Y R.beta z
  have hy : Y.x=s := hx
  have ht : 0 < Y.t := (hy.symm ▸ H.laws.data.room : Room P S T Y.x).fiery
  have hc' : Clutch Y z o.a R.beta d (0:ℝ) j (fun _ => Y.V) (fun _ => u) (fun _ => z) := by
    refine ⟨rfl,H.laws.intake.positive,rfl,mul_pos o.large ht,fun _=>rfl,hd,?_,?_⟩
    · intro i
      simpa only [u, sub_self, norm_zero] using
        (Brush.certified (E:=ℝ) (k:=j) (x:=(0:ℝ)) (d:=1) zero_le_one (0:G.Color)).climb
          (by simpa only [norm_zero] using hd) le_rfl
    · apply Filter.Eventually.of_forall
      intro y
      exact ⟨fun _ _ => rfl,mul_pos (mul_pos zero_lt_two o.large) ht⟩
  have ha : Mode (fun _ : ℝ => Y.V) 0 j v := ⟨hv,fun e => a_oneB G _ hv⟩
  have hs : Healthy (Pressure.temp Y.x) (H.supportP (Fan.elastic (S:=S) i)) Y.V := by
    unfold Healthy
    rw [show RG.flags (Pressure.temp Y.x) Y.V=∅ from hm.symm]
    simp
  have he := (Ξ.stream ℝ F Y (fun _=>Y.V) (fun _=>u) (fun _=>z) 0 z hx hw hc hm ha hc' ∅
    (Fan.elastic (S:=S) i) hs).bound
  change ‖Real.exp (Fan.vows X R Q o.a p z i)-1‖ ≤ Ξ.goalsL (Fan.chapter i) at he
  exact he

/-- The minimum takes the original scalar cap and retains the independently admitted rooted portfolio. -/
theorem same_fee (H : Cash W s μ L Q o t T R) {χ : Chi} {d v r C : ℝ}
    (Ξ : Utopia H j v d r C χ) (hd : 0 ≤ d) (hv : 0 ≤ v) (hcap : Q.goal L s ≤ 1)
    (X : Coat T F) (hx : X.x=s) (hw : X.width=o.K) (hc : X.χ=χ) (p : Disk G c)
    (hm : (timeΛ X p).manifest) (i : Veil c f) (z : Air f G) :
    |Fan.vows X R Q o.a p z i| ≤ min (H.w (Fan.chapter i)) (Real.exp 1 * Ξ.fare (Fan.elastic (S:=S) i)) := by
  have ha := (purchased H).2 F X hx hw p hm i z
  exact le_min ha ((logarithm _ (ha.trans (((purchased H).1 _).2.trans hcap))).trans
    (mul_le_mul_of_nonneg_left (conductor H Ξ hd hv X hx hw hc p hm i z) (Real.exp_pos _).le))

theorem stored (H : Cash W s μ L Q o t T R) (i : Veil c f) :
    H.text (Fan.elastic (S:=S) i) = H.w (Fan.chapter i) := rfl

/-- Buying the original row reserve at one quarter of the clock permits every original field degree and keeps the common raw weights. -/
def cut (β : ℝ) := β^(1/4:ℝ)

theorem envelope (β : ℝ) (hb : 1≤β) (y : LogIndex c f → ℝ)
    (hy : ∀i, 0≤y i ∧ y i≤β^(-(15/32:ℝ))) (i : Veil c f) :
    let d := (cut β)^(Fan.levy (fun _ => 0) i)
    0<d ∧ 0≤y (Fan.chapter i)/d ∧ y (Fan.chapter i)/d≤1 ∧ y (Fan.chapter i)/d*d=y (Fan.chapter i) := by
  intro d
  have hb' : 0<β := zero_lt_one.trans_le hb
  have hpos : 0<d := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hb' _) _
  have hcost : β^(-(15/32:ℝ)) ≤ d := by
    unfold d cut
    rw [← Real.rpow_mul hb'.le]
    apply Real.rpow_le_rpow_of_exponent_le hb
    rcases i with i|i <;> norm_num [Fan.levy,Fan.Pastel.chip,Fan.Pastel.slack,Fan.Pastel.mini]
  exact ⟨hpos,div_nonneg (hy _).1 hpos.le,(div_le_one hpos).2 ((hy _).2.trans hcost),div_mul_cancel₀ _ hpos.ne'⟩

end YM.LocalLTE.Fan.MeasuredRows

noncomputable section
namespace YM.LocalLTE.Fan.MeasuredCinema
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open FrameBox Pastel Merge Merge.Palette
variable {ι : Type} [Fintype ι] (M : ι → Lotus.Leaf R)
variable (Q : YM.ConnectedActivityE6.Target G P) (D : Merge.Tickets (Merge.Palette.sign M S))
    (H : Cash W t μ L Q o a T R) (X : Coat T F) (p : Disk G c)
    (L' : Finset (Veil c f)) (Y : Molecule S) (hh : D.reach ⊆ Y) (hq : Y\D.reach = Fan.arm L')
    (I : Finset (Tubular f G)) (hX : X.x=t) (hK : X.width=o.K) (hp : (timeΛ X p).manifest)
set_option quotPrecheck false
local notation "mΦ" => (fun i => (M i).ingredient)
local notation "PV" => Fan.pool I X p
local notation "CA" => cabinet I (postponement L t o)
open Bakers

/- At the true good measured material the original raw signed product needs no polynomial replacement. -/
include H hX hK hp in
omit [Fintype ι] in
theorem painted (hT : Stamp T) (b : Air f G) (x : Directions G c) (hβ : p=(gStep R.beta,x))
    (hf : ∀ i : Tubular f G, |b i| ≤ postponement L t o) :
    payment (o:=o) M D X p b = oils M mΦ D X p b := by
  obtain ⟨ht,h,_⟩ := Fan.incomeA X H hX hK hT x p hβ hp b hf
  unfold payment Team.paidU team
  rw [Finset.prod_image]
  · refine prod_congr rfl fun i hi => ?_
    unfold Leaf.paidU Leaf.fond
    rw [h, ←ht, mul_one]
  · exact fun i hi j hj hz => D.prop hi hj (congr_arg (fun i : Leaf R => i.turn.badge S) hz)

include H hX hK hp in
omit [Fintype ι] in
theorem cabinet_read (x : Directions G c) (hx : p=(gStep R.beta,x)) (hT : Stamp T) (m : ℕ) :
    wishes (L:=L) (o:=o) M mΦ Q D X L' I t m p = ∫ z in CA,
      payment (o:=o) M D X p (Pond.spill I z) * Bakers.barge L' X p m R Q o.a (Pond.spill I z) ∂PV := by
    rw [Bakers.swapping X I p H hX hK hp _ (alive ..)]; apply MeasureTheory.setIntegral_congr_fun (alive ..); intro i hi
    let z:= Pond.spill I i; have h: 0 ≤ postponement L t o:= by unfold postponement; have hf:= Delay.monitor_pos G L t; have hh:=o.rare; positivity
    have hb:∀ j,|z j|≤postponement L t o:= fur I hi h
    have he':= Fan.longing X H hX hK hT x p hx hp z hb; dsimp only; rw [painted M Q D H _ _ hX hK hp hT _ x hx hb]; -- order
    refine congr_arg₂ (·*·) rfl (congr_arg₂ (·*·) rfl (Finset.prod_congr rfl fun i hi=>congr_arg _ (congr_fun he' i)))

variable (hI: 1≤B)(r:ℕ→ℕ)(z:Veil c f→ℝ)(hZ:∀ i∈L',0≤z i ∧ z i≤1 ∧ ∀ b:Air f G, |vows X R Q o.a p b i| ≤ z i*B^(levy r i))
include hX hK hp H hh hq hI hZ
local notation "ℋ"=> (2+Real.exp 1)
local notation "ℙ"=> (team M D).weight
omit [Fintype ι] in
theorem component (hT:Stamp T) (x:Directions G c)(hβ:p=(gStep R.beta,x))(m:ℕ)(k:ℝ) (hk:(PV).real (cabinet I (postponement L t o))ᶜ ≤ k): let w:=wishes (L:=L) (o:=o) M mΦ Q D X L' I t m p; let f':=(team M D).qlocal4a_cinema (timeΛ X p) Y W o.a Q.table Q.halo I; let u:=ℙ*(ℋ^L'.card* (∏ i∈ L',z i)); ‖w‖≤u∧|f'-w|≤u*(k+L'.card*(B^Pastel.mini)^m):=by
  intro w f' u
  let b i:= payment (o:=o) M D X p (Pond.spill I i)
  let Θ i:= node X p R Q o.a L' (Pond.spill I i)
  let f i:= b i * Θ i
  let ξ i:= Bakers.barge L' X p m R Q o.a (Pond.spill I i); let g i:= b i* ξ i
  have hb:0<B:=zero_lt_one.trans_le hI; let d:=L'.card; have hr:0<(B:ℝ)^Pastel.mini:=Real.rpow_pos_of_pos hb _
  have hh₁:B^mini≤1:= Real.rpow_le_one_of_one_le_of_nonpos hI (by unfold mini; norm_num)
  have ht i (hi:i∈L')(b): |vows X R Q o.a p b i| ≤ z i*B^mini:= (hZ i hi|>.2.2 b).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hI (financial _ _ _ _)) (hZ i hi|>.1))
  let f₀ := ℋ^d*(∏ i∈L',z i); let V:=ℙ*f₀; have hR:0≤ℙ := (team M D).profit
  have hF'(x:Body (↥I)): ‖Θ x‖ ≤ f₀ ∧ ‖ξ x‖ ≤ f₀∧ ‖Θ x-ξ x‖≤ f₀*(d*(B^mini)^m):= Bakers.rays (D:=L') (p:=fun i=> vows X R Q o.a p (Pond.spill I x) i) z (fun i hi=>(hZ i hi).1) (fun i hi=>(hZ i hi).2.1) (fun i hi=> ht i hi _) hr hh₁ m
  have hv (x:(Body (↥I))): ‖f x‖≤ V ∧ ‖g x‖≤V ∧ ‖f x-g x‖≤ V*(d*(B^mini)^m):= by
       have hR':‖b x‖≤ℙ:= feesA ..; unfold f g; rw [norm_mul,norm_mul,← mul_sub,norm_mul]; exact ⟨mul_le_mul hR' (hF' x).1 (norm_nonneg _) hR,mul_le_mul hR' (hF' x).2.1 (norm_nonneg _) hR,(mul_le_mul hR' (hF' x).2.2 (norm_nonneg _) hR).trans_eq (mul_assoc ..|>.symm)⟩
  have h₀:0 ≤ V:=(norm_nonneg _).trans ((hv 0).1)
  have hm: Measurable b := (firesM M Q D H X p hX hK).comp (Pond.spill_m I) -- order
  have hV : w= ∫ i in CA,g i ∂ PV:= cabinet_read M Q D H X p L' I hX hK hp x hβ hT m -- order
  have hf₀ i:= (vow_b X H hX hK i p).comp (Pond.spill_m I)
  have hF: Integrable f PV:= (integrable_const V).mono' (show Measurable f from hm.mul (Finset.measurable_fun_prod _ fun i _=> (Real.measurable_exp.comp (hf₀ i)).sub measurable_const)).aestronglyMeasurable (ae_of_all _ (fun i=> (hv i).1))
  have hQ: Integrable g PV:= (integrable_const V).mono' (show Measurable g from hm.mul (Finset.measurable_fun_prod _ fun i _=>Finset.measurable_fun_sum _ fun j _=> measurable_const.mul ((hf₀ i).pow_const (j.val+1)))).aestronglyMeasurable (ae_of_all _ (fun i=>(hv i).2.1)) -- edit
  rw [hV, show f'= ∫ i,f i ∂ PV from quantum (o:=o) M Q D X p L' Y hh hq I ((H.laws.data.localP F (timeΛ X p) (show (timeΛ X p).x=t from hX) (show (timeΛ X p).width=o.K from hK) hp).sails.fullC.submatrix Subtype.val_injective)]
  let T:=cabinet I (postponement L t o)
  refine ⟨(norm_integral_le_integral_norm ..).trans ((setIntegral_mono (μ:=PV) (s:=T) hQ.norm.integrableOn (g:=fun _=> V) (integrable_const V) (fun x=> (hv x).2.1)).trans ?_),?_⟩
  · rw [setIntegral_const]; exact mul_le_of_le_one_left h₀ measureReal_le_one
  have hs:= alive I (postponement L t o); rw [← integral_add_compl hs hF]
  let a:= ∫ i in T,f i ∂PV; let b:= ∫ i in T,g i ∂PV; let w:= ∫ i in Tᶜ,f i ∂PV; let r:= (d:ℝ)*(B^mini)^m
  have he : a-b=∫ i in T, f i-g i ∂PV := Eq.symm (integral_sub hF.integrableOn hQ.integrableOn)
  have hy: |a-b| ≤ V*r:= by
    rw [he]
    let K:=V*r; have hp:0≤r:= by unfold r; positivity
    apply le_trans (MeasureTheory.norm_integral_le_integral_norm (μ:=(PV).restrict T) (fun x=>f x-g x)); apply le_trans (b:=∫ _ in T,K ∂PV)
    · exact MeasureTheory.integral_mono ((_root_.MeasureTheory.Integrable.norm (hF.sub hQ)).integrableOn) (integrable_const _) (fun x=> (hv x).2.2)
    rw [setIntegral_const]; exact mul_le_of_le_one_left (mul_nonneg h₀ hp) (measureReal_le_one)
  have hw: |w| ≤ V*k:= by
    apply (_root_.MeasureTheory.norm_integral_le_integral_norm (f:=f) ..).trans
    apply (MeasureTheory.setIntegral_mono (μ:=PV) (s:=Tᶜ) (hF.norm).integrableOn (g:=fun _=>V) (integrable_const V) (fun x=> (hv x).1) -- edit
      ).trans
    rw [setIntegral_const,mul_comm]; exact mul_le_mul_of_nonneg_right hk h₀
  change |a+w-b|≤V*_ ; rw [show a+w-b=w+(a-b) by ring]; exact (abs_add_le ..).trans ((add_le_add hw hy).trans_eq (by rw [← mul_add]))

end YM.LocalLTE.Fan.MeasuredCinema

noncomputable section
namespace YM.LocalLTE.Fan.MeasuredWing
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open FrameBox Pastel Merge Merge.Palette

open Merge.Palette Gas Ursell Bakers
open Greenbelt
set_option quotPrecheck false
attribute [local instance] Gauge.frobInner
variable {ι:Type}(M:ι → Lotus.Leaf R) (H:Cash W t μ L Q o a T R)(χ:Chi)
-- Every label.Energy in θ ledger same geometry.T.Z.T.Tag projection Ward.
local notation "Oz"=> Merge.Tickets (Merge.Palette.sign M S)
local notation "Y₀"=> radiusB t
variable (z:H.fragrances)(D:Captain.Oscars M z) {θ ι' J:ℕ}
-- parity.Y allele tall cone factor.Deferred.B.Gouge.
local notation "Ux"=> (fun k=> z.snd k)
local notation "U₀"=> Captain.reachability (H:=H) z
local notation "M₀"=> (fun i=> East.docket H z i)
local notation "q₀"=> (fun k=> Captain.quietR M (z.2 k) (D k))
variable {α C B' v₁ d v₀ e A β κ :ℝ}(q n k :ℕ)(r₀:ℕ→ℕ)(A':ι→Prop)(hx:Candor M z D q n r₀ A')


variable (C₁: Captain H j C d v₀ e B' v₁ y B η k χ)
    (hK: Daisy.HostQ H C₁.conduit B' B k)
local notation "ℙ"=> (fun i=> (Merge.Palette.team M (D i)).weight)
variable (reserve : ℝ) (fee : Veil c f → ℝ)
local notation "Bv" => reserve
local notation "Z" => fee
local notation "mΦ" => (fun i => (M i).ingredient)
variable (hC : ∀ i : Option (Fin z.fst), ∀ v∈Captain.quietR M (z.2 i) (D i), 0 ≤ fee v ∧ fee v ≤ 1)
include hx hC C₁
local notation "TZ" => Disk G c
local notation "Ξ" => (2+Real.exp 1)
theorem averaged (Q':ℝ) (hp0:0 ≤ Q') (u:Directions G c) (hV: flags (Pressure.temp t) (increment (1:Config G c) u)=∅)(hT:Stamp T)(m:ℕ)(hB:1≤reserve)
    (hp:let x: Disk G c:=(gStep R.beta,u); ∀ (i:Option (Fin z.fst))(F:Forest S.ratio)(X:Coat T F),X.x=t→X.width=o.K→X.χ=χ→(timeΛ X x).manifest→ (Fan.pool (Fan.fibers H (z.2 i)) X x).real (cabinet (Fan.fibers H (z.2 i)) (postponement L t o))ᶜ ≤ Q' ∧ ∀ j∈Captain.quietR M (z.2 i) (D i),∀ b:Air f G, |vows X R Q o.a x b j| ≤ fee j*reserve^(levy r₀ j)):
    let x:TZ:=(gStep R.beta,u);
    |wingTerm (χ:=χ) z M D (increment 1 u)- Field.speedΛ H z.2 * mica M mΦ H χ z D m x| ≤ |Field.speedΛ H z.2| * canvasX M H z D Z * budgetAt q z.1 m Bv Q':=by
    intro x
    let Y:= increment (1:Config G c) u; let V i:= z.2 i; let Z' (i):=quietR M (V i) (D i); let ℓ:=Field.speedΛ H z.2; let g i:= waltz H χ M (z.2 i) (D i) Y; let f' i:= Fan.pinV M mΦ H χ (V i) (D i) m x -- infer order
    have hc(i) :=Fan.shutter M H χ z D q n k r₀ A' hx C₁ i x Y rfl hV
    have hS(i):=Fan.weaving M H z D q n r₀ A' hx i
    let E':=Veil c f; let ξ: E'→ℝ:= Z; let K:=Bv; let θ:ℝ:= (Ξ)^q; let U(i):ℝ:=ℙ i*∏ j∈ Z' i,ξ j; let η:=Q'+q*(K^Pastel.mini)^m
    have hU(i):0 ≤ U i:=mul_nonneg (team M (D i)|>.profit) (prod_nonneg (fun j hj=> (hC _ _ hj).1)); have hθ:(0:ℝ) ≤ θ:=by unfold θ; positivity
    have hη:0 ≤ η:=by unfold η; positivity
    letI : Nonempty (Forest S.ratio):=Tree.select S.ratio S.patch.odd_side
    have h(i): |f' i| ≤ U i*θ ∧ |g i-f' i| ≤ U i*θ*η:=by
       let X'(r:Reserve S)(z:S.Choices):= (prism T t χ o.K (1:Config G c) (allot r)).taggedL z
       let Y'(r:Reserve S)(u:S.Choices):= Fan.wishes (L:=L) (o:=o) M mΦ Q (D i) (X' r u) (Z' i) (fibers H (V i)) t m x
       let Q₁(r:Reserve S)(u:S.Choices):= (team M (D i)).qlocal4a_cinema (timeΛ (X' r u) x) (V i).val W o.a Q.table Q.halo (Fan.fibers H (V i))
       let b:= (Z' i).card; have hb:b≤ q:= (card_le_card (hS i|>.1)).trans (hx.can.each i|>.received)
       have ht : ℙ i*((Ξ)^b*(∏ j∈Z' i,ξ j)) ≤ U i*θ:= by rw [mul_left_comm,← show U i=_ from rfl,mul_comm];apply mul_le_mul_of_nonneg_left _ (hU i); exact pow_le_pow_right₀ (by linarith [Real.exp_pos 1]) hb
       have h'(r:Reserve S)(u':S.Choices): ‖Y' r u'‖ ≤ U i*θ∧ |Q₁ r u'-Y' r u'| ≤ U i*θ*η:=by
          let P:=X' r u'; have hg:= hp i _ P rfl rfl rfl (show (timeΛ P x).manifest from hV.symm)
          obtain ⟨h1,h2⟩:= MeasuredCinema.component M Q (D i) H P x (Z' i) (V i).val (hx.lives i) (hS i|>.2.2) (Fan.fibers H (V i)) rfl rfl (show (timeΛ P x).manifest from hV.symm) hB r₀ ξ (fun j hj=> ⟨(hC _ _ hj|>.1),(hC _ _ hj|>.2),fun b=> (hg.2 _ hj b)⟩) hT u rfl m Q' hg.1 -- order
          refine ⟨h1.trans ht,h2.trans (mul_le_mul ht (show Q'+b*(K^mini)^m ≤ η from ?_) (by positivity) (mul_nonneg (hU _) hθ))⟩
          unfold η; gcongr
       have hp:f' i=likely (fun r:Reserve S=> likely (Y' r)):=rfl
       rw [hp,show g i=likely (fun r:Reserve S=> likely (Q₁ r)) from hc i]
       refine ⟨Field.avgBound _ (fun i=>Field.avgBound _ (fun j=> (h' i j).1)),Field.difference _ _ (fun i=> Field.difference _ _ (fun j=> (h' i j).2))⟩ -- order
    let p i:=U i*(θ*(1+η))
    have he i:0≤p i:=mul_nonneg (hU i) (mul_nonneg hθ (add_nonneg zero_le_one hη))
    have hf₀ : (∏ i,p i)= canvasX M H z D ξ*(θ*(1+η))^(z.fst+1):= by unfold p; rw [prod_mul_distrib,prod_const]; simp_rw [card_univ,Fintype.card_option,Fintype.card_fin]; rfl
    have he0 i: U i*θ ≤ p i:= by unfold p; rw [←mul_assoc]; exact le_mul_of_one_le_right (mul_nonneg (hU i) hθ) (le_add_of_nonneg_right hη)
    rw [show wingTerm (χ:=χ) z M D (increment 1 u)= ℓ*(∏ i,g i) from (by unfold g ℓ Captain.wingTerm Field.speedΛ;dsimp only; ring)];change |ℓ*(∏ i,g i)-ℓ*(∏ i,f' i)|≤ _; rw [← mul_sub,abs_mul,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg ℓ)
    refine le_trans (Bakers.price hη Finset.univ g f' p (fun i _=> he i) (fun i _=> ?_) (fun i _=>(h i).1.trans (he0 i)) (fun i _=>?_)) (?_)
    · have hΓ:=(abs_add_le (g i-f' i) (f' i)); rw [sub_add_cancel] at hΓ; refine hΓ.trans ((add_le_add (h i).2 (h i).1).trans_eq ?_); unfold p; ring
    · have ht':=(h i).2; rw [mul_comm η]; exact ht'.trans (mul_le_mul_of_nonneg_right (he0 i) hη)
    rw [hf₀,card_univ,Fintype.card_option,Fintype.card_fin]; change _≤ canvasX M H z D ξ*((↑(z.fst+1):ℝ)*η*(θ*(1+η))^(z.fst+1)); exact le_of_eq (by ring)

/- The averaged finite field is exactly the measured continuation on the actual physical coupling, for every independent live mark. -/
omit C₁ hC in
include hx in
theorem pegged (Φ : ℕ → ℝ → Config G f → ℝ) (Ψ : ι → ℝ → Config G f → ℝ)
    (hΦ : ∀ i, r₀ i≤n → R.activities.E i=Φ i (gStep R.beta))
    (hΨ : ∀ i, A' i → Ψ i (gStep R.beta)=(M i).ingredient) (m : ℕ) (x : Disk G c) :
    Fan.micaPT M H χ z D Φ Ψ m (gStep R.beta) x = Fan.mica M mΦ H χ z D m x := by
  exact prod_congr rfl fun i _ => Fan.pint M mΦ H χ z D q n r₀ A' hx Φ Ψ hΦ hΨ m i x

end YM.LocalLTE.Fan.MeasuredWing

noncomputable section
namespace YM.LocalLTE.Fan.CleanPeg
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open FrameBox Pastel Merge Merge.Palette

open Merge.Palette Gas Ursell Bakers
open Greenbelt
set_option quotPrecheck false
attribute [local instance] Gauge.frobInner
variable {ι:Type}(M:ι → Lotus.Leaf R) (φ:ι→ Config G f→ℝ) (H:Cash W t μ L Q o a T R)(χ:Chi)
local notation "Oz"=> Merge.Tickets (Merge.Palette.sign M S)
local notation "Y₀"=> radiusB t
variable (z:H.fragrances)(D:Captain.Oscars M z) {θ ι' J:ℕ}
local notation "Ux"=> (fun k=> z.snd k)
local notation "U₀"=> Captain.reachability (H:=H) z
local notation "M₀"=> (fun i=> East.docket H z i)
local notation "q₀"=> (fun k=> Captain.quietR M (z.2 k) (D k))
variable {α C B' v₁ d v₀ e A β κ :ℝ}(q n k :ℕ)(r₀:ℕ→ℕ)(A':ι→Prop)(hx:Candor M z D q n r₀ A')
variable (Φ:ℕ→ℝ→ Config G f→ℝ)(Ψ:ι→ℝ→ Config G f→ℝ)
open Weft
variable (hT : Stamp T) (u : Directions G c)
    (hV : flags (Pressure.temp t) (increment (1:Config G c) u)=∅)
    (hΦ : ∀ l i, Sum.inl i∈Captain.quietR M (z.2 l) (D l) → ∀ U:Config G f,
      flags R.p.threshold U=∅ → R.activities.E i U=Φ i (gStep R.beta) U)
    (hΨ : ∀ l i, i∈(D l).val → ∀ U:Config G f,
      flags R.p.threshold U=∅ → Ψ i (gStep R.beta) U=φ i U)

include hT hV hΦ hΨ in
theorem row (m : ℕ) (i : Option (Fin z.fst)) :
    let x : Disk G c := (gStep R.beta,u)
    Fan.pinPT M H χ Φ Ψ (z.2 i) (D i) m (gStep R.beta) x = Fan.pinV M φ H χ (z.2 i) (D i) m x := by
  intro x
  let X (r : Reserve S) (k : S.Choices) := (prism T t χ o.K (1:Config G c) (Greenbelt.allot r)).taggedL k
  let v := z.2 i
  let J := Fan.fibers H v
  let V := Captain.quietR M v (D i)
  have he (r : Reserve S) (k : S.Choices) : Fan.wishPT (L:=L) (o:=o) (t:=t) M Q (D i) (X r k) V J m Φ Ψ
      (gStep R.beta) x = Fan.wishes (L:=L) (o:=o) M φ Q (D i) (X r k) V J t m x := by
    let Y := X r k
    let R' := Fan.vest R Φ (gStep R.beta)
    have hβ : R'.beta=R.beta := by
      unfold R'; change ((gStep R.beta)^2)⁻¹=_; rw [gStep,inv_pow,inv_inv,Real.sq_sqrt H.laws.intake.positive.le]
    unfold Fan.wishPT Fan.wishes
    apply setIntegral_congr_fun (Fan.alive ..)
    intro y hy
    have ht : 0≤Fan.postponement L t o := by
      unfold Fan.postponement; have h:=Delay.monitor_pos G L t; have h':=o.rare; positivity
    have hfield := (Fan.incomeA Y H rfl rfl hT u x rfl (show (timeΛ Y x).manifest from hV.symm)
      (Pond.spill J y) (Fan.fur J hy ht)).2.2
    have hh (i' : Veil c f) (hi : i'∈V) : Fan.coming Q.table R' Y x (Pond.spill J y) i' =
        Fan.coming Q.table R Y x (Pond.spill J y) i' := by
      unfold Fan.coming; rw [hβ]; rcases i' with i'|i'
      · exact congrArg (fun a : ℝ => -a) (hΦ i i' hi _ hfield).symm
      rfl
    unfold Fan.calPT
    apply congrArg (pledgeΛ Y J y (Vine.pass x)* ·)
    apply congrArg₂ (·*·)
    · exact prod_congr rfl fun j hj => hΨ i j hj _ hfield
    · exact prod_congr rfl fun j hj => congrArg (Bakers.afloat m) (hh j hj)
  exact congrArg likely (funext fun r : Reserve S => congrArg likely (funext fun k : S.Choices => he r k))

include hT hV hΦ hΨ in
theorem field (m : ℕ) :
    let x : Disk G c := (gStep R.beta,u)
    Fan.micaPT M H χ z D Φ Ψ m (gStep R.beta) x = Fan.mica M φ H χ z D m x := by
  intro x
  exact prod_congr rfl fun i _ => row M φ H χ z D Φ Ψ hT u hV hΦ hΨ m i

end YM.LocalLTE.Fan.CleanPeg

noncomputable section
namespace YM.LocalLTE.Fan.MeasuredYoungRows
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open YM.ConnectedActivityE6.Blaze.Silica
open Brush Foramen Pastel Polar Clutch Strokes
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}

theorem actual (H : Cash W s μ L Q o t T R) {χ : Chi} {d v r C : ℝ}
    (Ξ : Utopia H j v d r C χ) (hd : 0 ≤ d) (hv : 0 ≤ v) (hgoal : Q.goal L s ≤ 1)
    (X : Coat T F) (hx : X.x=s) (hw : X.width=o.K) (hc : X.χ=χ) (hT : Stamp T)
    (u : Directions G c) (hm : (timeΛ X (gStep R.beta,u)).manifest) (i : Veil c f) (z : Air f G)
    (hz : ∀ e, |z e|≤postponement L s o) :
    let f := Fan.coming Q.table R X (gStep R.beta,u) z i
    |f|≤1 ∧ |f|≤ min (H.w (Fan.chapter i)) (Real.exp 1*Ξ.fare (Fan.elastic (S:=S) i)) := by
  intro f
  have hh := congrFun (Fan.longing X H hx hw hT u (gStep R.beta,u) rfl hm z hz) i
  have hs := MeasuredRows.same_fee H Ξ hd hv hgoal X hx hw hc (gStep R.beta,u) hm i z
  have hff : f=Fan.vows X R Q o.a (gStep R.beta,u) z i := hh
  rw [hff]
  exact ⟨hs.trans ((min_le_left ..).trans (((MeasuredRows.purchased H).1 _).2.trans hgoal)),hs⟩

theorem pegged (H : Cash W s μ L Q o t T R) {χ : Chi} {d v r C : ℝ}
    (Ξ : Utopia H j v d r C χ) (hd : 0≤d) (hv : 0≤v) (hgoal : Q.goal L s≤1)
    (X : Coat T F) (hx : X.x=s) (hw : X.width=o.K) (hc : X.χ=χ) (hT : Stamp T)
    (u : Directions G c) (hm : (timeΛ X (gStep R.beta,u)).manifest) (i : Veil c f) (z : Air f G)
    (hz : ∀ e, |z e|≤postponement L s o) (Φ : ℕ→ℝ→ Config G f→ℝ)
    (hΦ : ∀ n, i=Sum.inl n → ∀ U, flags R.p.threshold U=∅ → R.activities.E n U=Φ n (gStep R.beta) U) :
    let f := Fan.coming Q.table (Fan.vest R Φ (gStep R.beta)) X (gStep R.beta,u) z i
    |f|≤1 ∧ |f|≤ min (H.w (Fan.chapter i)) (Real.exp 1*Ξ.fare (Fan.elastic (S:=S) i)) := by
  intro f
  let R' := Fan.vest R Φ (gStep R.beta)
  have hb : R'.beta=R.beta := by
    unfold R'; change ((gStep R.beta)^2)⁻¹=_; rw [gStep,inv_pow,inv_inv,Real.sq_sqrt H.laws.intake.positive.le]
  have hf := (Fan.incomeA X H hx hw hT u (gStep R.beta,u) rfl hm z hz).2.2
  have he : f=Fan.coming Q.table R X (gStep R.beta,u) z i := by
    change Fan.coming Q.table R' X (gStep R.beta,u) z i=_
    unfold Fan.coming; rw [hb]; rcases i with i|i
    · exact congrArg (fun a : ℝ=> -a) (hΦ i rfl _ hf).symm
    rfl
  rw [he]
  exact actual H Ξ hd hv hgoal X hx hw hc hT u hm i z hz

end YM.LocalLTE.Fan.MeasuredYoungRows

noncomputable section
namespace YM.LocalLTE.Fan.MeasuredWingTariff
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open YM.ConnectedActivityE6.Blaze.Silica
open Brush Foramen Pastel Polar Clutch Strokes
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}

def height (p q : ℕ) := 32*(p+q+1)

def small (β : ℝ) (p q : ℕ) := β^(-((p+q+1:ℕ):ℝ))

def constant (q : ℕ) := ((q+1:ℕ):ℝ)*(1+(q:ℝ))*((2+Real.exp 1)^q*(2+(q:ℝ)))^(q+1)

theorem order (β : ℝ) (hβ : 1≤β) (p q : ℕ) :
    ((MeasuredRows.cut β)^Pastel.mini)^(height p q) ≤ small β p q := by
  have hb := zero_le_one.trans hβ
  unfold MeasuredRows.cut small height Pastel.mini
  rw [← Real.rpow_mul hb,← Real.rpow_natCast,← Real.rpow_mul hb]
  apply Real.rpow_le_rpow_of_exponent_le hβ
  push_cast
  nlinarith [Nat.cast_nonneg (α:=ℝ) p,Nat.cast_nonneg (α:=ℝ) q]

theorem budget {q n m : ℕ} (hn : n≤q) {B a S δ : ℝ} (ha : 0≤a) (ha₁ : a≤1)
    (hS : 1≤S) (haS : a≤S*δ) (hδ : 0≤δ) (hB : 0≤(B^Pastel.mini)^m)
    (hB₁ : (B^Pastel.mini)^m ≤ 1) (hBδ : (B^Pastel.mini)^m ≤ δ) :
    Fan.budgetAt q n m B a ≤ constant q * S * δ := by
  let t := (B^Pastel.mini)^m
  let v := a+(q:ℝ)*t
  have hq : (0:ℝ)≤q := Nat.cast_nonneg _
  have hv : 0≤v := add_nonneg ha (mul_nonneg hq hB)
  have hmax : (q:ℝ)*t≤q := (mul_le_mul_of_nonneg_left hB₁ hq).trans_eq (mul_one _)
  have hu : v≤1+q := add_le_add ha₁ hmax
  have hp : t≤S*δ := hBδ.trans (le_mul_of_one_le_left hδ hS)
  have hs : v≤(1+(q:ℝ))*S*δ := by
    calc v ≤ S*δ+(q:ℝ)*(S*δ) := add_le_add haS (mul_le_mul_of_nonneg_left hp hq)
         _ = _ := by ring
  let base := (2+Real.exp 1)^q*(2+(q:ℝ))
  have hb : 1≤base := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [Real.exp_pos 1])) (by linarith)
  have he : (2+Real.exp 1)^q*(1+v)≤base := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have ht: ((2+Real.exp 1)^q*(1+v))^(n+1)≤base^(q+1) := (pow_le_pow_left₀ (by positivity) he _).trans
    (pow_le_pow_right₀ hb (Nat.succ_le_succ hn))
  change ((n+1:ℕ):ℝ)*v*((2+Real.exp 1)^q*(1+v))^(n+1)≤_
  calc _ ≤ (((q+1:ℕ):ℝ)*((1+(q:ℝ))*S*δ))*base^(q+1) := by gcongr
       _ = _ := by unfold constant base; ring

def purse (H : Cash W s μ L Q o t T R) {χ : Chi} {d v r C : ℝ} (Ξ : Utopia H j v d r C χ)
    (β : ℝ) (i : Veil c f) := min (H.w (Fan.chapter i)) (Real.exp 1 * Ξ.fare (Fan.elastic (S:=S) i)) /
      (MeasuredRows.cut β)^(Fan.levy (fun _=>0) i)

theorem quote (H : Cash W s μ L Q o t T R) {χ : Chi} {d v r C : ℝ} (Ξ : Utopia H j v d r C χ)
    {β : ℝ} (hβ : 1≤β) (hQ : Q.goal L s ≤ β^(-(15/32:ℝ))) (i : Veil c f) :
    0≤purse H Ξ β i ∧ purse H Ξ β i≤1 ∧ purse H Ξ β i≤(Real.exp 1*β)*Ξ.fare (Fan.elastic (S:=S) i) := by
  let y : LogIndex c f→ℝ := fun i=> min (H.w i) (Real.exp 1*Ξ.goalsL i)
  have hw := (MeasuredRows.purchased H).1
  have hgoals (i : LogIndex c f) : 0 ≤ Ξ.goalsL i := Ξ.uses.nonneg (.inr (.inl i))
  have hy (i : LogIndex c f) : 0≤y i ∧ y i≤β^(-(15/32:ℝ)) :=
    ⟨le_min (hw i).1 (mul_nonneg (Real.exp_pos _).le (hgoals i)),(min_le_left ..).trans ((hw i).2.trans hQ)⟩
  obtain ⟨hd,h0,h1,_⟩ := MeasuredRows.envelope β hβ y hy i
  refine ⟨h0,h1,?_⟩
  let D := (MeasuredRows.cut β)^(Fan.levy (fun _=>0) i)
  have hb : 0<β := zero_lt_one.trans_le hβ
  have hg : β⁻¹≤D := by
    unfold D MeasuredRows.cut
    rw [←Real.rpow_neg_one,←Real.rpow_mul hb.le]
    apply Real.rpow_le_rpow_of_exponent_le hβ
    rcases i with i|i <;> norm_num [Fan.levy,Pastel.chip,Pastel.slack,Pastel.mini]
  have h₁ : 1≤β*D := calc 1 = β*β⁻¹ := (mul_inv_cancel₀ hb.ne').symm
                       _ ≤ β*D := mul_le_mul_of_nonneg_left hg hb.le
  change y (Fan.chapter i)/D≤_
  apply (div_le_iff₀ hd).mpr
  calc _ ≤ Real.exp 1*Ξ.fare (Fan.elastic (S:=S) i) := min_le_right ..
       _ ≤ (Real.exp 1*Ξ.fare (Fan.elastic (S:=S) i))*(β*D) :=
         le_mul_of_one_le_right (mul_nonneg (Real.exp_pos _).le (Ξ.fares _)) h₁
       _ = _ := by ring

end YM.LocalLTE.Fan.MeasuredWingTariff
