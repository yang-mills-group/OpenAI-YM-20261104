import YM.OPE.Compatible.Minuet.Breeze
/-!
# F patch integration fixing exterior. Report conditional function of stencil.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open AnalyticBridge.VerifiedReset
open Next.Rank.Thirst
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P₀:Teller G} {T: Tube G S} {R : Rep G f}
    {p : BudgetPoint} {m n: ℕ} {W a r t σ E Λ μ x κ C w ε D b B: ℝ} {Ñ:ChartRatio G}
variable {F:Forest S.ratio} (I:Seats F) (G)
abbrev Rim := {i:F.Free//i∉I}→ G.El
def threadT: (F.Slice G) ≃ᵐ World F I G × Rim G I := MeasurableEquiv.piEquivPiSubtypeProd _ _
def hail := Measure.pi (fun _ : ↥I => G.probHaar)
def rimH:= Measure.pi fun _: {i:F.Free // i∉I}=> G.probHaar
instance precipY : IsProbabilityMeasure (hail G I):= by unfold hail; infer_instance
instance precipT : IsProbabilityMeasure (rimH G I):=by unfold rimH; infer_instance
lemma tapestry : MeasurePreserving (threadT G I) (F.order G) ((hail G I).prod (rimH G I)):=by
   unfold threadT Forest.order hail rimH
   convert! measurePreserving_piEquivPiSubtypeProd (fun _:F.Free=> G.probHaar) (fun i=>i∈I)
variable {G} {J:Seats F}{X Y Z:Support f}{q:Support c}
abbrev Wind (p:World F I G) (x:Rim G I):= (threadT G I).symm (p,x)
lemma interior_e (p:World F I G)(x:Rim G I):curveF F I (Wind I p x)=p:=congr_arg Prod.fst ((threadT G I).apply_symm_apply _)
lemma exterior_e (p:World F I G)(x:Rim G I)(i:{i:F.Free// i∉I}):Wind I p x i.val=x i:=congr_fun (congr_arg Prod.snd ((threadT G I).apply_symm_apply (p,x))) i
lemma resetting (p:World F I G)(x:Rim G I):shave I (Wind I p x)=Wind I 1 x:=by
   ext1 i; unfold shave; split
   next h=> exact (congr_fun (interior_e I (1:World F I G) x) ⟨i,h⟩).symm
   next h=> exact (exterior_e I _ x ⟨i,h⟩).trans (exterior_e I _ x ⟨i,h⟩).symm
-- extension J shelf to full exterior and cuts
def ald (J:Seats F)(x:World F J G) : Rim G I:=fun i=> if h:i.val∈J then x ⟨_,h⟩ else 1
def intoN (J:Seats F)(x:Rim G I):World F J G:=fun i=> if h:i.val∈I then 1 else x ⟨_,h⟩
lemma couponSt (J:Seats F)(p:World F I G)(x:Rim G I): let y := curveF F J (Wind I p x)
   ald I J (intoN I J x)=ald I J y ∧
    y=curveF F J (Wind I p (ald I J y)):=by
   intro y; have hs (i:{i:F.Free//i∉I})(hi:i.val∈J): ald I J y i=x i:=by unfold ald; rw [dif_pos hi]; exact exterior_e I _ x i
   constructor
   · ext1 i; by_cases h:i.val∈J
     · rw [hs i h]; unfold ald intoN; rw [dif_pos h]; dsimp only; rw [dif_neg i.property]
     unfold ald; rw [dif_neg h,dif_neg h]
   ext1 i; by_cases h:i.val∈I
   · exact (congr_fun (interior_e I p x) ⟨_,h⟩).trans (congr_fun (interior_e I p _) ⟨_,h⟩).symm
   let q:{i:F.Free// i∉I}:=⟨i.val,h⟩; exact (exterior_e I _ x q).trans ((hs q i.property).symm.trans (exterior_e I _ _ q).symm)
abbrev Shelter (B:ℝ)(p:World F I G): Prop:=∀ i,G.chord (p i)≤B
lemma hut (B:ℝ) : MeasurableSet {p:World F I G| Shelter I B p}:=by
   simp only [Shelter, Set.setOf_forall]; apply MeasurableSet.iInter; intro i; exact measurableSet_le (G.continuous_chord.measurable.comp (measurable_pi_apply i)) measurable_const
-- Actual sharp cut guard INSIDE.J open after equality may use enclosed measurable
-- g extension function on World F J (not necessarily centroid) for any amplitude
def ballotY {J:Seats F}(R:Rep G f)(V:Config G c)(m:ℕ)(k:S.Choices)(B:ℝ)(y:World F J G)(p:World F I G):ℝ:= if Shelter I B p then Ruin R V m I k (F.drape (Wind I p (ald I J y))) else 0
def report (J:Seats F)(R:Rep G f)(V:Config G c)(m:ℕ)(k:S.Choices)(B:ℝ)(f':World F I G→ℝ)(x:World F J G):=
   let g:= ballotY I R V m k B x; (∫ p,g p*f' p ∂hail G I) / (∫ p,g p ∂hail G I)
private lemma settle {α:Type}[MeasurableSpace α](u v:α→ℝ) (μ:Measure α)[IsFiniteMeasure μ](hm:Envelope u)(hf:Envelope v)(hp:∀ a,0 ≤ u a)(x:ℝ)(hx:0≤x)(hw:∀ a,‖v a‖≤x) :
    let c:=∫ p,u p ∂μ; let V:=∫ p,u p * v p ∂μ
    ‖V/c‖ ≤ x ∧ (∫ p,u p*(v p-(V/c)) ∂μ)=0 := by
   intro c V; have hh: ‖V‖≤ c*x:=by
      rw [show c*x=∫ p,u p*x ∂μ from (integral_mul_const ..).symm]; apply (norm_integral_le_integral_norm _).trans (integral_mono ((hm.mul hf).integrable _|>.norm) ((hm.mul (Envelope.const _)).integrable _) (fun i=>?_)); dsimp only; rw [norm_mul, Real.norm_of_nonneg (hp _)]; exact mul_le_mul_of_nonneg_left (hw _) (hp _)
   simp_rw [mul_sub]; rw [integral_sub ((hm.mul hf).integrable _) ((hm.mul (Envelope.const _)).integrable _),integral_mul_const]; change ‖V/c‖ ≤ x ∧ V-c*(V/c)=0
   by_cases h:c=0; · have hp:V=0:=norm_le_zero_iff.mp (by rwa [h,zero_mul] at hh); simp only [h,hp,zero_div,norm_zero,hx,zero_mul,sub_zero,and_self]
   have he: 0<c:= (integral_nonneg hp).lt_of_ne (Ne.symm h)
   constructor
   · rw [norm_div,Real.norm_of_nonneg he.le]; exact (div_le_iff₀ he).mpr (hh.trans_eq (mul_comm ..))
   field_simp; ring
section
variable (P: S.patch.Branches S.kernel G)(H:R.Lawful σ C Λ E w)(V:Config G c)(m:ℕ)(k:S.Choices)(B:ℝ)
include P H
lemma coin_vote : Envelope (fun i:World F J G ×World F I G=> ballotY I (J:=J) R V m k B i.1 i.2):=by
    apply Envelope.piece _ _ (Envelope.const _)
    · exact measurable_snd (hut I B)
    apply Env.along (wickRoad H k V P m I)
    apply F.continuous_drape.measurable.comp ((threadT G I).symm.measurable.comp (measurable_snd.prodMk ?_)); apply measurable_pi_lambda; intro i; unfold ald; split_ifs; exact (measurable_pi_apply _).comp measurable_fst; exact measurable_const
variable (f':World F I G→ℝ)(hf:Envelope f'){h:ℝ}(hw:∀ w,‖f' w‖≤h)
include hf
lemma reports_x (J:Seats F): Measurable (report I J R V m k B f'):=by
   have he:= coin_vote (J:=J) I P H V m k B; exact ((he.meas.mul (hf.meas.comp measurable_snd)).stronglyMeasurable.integral_prod_right' (ν:=hail G I)).measurable.div ((he.meas.stronglyMeasurable.integral_prod_right' (ν:=hail G I)).measurable)
include hw
set_option maxHeartbeats 200000 in
lemma atReport (x:World F J G) :
   let b:=ballotY I (J:=J) R V m k B x; let r:=report I J R V m k B f' x
   ‖r‖≤h ∧ (∫ p,b p*(f' p-r) ∂hail G I)=0:=by
   intro b r; have he:= coin_vote (J:=J) I P H V m k B; have hs:0≤h:=(norm_nonneg _).trans (hw 1)
   have hm : Envelope b:= Env.along he (g:=fun p:World F I G=>(x,p)) (measurable_const.prodMk measurable_id)
   have hp p:0 ≤ b p:=by unfold b ballotY;split; exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le; exact le_rfl
   exact settle b f' (hail G I) hm hf hp h hs hw
end
end YM.PhysicalNext.Repeat.Aroma
