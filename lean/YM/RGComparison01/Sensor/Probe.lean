import YM.RGComparison01.Sensor.Flag
import YM.RGComparison01.Sensor.Stamper
import YM.RGComparison01.Marks.Diner
/-!
# Seats prepared to take normalized truncated readings

 Cost on the full incoming group via mask guarantee, not using it at
 equality in derivatives. Does NOT recover unmasked physical test from
 the flagged-gas difference. Handles ANY many probes on same background.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Sensor
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Push.Uniform Fare Sienna Lapis Lotus Pledge Pledge.Diner
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{c f C F:Side} {P':Patch}
variable (R:RG.Rep G f) (r:ℕ)
set_option quotPrecheck false
local notation "b"=> gStep R.beta
local notation "T"=> stand R
local notation "Z"=> R.p.threshold
abbrev eyeTest (V:ℝ)(p:Cell f)(U:Config G f):ℝ := (V⁻¹)^ (2:ℕ)*G.price (faceValue U p)
lemma localH (V:ℝ)(p:Cell f): LocalOn (touched p:Support f) (eyeTest («G»:=G) V p):= by
    intro U W h
    have hp: faceValue U p=faceValue W p:= by apply travel_local _ _; apply agrees_mono h; exact fun i h=> (List.mem_toFinset.mpr h)
    unfold eyeTest; rw [hp]
-- tag and costs separate when lifting
abbrev curt (P:Support f) (p:Cell f) (R:RG.Rep G f): Config G f→ℝ:= masked R.p.threshold P (eyeTest (gStep R.beta) p)
abbrev lensWeight (t z:ℝ) := z^2*t⁻¹^ (2:ℕ)  -- threshold z, amplitude t
lemma violet (Q:Support f)(p:Cell f)(hQ:p.1∈Q)(V:Config G f): ‖curt Q p R V‖ ≤ lensWeight (gStep R.beta) R.p.threshold:=by
   unfold curt; by_cases h:Healthy Z Q V; swap; · rw [masked_ne _ _ _ _ h,norm_zero]; unfold lensWeight; positivity
   rw [masked_eq _ _ _ _ h]; have hx:G.chord (faceValue V p) ≤ R.p.threshold:= by_contra fun ht=> Finset.disjoint_left.mp h hQ ((flags_spec _ _ _).2 ⟨_,Work.E01.base_touched p,lt_of_not_ge ht⟩)
   unfold eyeTest; rw [mul_comm, Real.norm_of_nonneg (mul_nonneg (G.price_range _).1 (sq_nonneg _))]
   refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _); have he:= pow_le_pow_left₀ (G.chord_nonneg _) hx 2
   linarith only [he,G.chord_price (faceValue V p),G.price_range (faceValue V p)|>.1]
lemma terrific (Q:Support f) (p:Cell f) (he:touched p⊆ Q) : UsesFinal R.p.threshold Q (curt Q p R)∧ GaugeInvariant (curt Q p R)∧ Measurable (curt Q p R):= by
   unfold curt
   refine ⟨fun U W h hx=>?_,fun g U=>?_, masked_measurable _ _ _ ((show Continuous (eyeTest (gStep R.beta) p) from continuous_const.mul ((G.continuous_price).comp (continuous_travel ..))).measurable)⟩
   · have hp:Healthy Z Q U↔ Healthy Z Q W:= by unfold Healthy; simp only [Finset.disjoint_iff_inter_eq_empty,hx]
     by_cases hh: Healthy Z Q U
     · rw [masked_eq _ _ _ _ hh, masked_eq _ _ _ _ (hp.mp hh)]; exact localH _ p U W (agrees_mono h he) -- binder no G
     rw [masked_ne _ _ _ _ hh, masked_ne _ _ _ _ (mt hp.mpr hh)]
   have hx: Healthy Z Q U ↔ Healthy Z Q (gauge g U):= by unfold Healthy; rw [gauge_flags]
   by_cases h:Healthy Z Q U
   · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ (hx.mp h),eyeTest,eyeTest, face_gauge,G.price_conj]
   rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ (mt hx.mpr h)]

-- full alignment.Address `a` multiplicity explicit. No forced here.
variable (p:Cell f)(hr:2≤r)
local notation "P"=> neighbors r p.1
local notation "K"=> (P)
abbrev mark (a:ℕ) :Lotus.Leaf (stand R):=by
    have ht:= man R r (p.1,a); let z:= (tag R r (p.1,a)).val; let w:= Wing.logKey z
    have hx:w.support (T)=P:= ht.2.1
    have hh:= terrific R P p (fun i hi=>(neighbors_mem ..).2 ((Work.E01.sep_touched p i hi).trans hr))
    refine ⟨w,curt K p R,hx.symm ▸ hh.1,fun V he=> ?_,ht.2.2,lensWeight (gStep R.beta) (R.p.threshold),fun V=> violet R _ p (show p.1∈P from (neighbors_mem ..).2 (by rw [separation_self]; exact Nat.zero_le _)) V,hh.2.1,hh.2.2⟩
    have hY : Healthy Z P V:= by_contra fun h=> he (masked_ne _ _ _ _ h)
    change Healthy Z (w.support (T)) V; rw [hx]; exact hY
lemma siteAt (a:ℕ): Leaf.crest (mark R r p hr a)= P:= man R r (p.1,a) |>.2.1
omit p in
lemma chef {ι:Type}(p:ι→Cell f) (l:ι→ℕ) : ∃ H:Diner.Driver (fun i=> mark R r (p i) hr (l i)), H.origin= fun i=> (p i).1:=by
   let X(i:ι):= mark R r (p i) hr (l i)
   exact ⟨⟨fun i=> (p i).1, fun i=> (by change (p i).1 ∈ (X i).crest; unfold X; rw [siteAt]; exact (neighbors_mem ..).2 (by rw [separation_self]; exact Nat.zero_le _))⟩, rfl⟩
-- Blueprint.Q lifting against Ribbon/full mask
variable {ι:Type}
variable (h:f.val=c.val*P'.L.val) (H:F.val=C.val*P'.L.val){j:ℕ} (hC:C.val=c.val*j)(R':RG.Rep G F)(l:ι→ℕ)(p:ι→Cell f)(p':ι→Cell F)
local notation "y"=> (Deck.fineP h H hC)
local notation "A0"=> (Macrame.splitter (Deck.divides y))
local notation "T'"=> (stand R')
variable (he:2≤ c.val)
lemma liftT (hp:4<f.val)(hA :∀ i:ι, (A0 (p' i).1,(p' i).2)=p i)(hx: R'.p=R.p)(hv:R'.beta=R.beta) (x:Site C)(k:ℕ)(hh :∀ i, separation x ((decreed H).parent (p' i).1) ≤ k) :
    Relay.Lens (h:=h) (H:=H) (hC:=hC) (he:=he) (fun i=>mark R r (p i) hr (l i)) (fun i=>mark R' r (p' i) hr (l i)) (stance R r) (stance R' r) (castP R r R' y) (fun i:ι=> tag R' r ((p' i).1,l i)) x k:=by
   let L:=Lace.project («h»:=h) (H:=H) hC he
   refine ⟨crosses R r R' (y),fun i=>rfl,fun i=>?_,fun i=> ?_,fun i V=>?_⟩
   · rw [billed,show A0 (p' i).1=(p i).1 from congrArg Prod.fst (hA i)]
   · rw [(man R' r _).1]; exact hh i
   let Z0:= neighbors r (p i).1; let Z1:= neighbors r (p' i).1; let U:= L.high.links V
   have ht: Z1.image (A0)= Z0:= by rw [neigh_f r y,show A0 (p' i).1=(p i).1 from congrArg Prod.fst (hA i)]
   have hh: Healthy R'.p.threshold Z1 U ↔ Healthy Z Z0 V := by rw [←ht,hx]; exact Deck.vigor y V hp Z Z1
   by_cases hz : Healthy Z Z0 V; swap
   · exact (masked_ne _ _ _ V hz).trans (masked_ne _ _ _ U (mt hh.mp hz)).symm
   change masked Z Z0 _ V=masked R'.p.threshold Z1 _ U
   rw [masked_eq _ _ _ _ hz, masked_eq _ _ _ _ (hh.mpr hz)]
   have he':faceValue V (p i)=faceValue U (p' i):=by
      rw [←hA i]; exact (L.high.traveller ..).symm
   unfold eyeTest; rw [hv,he']
end YM.RGComparison01.Sensor
