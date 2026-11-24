import YM.Qlocal.Moonset.Clearing
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Actual.Season
open Function Filter Set Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open Marker MeasureTheory Extra.Trajectories Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms
open Progress.DirectedRecipe ConnectedActivityE6 Coat PhysicalNext PhysicalNext.Repeat AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Metric Height Roof Input Org Supply Pane Slide
open PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost PhysicalNext.Repeat.Legato
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff BigOperators YM.Qlocal.Payload
open AllOrder Transit Transit.WheelP Floe.Step.PlanV
open Merge Switch Spectrum UniformPays Publishing Emissions Payload Provisional Footprint StageArt Program Program.Hull
open RGComparison01 RGComparison01.Pledge
open Leasing Integration Integration.LocalComparison Integration.RiderTastePresentation
variable {Ω ι V : Type} [DecidableEq V][Fintype V][Nonempty V] (B:Marker.Census V) {G:Gauge}
    (X:Run G){Δ:ℕ→Prop} {m k p N j k' z n i l : ℕ} {δ r θ u v w E C ℓ: ℝ}
local notation "a"=> X.alloy.B.a
set_option quotPrecheck false
local notation "A"=> X.alloy
local notation "Y"=> X.alloy.B.a.clock.hatBeta
local notation "κ"=> Fintype.card (Gauges.Atlas.Notice B)
local notation "Z"=> fun i=>Real.log (Y i)
local notation "τ"=> Studio.loss X B
open Parabola Dialect Calendars
namespace Studio
/-! Size of the repeated estimate, in a setup tolerance ε, mapped to actual coupling. -/
variable (ζ:ℕ→ℝ)(T:ℕ→ℕ)
open Squall Squall.Skull Camp Hull Frigus
local notation "D"=> X.rolls
noncomputable def spend_at (δ:ℝ) (p:ℕ):ℝ:= -((p+1:ℕ):ℝ)/2+δ/4
noncomputable def speculum (δ:ℝ)(p i:ℕ):ℝ:= (X.alloy.B.a.clock.hatBeta i)^ (spend_at δ p)
local notation "u★[" i "]"=> speculum X δ p i
lemma strong (h:δ ≤ p+1): spend_at δ p < 0:= by unfold spend_at; push_cast; linarith only [h,Nat.cast_nonneg (α:=ℝ) p]
lemma dollars (h:δ ≤ p+1)(i:ℕ): 0< u★[i]∧ u★[i] ≤1:= by have he:= (A).B.a.fits.delayed i; exact ⟨Real.rpow_pos_of_pos (zero_lt_one.trans he) _, Real.rpow_le_one_of_one_le_of_nonpos he.le (strong h|>.le)⟩
structure Charged (u:ℝ)(z:ℕ) (T:ℕ→ℕ): Prop where
    positive : 0<u
    small : u≤1
    purses : ∀ m≥z,Banknote.stipend X.alloy m p ζ ≤ u
    hard   : ∀ m≥z, Frigus.hardcap X.alloy.B.a T m ≤ u
local notation "ζL"=>fun i=>ζ ((A).B.a.clock.J i)
local notation "H"=>fun i=>T ((A).B.a.clock.J i)
local notation "Φ"=> fun t=>Y (t+1)
local notation "C'"=> fun i=>Banknote.stipend X.alloy i p ζ
local notation "σ"=> fun i=> Frigus.hardcap X.alloy.B.a T i
lemma genius (h:δ ≤ p+1) (hv:0<δ)(ht:Tendsto T atTop atTop)(hT:Tendsto ζ atTop (𝓝 0)): ∀ᶠ z in atTop, Charged X ζ (u★[z]) z T (p:=p):= by
 let d:= spend_at δ p; have he:d<0:= strong h; let b i:= (A).B.a.clock.J (i+1); have hp : Tendsto b atTop atTop:= ((A).B.a.fits.deep).comp (tendsto_add_atTop_nat 1);
 have ht':∀ᶠ i:ℕ in atTop,-(T (b i):ℝ) ≤ d:=by filter_upwards [((tendsto_natCast_atTop_atTop.comp (ht.comp hp))|>.eventually_ge_atTop (-d))] with i hi; simpa using (neg_le_neg (show -(spend_at δ p) ≤ _ from hi)) -- likely simp turns wrong
 have hδ:∀ᶠ i:ℕ in atTop,2*ζ (b i) ≤ δ/4:=by filter_upwards [((hT.comp hp).eventually (gt_mem_nhds (by linarith only [hv] : 0<δ/8)))] with i hi; change ζ (b i)<δ/8 at hi; linarith only [hi]
 obtain ⟨i,hi⟩:= eventually_atTop.mp (ht'.and hδ);
 filter_upwards [eventually_ge_atTop i] with z hz
 have he'(m:ℕ)(h:z ≤ m): Φ m^d ≤ u★[z] := Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans ((A).B.a.fits.delayed _)) (Hull.grown X.metals X.rolls (A) (h.trans (Nat.le_succ _))) he.le
 refine ⟨(dollars X h z).1,(dollars X h z).2,fun m hm=> le_trans ?_ (he' m hm),fun m hm=> le_trans ?_ (he' m hm)⟩
 · unfold Banknote.stipend tone; rw [← PriceCompiler.beta_eq (A).B.valid]; apply Real.rpow_le_rpow_of_exponent_le ((a).fits.delayed _|>.le); unfold d spend_at platform Skull.score AllOrder.Catch.graded; have hh:= hi m (hz.trans hm) |>.2; unfold b at hh; linarith only [hh]
 unfold Frigus.hardcap; apply le_trans (mul_le_of_le_one_left _ (reserve_bounds (a) m).2); · exact Real.rpow_le_rpow_of_exponent_le ((a).fits.delayed _|>.le) (hi _ (hz.trans hm)|>.1)
 exact Real.rpow_nonneg (zero_le_one.trans ((a).fits.delayed _|>.le)) _
-- thermal + charges. Output recovery targets δ ≤ p+1 arbitrary fixed. uniform reference β at reporting mesh `z`. κ-rate can be stronger.
local notation "Kℓ"=> Studio.scale B X
noncomputable def target (z:ℝ)(p:ℕ)(β:ℝ):= (2:ℝ)^((p+1:ℝ)-z) * Coat.gStep β^((p+1:ℝ)-z)
variable (g:G.Simple)
include g
lemma profile (h:δ ≤ p+1)(hv:0<δ)(r:ℕ): ∀ᶠ i in atTop,∀ β∈band X.alloy.B.a i,∀ j≥i, Close X.alloy.B.a i j→ (Kℓ i j)^r*speculum X δ p i ≤ target δ p β:= by
 filter_upwards [gain B X g r (by linarith only [hv] : 0 < δ/4)] with i hi β hβ j hj he; let G':= (Studio.scale B X i j); let y:= (A).B.a.clock.hatBeta i; have hp:1 ≤ y:= (a).fits.delayed i|>.le; have hy:0< y:=zero_lt_one.trans_le hp; have hδ :=dollars X h i |>.1; apply (mul_le_mul_of_nonneg_right (hi j hj he) hδ.le).trans;
 unfold target speculum; rw [← Real.rpow_add hy]; let v:=(p+1:ℝ)-δ; rw [show δ/4+spend_at δ p= -(1/2)*v by unfold v spend_at; push_cast; ring, Real.rpow_mul hy.le]; obtain ⟨hw,ht,hC,hK⟩:= Hull.blue («A»:=A) hβ; have he: Coat.gStep y ≤ 2*Coat.gStep β:= Geo.strip hy ht hβ.2; rw [Real.rpow_neg hy.le, ← Real.sqrt_eq_rpow]; exact (Real.rpow_le_rpow (Fare.gS y hy|>.1.le) he (sub_nonneg.mpr h)).trans_eq (Real.mul_rpow zero_le_two hC.le)

lemma kernel (ht:Tendsto T atTop atTop)(r v:ℕ): ∀ᶠ i in atTop,∀ m≥i,∀ β∈band X.alloy.B.a (m+1),∀ j≥m+1, Close X.alloy.B.a m j→ (Kℓ (m+1) j)^r*Frigus.hardcap X.alloy.B.a T m ≤ Hull.hard X.alloy.B.a m * Coat.gStep β^v:= by
 have he:Tendsto (fun i=> T (X.alloy.B.a.clock.J (i+1))) atTop atTop:=ht.comp ((A).B.a.fits.deep.comp (tendsto_add_atTop_nat 1)); obtain ⟨m,hm⟩:= eventually_atTop.mp (((gain B X g r zero_lt_one).and ((Corrected.Grows.beta (a) g)|>.eventually_ge_atTop 2)).and (he.eventually_ge_atTop (v+1))); refine (eventually_ge_atTop m).mono (fun z hz i hi β hβ j hj hc=>?_); obtain ⟨h0,hT⟩:= hm _ (hz.trans hi); -- h0/hT pairs check
 let W:= T ((A).B.a.clock.J (i+1)); let y:= Y (i+1); let x:= Kℓ (i+1) j; have hy:2 ≤ y:= (hm _ ((hz.trans hi).trans (Nat.le_succ _))).1.2; have hv: v+1 ≤ W:= hT -- proj
 have hh: x^r ≤ y:= ( (hm (i+1) (by omega)).1.1 j hj (Hull.close_shrink hc (Nat.le_succ _))).trans (Real.rpow_one y|>.le)
 obtain ⟨he₀,he₁,hf,hQ⟩:= Hull.blue («A»:=A) hβ; have h0:0<y:=zero_lt_one.trans he₀; have hb:β ≤2*y:= hβ.2; have ht : y⁻¹ ≤ Coat.gStep β:= inv_anti₀ (Real.sqrt_pos.mpr he₁) (by apply Real.sqrt_le_iff.mpr; exact ⟨h0.le,by nlinarith only [hb,hy]⟩)
 change _*(Hull.hard _ i * y^ (-(W:ℝ)))≤ _; rw [mul_left_comm]; apply mul_le_mul_of_nonneg_left _ (reserve_bounds (a) i|>.1.le); apply (mul_le_mul hh (Real.rpow_le_rpow_of_exponent_le he₀.le (neg_le_neg (show ((v+1:ℕ):ℝ)≤↑W from (by exact_mod_cast hv)))) (Real.rpow_nonneg h0.le _) h0.le).trans _; apply le_trans _ (pow_le_pow_left₀ (inv_pos.mpr h0).le ht v); rw [Real.rpow_neg h0.le, Real.rpow_natCast,pow_succ',inv_pow]; exact le_of_eq (by field_simp)
end Studio
end YM.Qlocal.Actual.Season
