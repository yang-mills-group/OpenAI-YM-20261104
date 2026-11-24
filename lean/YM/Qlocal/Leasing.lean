import YM.Qlocal.Reclosure
-- existing hold on Sail base, for reuse later in witnesses of narrow cluster pricing.
import YM.RGComparison01.Marks.Admission

/-! Stagewise funding for **real** primitive solver, including keeping the
 Lane of K charges usable even for the innovation stage after mark exit.
 No analytic coupling continuation at actual parameters or assumed test gates.

 Earnings variable W0 in primitive is bought at exp(-mark) then exchanged
 at **1/8 of forecast** (actual β). Show the uniform +1+1 reserve; burn 1
 twice in exact repeated packing on the coarse representation. Pays *all*
 fields after that. Uses `Rent` (µ bought before entering history), adapted
 from its pricing proof.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Leasing
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
open RGComparison01 RGComparison01.Pledge
open Checks Baked Palette Pillow Resin Season Ink Switch Mallow Ovens OmitClusters Song Refrain Motion Extra.Iteration
open Push.PriceCompiler Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03 ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt Boulevard Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Divides Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Opera Slide
open Push.Uniform Sienna Fare Lapis
open Holdings
open Tensor WilsonStartup Presented Planned.JetPort Ovens
open RG.Shoot

section rent
lemma resize_seed (Pt : Teller G) (Q : ConnectedActivityE6.Target G Pt) (L : Side) (μ : ℝ) (hμ : 0<μ)
    (F : Postage) (A : Time.Forecast F) (hA : A.hard ≤ μ/32) (c : ℝ) (hc : 0<c) :
    ∀ᶠ x : ℝ in atTop, ∀ β : ℝ, Next.Scheduling.inBand (betaF G x L) β →
      Real.exp (-Q.mark L μ x) ≤ c*A.pair.strong (betaF G x L) β := by
  have hF := A.surplus
  have hr : 0<A.hard := F.pos.trans hF
  let κ:= μ/8; have hZ:0<κ:=by unfold κ; positivity
  let Z x:= Real.exp (-κ* Delay.fineMonitor G L x^2)
  have h : Rate G L (-1) Z:= by simpa only [Z,Real.rpow_two] using! (Rate.monitor_cutoff (G:=G) (L:=L) (a:=-1) hZ (show 0<(2:ℝ) by norm_num))
  filter_upwards [Delay.shift_pos G L,h.below (by norm_num) c hc] with x hx hv β hb
  let y:=betaF G x L
  have hy : Clock.gap y / 2 ≤ Clock.gap β := (band_gap y β hx hb).1
  have hg : 0 < Clock.gap y := Clock.gp hx
  have hβ : 0 < Clock.gap β := lt_of_lt_of_le (half_pos hg) hy
  let p := Instrument.plain.P y
  let t := Instrument.plain.t y / Clock.gap β
  have hp : 0 < p := Clock.wp _ _
  have ht : 0 ≤ t := div_nonneg (mul_pos hg hp).le hβ.le
  have he : p = Delay.fineMonitor G L x := Clock.watch_two _
  have ht' : t ≤ 2*p := (div_le_iff₀ hβ).mpr (by change Clock.gap y*p ≤ 2*p*_; nlinarith only [hy,hp])
  let u := Q.mark L μ x
  have hu : u= μ/4*p^2 := by rw [he]; unfold u; change μ/2*(1/2)*Delay.fineMonitor G L x^2 = μ/4*_; ring
  have hrate : -u ≤ -κ * Delay.fineMonitor G L x ^2 + -A.hard*t^2 := by
    rw [hu,← he]; unfold κ; nlinarith only [mul_le_mul_of_nonneg_left (sq_le_sq₀ ht (ht.trans ht')|>.2 ht') hr.le,mul_le_mul_of_nonneg_right hA (sq_nonneg (2*p))]
  unfold Time.Forecast.pair Progress.DirectedRecipe.Payments.Pairing.strong
  dsimp only
  let l := Real.exp (-A.hard*t^2); have ha := (le_abs_self _).trans hv;
  refine le_trans (Real.exp_le_exp.mpr hrate) ?_; rw [Real.exp_add]
  change Z x*l ≤ c*(max 1 A.coeff*l);
  exact (mul_le_mul_of_nonneg_right ha (show 0 ≤ l from (Real.exp_pos _).le)).trans
    (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Real.exp_nonneg _) (le_max_left ..)) hc.le)
end rent

section preparation
variable {X:Sheet G} {Tc : MapPrices}{Q : Targets X Tc} (Z : Expenses Q) {v : ℕ→ℝ}
      {D:Rolls X} {P₀:Return.Wages}(Y:PhysicalNext.Repeat.Register D Z P₀ v) {F' : ℕ→ℕ→Postage} (F: Time.Scouts (F:=F'))
      {Θ : Protection D}(U : Delays Θ)(hi : ∀ i j,StepStages j i → qualify Z i j (D.L j).val)
variable (η : ℕ →ℝ) (hη : ∀ j,0 < η j)
set_option quotPrecheck false
local notation "x₁"=> (X.profile i)
local notation "x₂"=>(X.profile j)
local notation "L★"=>D.L j
local notation "ℓ★" => (Z j i)
variable (i j:ℕ) (h0:4≤j)
open RGComparison01.Pledge

-- stronger price than needed, covers all likely finite-load rough calls.
structure Juvenile -- include n width? K buy tracks through power d.
    (B:Bauble G (D.L j)) (k k':ℕ)(η₀ s:ℝ): Prop where
  permission : Cellar (Q j i) Chi.canonical (P₀ j i) (D.L j) (Mural.sheet X D h0) (Y.o j i) (X.profile i).order k k' (X.profile i).power (Y.μ j i) (Z j i).earn (asset (Z j i)) B.mass B.pre B.roi B.miss B.invZ s
  prehit : ∀ β,Next.Scheduling.inBand (betaF G s (D.L j)) β → Real.exp (-(Q j i).mark (D.L j) (Y.μ j i) s) ≤ 1/8*(F j i).pair.strong (betaF G s (D.L j)) β
  charge : ∀ β,0<β→ betaF G s (D.L j)/2 ≤ β→ |B.roi s| ≤ gStep β ^ (-η₀) ∧ |B.invZ s| ≤ gStep β ^ (-η₀) ∧ |B.miss s|≤ gStep β ^ (-η₀)
  -- these two also true from schedule (hat≥1, seeds_paid) later; leave here for all m, not just ∀ᶠ
  logical : 1< betaF G s (D.L j)
  paid : Height.grow G (D.L j) s ^ k ≤ Real.exp ((Q j i).mark (D.L j) (Y.μ j i) s)

lemma split_seed (G: Gauge)(P:Teller G)(Q:ConnectedActivityE6.Target G P)(L:Side) (k:ℕ)(μ:ℝ)(h:0<μ):
    ∀ᶠ x in atTop,Height.grow G L x^k ≤ Real.exp (Q.mark L μ x) := by
  have hh : Rate G L (3/8) (Height.grow G L):= Rate.power
  have hp : Rate G L (-(3/8*(k:ℝ))-1) (fun x=>Real.exp (-Q.mark L μ x)):= by
    apply Rate.congr (Rate.monitor_cutoff (show 0<μ/2*(1/2) by positivity) (show 0 < (2:ℝ) by norm_num)) (Eventually.of_forall fun x=>?_); dsimp only; rw [Real.rpow_two]; change Real.exp (-(μ/2*(1/2)*Delay.fineMonitor G L x^2))=_; rw [neg_mul]
  filter_upwards [((hp.mul (hh.pow k)).below (by ring_nf; norm_num) 1 zero_lt_one)] with x hx
  apply (le_of_mul_le_mul_left ?_ (Real.exp_pos (-Q.mark L μ x))); apply le_trans ((le_abs_self _).trans hx); rw [← Real.exp_add, neg_add_cancel,Real.exp_zero]
local notation "Ju" => Juvenile Z Y F i j h0
variable (hp:Pocket Y F)
include hi hp hη
lemma negotiable (hv:StepStages j i) (k:ℕ): ∃ (l:ℕ) (B:Bauble G (D.L j)), ∀ᶠ s in atTop, Juvenile Z Y F i j h0 B k l (η j) s:=by
 have ha := hi i j hv; have hW:= (Y.consumes j i hv).2.1; let X₀:= (Mural.sheet X D h0);
 obtain ⟨P,l,hP⟩:= ha (D.L j) le_rfl X₀ (X.has _) _ _ (Y.consumes j i hv).1 hW (Y.o j i) (X.profile i).order k (X.profile i).power
 refine ⟨l,P,?_⟩
 filter_upwards [hP, resize_seed _ (Q j i) (D.L j) _ hW _ (F j i) (hp.price j i hv) _ (show (0:ℝ)<1/8 by norm_num), Geo.loss P.revenue (hη j) 0, Geo.loss P.positive (hη j) 0, Geo.loss P.progress (hη j) 0, (Work.E09.betaF_growth G (D.L j)).eventually_gt_atTop (1:ℝ), split_seed G _ (Q j i) (D.L j) k _ hW] with t ht he h₁ h₂ h₃ hβ hB; -- annotations
 exact ⟨ht,he,fun β v hx=> by simpa only [pow_zero,mul_one,Nat.cast_zero,zero_sub] using And.intro (h₁ β v hx) (And.intro (h₂ β v hx) (h₃ β v hx)),hβ,hB⟩

-- pre-L qualifier is monotone pointwise
omit hp hη hi
lemma clearance : ∃ f:ℕ→ℕ, ∀ i j (_:StepStages j i), ∀ L≥f j, qualify Z i j L := by
 choose b h using fun i j=> priorBill Z i j; refine ⟨fromMax (fun j i=> b i j),fun i j hx L hL L' hl=> h i j L' (le_trans (?_) hl)⟩; exact le_trans (le_fromMax (fun j i=> b i j) hx) hL
structure Facilities (ν:ℕ → ℕ) : Prop where
  every : ∀ i j (_:StepStages j i)(h0:4 ≤ j), ∀ k≤ ν j, ∃ (l:ℕ) (B:Bauble G (D.L j)), ∀ s≥ U.betaEntry j, Juvenile Z Y F i j h0 B k l (η j) s

include hp hη hi
lemma advance (H:ℕ→ℕ): ∃ W: Delays Θ, DelayLe U W ∧ ∀ V:Delays Θ, DelayLe W V→ Facilities Z Y F V η H := by
   let p v j i := ∀ h0:4≤j, ∀ k≤ H j, ∃ (l:ℕ) (B:Bauble G (D.L j)), ∀ s≥v, Juvenile Z Y F i j h0 B k l (η j) s
   have h j i (hi':StepStages j i): ∀ᶠ v in atTop,p v j i:= by
     by_cases h : 4≤ j; swap; · exact Eventually.of_forall fun _ hv=> (h hv).elim
     have hW k (_: k∈Finset.range (H j+1)): ∀ᶠ x in atTop, ∃ l B, ∀ s≥x, Juvenile Z Y F i j h B k l (η j) s:= by
       obtain ⟨l,B,H⟩:= negotiable Z Y F hi η hη i j h hp hi' k; obtain ⟨x,hX⟩:= eventually_atTop.mp H; exact (eventually_ge_atTop x).mono fun t ht=>⟨l,B,fun u hu=> hX _ (ht.trans hu)⟩
     exact ((Filter.eventually_all_finset (I:=range (H j+1))).mpr hW).mono fun x hx _ k hk=> hx k (mem_range.mpr (by omega))
   obtain ⟨x,-,hx,hX⟩:= collect_upper U.betaEntry (fun j v=>∀ i, StepStages j i → p v j i) fun j=>eventually_transitions j _ _ (h j)
   exact ⟨{ U with betaEntry:=x },⟨hx,le_rfl,le_rfl,le_rfl⟩, fun _ h=>⟨fun i j l h₁ k => hX j _ (h.beta j) i l h₁ k⟩⟩
end preparation

end YM.Qlocal.Leasing
