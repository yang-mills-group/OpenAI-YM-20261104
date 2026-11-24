import YM.Qlocal.Leasing
/-!
Instantiate the universal primitives at a scheduling lease in the purchased currency.
Available at the Guide for any admitted period & construction-cutoff. Reclosure
trace tickets use the same θ. The support exponent ticket buys at least +3
at this entry, of which +2 is needed for two packings at that step. Strong CP.
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
variable {M:Metals G}{R':Rolls M.p}{A:Alloy M R'} (F:Roost.Factor A)
    {m N p:ℕ} {η:ℕ→ℝ} {u:ℕ→ℕ}
local notation "C₀"=> A.B.a
set_option quotPrecheck false
local notation "c"=> A.B.a.S.side m p
local notation "f"=> A.B.a.S.side (m+1) p
local notation "J"=> A.B.a.clock.J (m+1)
local notation "I"=> A.B.a.clock.J m
local notation "S₀"=> (C₀).clock.op m p
local notation "Y"=> (Mural.sheet M.p R' ((C₀).clock.adm (m+1)))
local notation "x₀"=> (C₀).clock.hatBeta m
local notation "θ"=> (C₀).budget m
local notation "μ₀"=> F.shape.μ J I
local notation "L★"=> R'.L J
local notation "F'"=> (F.target J I)
local notation "ℓ★"=> (F.expense J I)
variable (hκ: Facilities F.expense F.shape F.scout A.delay η u)
include hκ
local notation "B!"=> Bauble G L★
section career
local notation "q" => Θ -- conflict
structure Opened (η':ℕ→ℝ) (k k' : ℕ) (m:ℕ) (B:Bauble G (R'.L (A.B.a.clock.J (m+1)))): Prop where
  paid : ∀ β ≥ A.delay.betaEntry (A.B.a.clock.J (m+1)),
     Juvenile F.expense F.shape F.scout (A.B.a.clock.J m) (A.B.a.clock.J (m+1)) (A.B.a.clock.adm (m+1)) B k k' (η' (A.B.a.clock.J (m+1))) β

-- note include hκ in structure? omit before.
lemma payable (hm:k ≤ u J) : ∃ k' B, Opened F η k k' m B := by
  obtain ⟨l,B,h⟩:= hκ.every _ _ (step_paid C₀ m) (A.B.a.clock.adm (m+1)) _ hm; exact ⟨l,B,⟨h⟩⟩
end career
omit hκ
variable (η) (B':Bauble G (R'.L (A.B.a.clock.J (m+1)))) (hB : Opened F η k j m B')
local notation "s"=> θ.supportExponent
local notation "λ★"=> β -- placeholder
include hB
lemma resize_pay {β:ℝ} (he: β∈band (C₀) (m+1)) : Real.exp (-(F').mark L★ μ₀ x₀) ≤ Time.forecastK (C₀) m F.scout β / 8 := by
  have ht : inBand (betaF G x₀ L★) β:= by rw [← PriceCompiler.beta_eq A.B.valid]; exact trial_in he
  have he':= (hB.paid x₀ (A.B.valid.pays m)).prehit β ht; exact he'.trans_eq (by unfold Time.forecastK; rw [PriceCompiler.beta_eq A.B.valid]; ring)
lemma subpower {β:ℝ} (he: β∈band (C₀) (m+1)) : 0 < β ∧ |B'.roi x₀| ≤ gStep β^(-(η J)) ∧ (B'.mass x₀)⁻¹ ≤ gStep β^(-(η J)) ∧ |B'.miss x₀| ≤ gStep β^(-(η J)) := by
  let h:= hB.paid x₀ (A.B.valid.pays m); have hb : betaF G x₀ L★ / 2 ≤ β := by rw [← PriceCompiler.beta_eq A.B.valid]; exact he.1
  have hp:0 < β:= (half_pos (zero_lt_one.trans h.logical)).trans_le hb; have he:= h.charge β hp hb
  exact ⟨hp,he.1,h.permission.shores ▸ (le_abs_self _).trans he.2.1,he.2.2⟩

-- remove macro repeats.Note include opened
local notation "u★"=> (A.B.a.S.oneStep m p).exact_size
variable {R:RG.Rep G (A.B.a.S.side (m+1) p)} (Y': Boulevard.Chartlet F.shape A N m (A.B.a.S.oneStep m p).exact_size R) -- Guide conversion later
    (hr:Boulevard.SeekR F.shape A N m (A.B.a.S.oneStep m p).exact_size Y') (hm:m<N) (hβ:R.beta ∈ band A.B.a (m+1))
    {Ω : Type} {L : ι → Lotus.Leaf R}{D : Ω → ι→ Lotus.Leaf R}
    {w₀ : ℕ→Prop}
local notation "D₀"=> selfA Y'
local notation "O"=> Chi.canonical
local notation "γ"=> A.B.kin.alpha N m
local notation "τ"=>(F.expense J I).earn
local notation "K'"=> weighty Y' O
local notation "A'"=> (Beam.marquee Y' θ).read (Song.plusone Y' D₀ O γ)
-- avoid ambiguity writing header. support.S.F enclosure all V.
variable [Fintype ι] (h : Roster L D) (g:ι→ℝ) (hx: Bench L g (B'.mass (A.B.a.clock.hatBeta m)))
  (hE: (Tithe.portion R.activities Ψ).EBound R.p e)(he : e ≤ incomingE G (R'.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m))
include hm hr hβ hx hE he
local notation "Z₁"=>Time.forecastK A.B.a m F.scout R.beta / 8
local notation "K₀"=> fun x=> Palette.shoot (D x) Y' O g Y' D₀
open Primitive
set_option maxHeartbeats 1000000 in
theorem supplies (x : Forest (S₀).ratio) :
   SwitchStep D S₀ g (Gorges.epochs F m u★ Y' x) (A') θ (K₀)
    (fun x z=> Ink.yielded (D x) g Y' (χ:=O) (h.castLabel Y' x z)) ∧
   Primitive.Earnings Y' O h γ (θ) g D₀ Ψ j (B'.roi x₀/(Height.grow G L★ x₀)^k)
      Z₁ e (B'.miss x₀) (B'.roi x₀) (τ) ∧ (θ).supportExponent+3≤τ:= by
  let z:= hB.paid x₀ (A.B.valid.pays m); let Yw:= F.target J I; let H:= A.B.a.clock.J (m+1); have hZ:= z.permission;
  have hv : (Pane.panel A m u★).patch=Y:= Y'.laws.data.funds.patch rfl rfl
  rw [← hv,(Rain.jersey (A:=A) (m:=m)).1.symm, (Rain.jersey (A:=A) (m:=m)).2.1.symm] at hZ
  let σ:=F.pledging.jewels _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)
  obtain ⟨c',d,v,s',z',q,r,k',Yℓ,l,t,⟨N',hT⟩,hN,h₁⟩:= σ.2 _ _ _ (Pane.orchestra A N u★) Y'.laws.data.funds (Pane.ovation A N u★ hm F.pledging.conducts.full) R Y'
  have hz:= Pane.ovation A N u★ hm F.pledging.conducts.full
  obtain ⟨hp,hQ⟩:= Primitive.complete Y' O h γ θ g x (D₀) hZ rfl rfl hx hz hE he z.paid N' (A.B.support.cap N m hm.le) ((Rain.jersey (A:=A) (m:=m)).1.le) hr
  refine ⟨hp, ?_,?_⟩
  · have hK := (hZ.buys _ _ _ _ rfl hz R _ Y').1 ι L g hx; exact
     { hQ with force:= hQ.force.relax ((mul_le_of_le_one_right (Real.exp_nonneg _) (by linarith only [hK.books])).trans (resize_pay F η B' hB hβ)) le_rfl }
  rw [(Rain.jersey (A:=A) (m:=m)).2.2.1]; exact F.pledging.agenda _ _ (step_paid A.B.a m)|>.1
end YM.Qlocal.Leasing
