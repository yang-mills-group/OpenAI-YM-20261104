import YM.LocalTaylorR2.King.Beacon
/-! # MAIN ledger and its two new Taylor debits after inheriting E. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.King
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Captain
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Ovens Time UVNext UVNext.CouplingReset Daisy.Charity.RG12 Tail
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open CalendarStep
local notation "❖" => Chi.canonical

/-! # Lens core E-error post the actual regroup, with inherited error as input. -/
open Reel Strand Rain Roost Mallow Capstone

variable {G:Gauge}{M:Metals G}{D:Rolls M.p}{A:Alloy M D}
   (Ξ:Engine G)(R:Factor A){m n N:ℕ}{l k:ℝ}{Q:In A.B.a m n}(H:Spring R N m n l k Q) (x:ℝ)(hx:x∈Set.Icc l k)
   (w: Reel.Scroll G (A.B.a.S.side (m+1) n))(p:ℕ)
local notation "z"=> A.B.a.clock.hatBeta m
local notation "z'"=> A.B.a.clock.hatBeta (m+1)
local notation "Ω"=> A.B.a.clock.J (m+1)
local notation "B"=> A.B.a.budget m
local notation "K"=> A.B.a.params m
local notation "b"=> A.B.a.S.side m n
local notation "τ"=> (H.H.latch x)
local notation "d"=> H.ordinal
local notation "I"=> H.H.base
local notation "a!"=> H.V' x
local notation "O"=> H.X'
local notation "r"=> (H.result x)
local notation "xH"=> (Q x)
local notation "Y"=> (H.H.houses (H.H.latch x))
local notation "γ"=> A.B.kin.alpha N m
local notation "T"=> (A.B.kin.path N m)
local notation "X"=> (H.H.sister (H.H.latch x))
local notation "k₀"=> Rain.lint R.target A m
local notation "a"=> Trio.base k₀ (radiusB z)
local notation "Φ"=> A.B.a.clock.allowance m
local notation "Φ'"=> A.B.a.clock.allowance (m+1)
set_option quotPrecheck false
local notation "w'"=> ((Q (τ)).activities.E)
-- override before reclosure. K lights unaffected.
def raiment := fun i=> if (pennant I i).2 ∈ Meadow.bouquet I d then 0 else (comet Y Ξ w X ❖ γ p true (fun i=>¬p+1 ≤ i)) i
-- no use full E in the new pass. Keep beacons from Track IV uses independent auxiliary Shadow inputs‟ convention as IV (uses their actual E)! Z.* reads many actual GS*
def alumni := { (a!) with
   logRead:= (bison { (Rain.uptick H.H H.ordinal x) with logRead:= raiment Ξ R H x w p } (King.pillar Ξ.toRegime R H x p true) 0).regular }
def ordersDue := { (a!) with logRead:= (a!).logRead-(alumni Ξ R H x w p).logRead }
variable (hE:Mallow.RG12.Earned (ticketD G) R.shape A.delay)(he:Mallow.RG12.Earned (wheelD G) R.shape A.delay)(hm:m<N)
   (hΞ:Mallow.RG12.Earned (survey Ξ.toRegime) R.shape A.delay) (hV:p ≤ A.B.a.clock.J (m+1)) (h₀: 3 ≤ p)
local notation "fc"=> Time.forecastE A.B.a m
local notation "Ks"=>Time.forecastK A.B.a m R.scout (Q x).beta
-- invoices.Scope
lemma arrangement : Yoke I (alumni Ξ R H x w p).logRead ∧ Yoke I (a!).logRead := by
   have he : ∃ g: Magazine I → Config G b→ℝ, raiment Ξ R H x w p=choir g ∘ pennant I:= by
      refine ⟨fun i=> if i∈ Meadow.bouquet I d then 0 else ebony Y Ξ w X ❖ γ p true (fun i=>¬ p+1 ≤ i) i,?_⟩; ext1 i; unfold raiment; dsimp only [choir,Function.comp_apply]; split
      next h=> ext; simp
      next h=> rfl
   exact ⟨replenished I (α:=King.pillar Ξ.toRegime R H x p true) («X»:=0) (uV:={(Rain.uptick H.H H.ordinal x) with logRead:= raiment Ξ R H x w p}) (by exact he) rfl, replenished I (α:= Rain.beacons H.H H.knows H.W d x) («X»:= Rain.lights H.H H.knows H.W d x) (uV:= Rain.uptick H.H H.ordinal x) ⟨_,rfl⟩ rfl⟩

include hΞ hE he hV h₀ hx hm
variable {v:ℝ}(hA:Affords (Q x) A.B.a (m+1) w v)
include hA
local notation "L" => CalendarStep.loss Ω
local notation "e" => Capstone.fare k₀ (A.B.a.params m) z * (z' ^ requested (p+1) (L))
local notation "q"=> (2*v/Φ')
local notation "v'!"=> (q*fc)
local notation "p'" => Capstone.sketch R H x p true
omit he h₀ in
lemma kings : Meadow.Budget B H.H.doors.reg (Reel.allotE R H x w p-raiment Ξ R H x w p) (2*z' ^ requested (p+1) L):=by
   let X':=Q (τ)
   have hf : Q (τ)=Q x:=congr_arg Q (by rw [Roof.Embrasure.click H.H x hx]); rw [← hf] at hA
   obtain ⟨g,hg,hb,h⟩:= Reel.blend_it hA; obtain ⟨hr,hc⟩:= H.knows _ (τ).property; have hh:= (H.knows _ H.H.he).1
   have hu:= hA.stamps g; rw [h] at hu; have hp : PartialLives A.B.bake N (m+1) n (bend X' w):= ⟨hr.path,hr.point,hr.clip,hu⟩
   obtain ⟨J,hJ⟩:= Opera.partial_feature A.B R.shape hm R.pledging.conducts.full R.pledging.conducts.income hp hc
   let U:Match.Alliance (I) J 1 0:= Match.staple (hh.path.trans hr.path.symm) (H.waves.reg _ H.H.he _ (τ).property) (H.waves.forced _ H.H.he _ (τ).property)
   let ℓ:= z'^requested (p+1) (L); let V:=sight (Y) w X ❖ γ p true (fun i=>¬p+1 ≤ i) - comet (Y) Ξ w X ❖ γ p true (fun i=>¬p+1 ≤ i)
   have hu: Meadow.Budget B (Beam.marquee I B).reg V (2*ℓ):=by
      let y:= A.B.a.S.oneStep m n; obtain ⟨C₁,C₂,f,t₀,A₁,a₁,B₁,b₁,j₁,D₁,y₁,w₁,T₁,f₁,J₁,Z₁,h₁⟩:= engaged R y.exact_size J hm hE p hV (L) le_rfl
      obtain ⟨C₂,C₁,f,t₀,A₁,a₁,B₁,b₁,j₁,D₁,y₁,w₁,T₁,f₁,J₁,Z₂,h₂⟩:= loaded Ξ.toRegime R y.exact_size J hm hΞ p hV (L) le_rfl
      let Ξ₀:=Ξ.toRegime
      have ha: (plusone I U ❖ γ).logRead= (sheaves J U γ p true).logRead+(sheaves J U γ p false).logRead:=by simpa only [sheaves,Bool.false_eq_true,ite_false,ite_true] using! YM.LocalTaylorR2.subtract J h₁.probed U (A.B.kin.alpha N m) (fun i=>p+1 ≤ i)
      have hb: (plusone I U ❖ γ).logRead=(stellar J U γ p Ξ₀ true).logRead+(stellar J U γ p Ξ₀ false).logRead:=by simpa only [stellar,Bool.false_eq_true,ite_false,ite_true] using! YM.LocalTaylorR2.subtract J h₂.probed U (A.B.kin.alpha N m) (fun i=>p+1 ≤ i)
      have hc: V=(stellar J U γ p Ξ₀ false).logRead-(sheaves J U γ p false).logRead:=by
         unfold V; have hv (i:ℕ)(hi: ¬ p+1≤ i):i≤p:=by omega
         have hx:(X).units=Equiv.refl _:= H.H.agrees (τ)
         rw [verges Y w X J U rfl hx _ _ p true _ hv,heal Y Ξ w X J U rfl hx _ _ p true _ hv]; unfold sheaves stellar at *; simp only [ite_true,ite_false,Bool.false_eq_true] at *; unfold Ξ₀ at hb ⊢; rw [ha] at hb; exact sub_eq_sub_iff_add_eq_add.mpr (by rw [add_comm ((cohort J («χ»:= ❖) U γ (M:=p) (Mesh.issue J (Ξ.symbol J p) ❖) true (fun i=> ¬p+1 ≤ i)).logRead)] at hb; exact hb) -- check orientation
      rw [hc, two_mul]; apply gauges_sub
      · simpa only [stellar,Bool.false_eq_true,ite_false] using! bequeath Ξ.toRegime R y.exact_size J h₂ U (le_refl (p+1)) (fun i=> p+1 ≤ i) (fun _ hi=>hi)
      simpa only [sheaves,Bool.false_eq_true,ite_false] using! allocation R y.exact_size J h₁ U (le_refl (p+1)) (fun i=> p+1 ≤ i) (fun _ hi=>hi)
   have heq: Reel.allotE R H x w p-raiment Ξ R H x w p=(fun i=> if (pennant I i).2∉ Meadow.bouquet I d then V i else 0):=by
      ext1 i; unfold Reel.allotE raiment; simp only [Pi.sub_apply]; split_ifs; · rw [sub_self]
      rfl
   rw [heq]; convert! Reel.reenact (fun i=> (pennant I i).2∉ Meadow.bouquet I d) hu using 1; ext1 i; split_ifs <;> rfl
end YM.LocalTaylorR2.King
