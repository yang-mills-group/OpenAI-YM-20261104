import YM.LocalTaylorR2.Reel.Taproom
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Reel
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
open Strand Rain Roost Mallow Capstone
section blend
variable {G:Gauge}{b:Side}
def curve (g f:Reel.Scroll G b)(α:ℝ)(u:Strand):= g+dial u • (α • (f-g))
-- assume at TRUE x budget side P. NO Lit/extraction of new payment agencies. input d parameter total. 
structure Affords (V:Rep G b)(Z:Levels G)(m:ℕ)(f:Scroll G b)(d:ℝ):Prop where
   leftB : 0 < d
   small : 2*d ≤ Z.clock.allowance m
   stamps : ∀ u:Strand, Sizing Z m (bend V (curve V.activities.E f (Z.clock.allowance m/(2*d)) u)) (Z.clock.allowance m)
-- no need price in d explicitly for interpolation premise; will include also in consumer
lemma blend_it {V:Rep G b}{Z:Levels G}{m:ℕ}{f:Scroll G b}{d:ℝ}(hx:Affords V Z m f d):
   ∃ (a:Strand), 0≤dial a ∧ dial a=2*d/Z.clock.allowance m ∧ curve V.activities.E f (Z.clock.allowance m/(2*d)) a=f:=by
   have ht:0<d:=hx.leftB; let k:=Z.clock.allowance m; let y:=V.activities.E
   have he:0<k:=(mul_pos zero_lt_two ht).trans_le hx.small
   have hh:0≤2*d/k:=by positivity
   refine ⟨⟨2*d/k,⟨by linarith,(div_le_one he).2 hx.small⟩⟩,hh,rfl,?_⟩
   change y+ (2*d/k) • ((k/(2*d)) • _) = f; rw [smul_smul, show 2*d/k*(k/(2*d))=1 from by field_simp,one_smul]; abel
end blend
variable {G:Gauge}{M:Metals G}{D:Rolls M.p}{A:Alloy M D}
   (R:Factor A){m n N:ℕ}{l k:ℝ}{Q:In A.B.a m n}(H:Spring R N m n l k Q) (x:ℝ)(hx:x∈Set.Icc l k)
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
def allotE := fun i=> if (pennant I i).2 ∈ Meadow.bouquet I d then 0 else (sight (Y) w X ❖ γ p true (fun i=>¬p+1 ≤ i)) i
-- no use full E in the new pass. Keep beacons from Track IV uses non-E Shadow inputs! Z.* reads many actual GS*
def abridge := { (a!) with
   logRead:= (bison { (Rain.uptick H.H H.ordinal x) with logRead:= allotE R H x w p } (Capstone.rescue R H x p true) 0).regular }
def wages := { (a!) with logRead:= (a!).logRead-(abridge R H x w p).logRead }
variable (hE:Mallow.RG12.Earned (ticketD G) R.shape A.delay)(he:Mallow.RG12.Earned (wheelD G) R.shape A.delay)(hm:m<N)
   (hV:p ≤ A.B.a.clock.J (m+1)) (h₀: 3 ≤ p)
local notation "fc"=> Time.forecastE A.B.a m
local notation "Ks"=>Time.forecastK A.B.a m R.scout (Q x).beta
-- invoices.Scope
lemma arrangement : Yoke I (abridge R H x w p).logRead ∧ Yoke I (a!).logRead := by
   have he : ∃ g: Magazine I → Config G b→ℝ, allotE R H x w p=choir g ∘ pennant I:= by
      refine ⟨fun i=> if i∈ Meadow.bouquet I d then 0 else crawl Y w X ❖ γ p true (fun i=>¬ p+1 ≤ i) i,?_⟩; ext1 i; unfold allotE; dsimp only [choir,Function.comp_apply]; split
      next h=> ext; simp
      next h=> rfl
   exact ⟨replenished I (α:=Capstone.rescue R H x p true) («X»:=0) (uV:={(Rain.uptick H.H H.ordinal x) with logRead:= allotE R H x w p}) (by exact he) rfl, replenished I (α:= Rain.beacons H.H H.knows H.W d x) («X»:= Rain.lights H.H H.knows H.W d x) (uV:= Rain.uptick H.H H.ordinal x) ⟨_,rfl⟩ rfl⟩

include hE he hV h₀ hx hm
variable {v:ℝ}(hA:Affords (Q x) A.B.a (m+1) w v)
include hA
local notation "L" => CalendarStep.loss Ω
local notation "e" => Capstone.fare k₀ (A.B.a.params m) z * (z' ^ requested (p+1) (L))
local notation "q"=> (2*v/Φ')
local notation "v'!"=> (q*fc)
local notation "p'" => Capstone.sketch R H x p true
lemma royalty : Meadow.Budget B H.H.doors.reg (allotE R H x w p-(Capstone.rigging R H x p true).logRead) v'! :=by
    let W:=w'; let S:=(Φ'/(2*v)) • (w-W); let X':=Q (τ)
    have hf : Q (τ)=Q x:=congr_arg Q (by rw [Roof.Embrasure.click H.H x hx]); rw [← hf] at hA
    obtain ⟨g,hg,hb,h⟩:= blend_it hA; obtain ⟨hr,hc⟩:= H.knows _ (τ).property; have hh:= (H.knows _ H.H.he).1
    have hp : ∀ j:Strand, PartialLives A.B.bake N (m+1) n (bend X' (W+dial j • S)):= fun j=>⟨hr.path,hr.point,hr.clip,hA.stamps j⟩
    have hv := renting R hm hc I (hr.path.trans hh.path.symm) (H.waves.reg _ H.H.he _ (τ).property) (H.waves.forced _ H.H.he _ (τ).property) hE Y X S p (H.H.agrees _) hV (le_trans (by norm_num) h₀) hp g hg
    have hw :0 ≤ (fc):= mul_nonneg (Time.credit_pos ..|>.le) (Capstone.allow_pos ..)
    let y:=sight Y (W+dial g • S) X ❖ γ p true (fun i=> ¬p+1 ≤ i)-sight Y W X ❖ γ p true (fun i=> ¬ p+1 ≤ i)
    have hu: Meadow.Budget B H.H.doors.reg y (dial g * fc) := Reel.budgetF hv (by
      have hl:=(trust R he p hV h₀).2.1
      change 0 ≤ (g:ℝ) at hg; unfold dial; nlinarith only [mul_le_mul_of_nonneg_right hl hg,mul_nonneg hg hw])
    rw [hb] at hu
    have hx : allotE R H x w p-(Capstone.rigging R H x p true).logRead=(fun i=> if (pennant I i).2∉ Meadow.bouquet I d then y i else 0):=by
       ext1 i; unfold allotE rigging songKeep sheaves; unfold y; simp only [ite_true,Pi.sub_apply]; split_ifs
       · simp
       rw [accrues Y X ❖ γ p true (fun i=> ¬ p+1 ≤ i) (fun _ h=>by omega),show W+dial g • S=w from h] -- W
    rw [hx]; convert! reenact (fun i=>(pennant I i).2 ∉ Meadow.bouquet I d) hu using 1; ext1 i; split_ifs <;> rfl
local notation "U" => abridge R H x w p
local notation "P" => wages R H x w p
lemma keeperP : Meadow.Budget B (O).reg ((U).logRead-(p').logRead) v'! := by
    have h:=royalty R H x hx w p hE he hm hV h₀ hA
    let u:={(Rain.uptick H.H d x) with logRead:=allotE R H x w p}
    exact lanes H.H.doors (n:=a) (2*a) («B»:=B) («U»:=u) (V:=Capstone.rigging R H x p true) («Y»:=0) (Z:=Rain.lights H.H H.knows H.W d x) (A:=Capstone.rescue R H x p true) h
lemma sandbox : Collection.Local (O) B P (e + v'!) Ks:=by
    have hb:=(arrangement R H x w p); let f:=Capstone.sketch R H x p false
    have ht:= H.core hm x hx; obtain ⟨hd,hv,hF,hk,hk'⟩:= Capstone.rebased R H x hx p hE hV hm
    refine scoop I _ _ _ ht rfl (active_sub I hb.2 hb.1) ?_
    have hh : (P).logRead=f.logRead-((U).logRead-(p').logRead):=by unfold wages; dsimp only []; rw [hd]; change _+ f.logRead - (U).logRead =_; abel
    rw [hh]; exact Reel.gauges_sub (Capstone.budget_of_local hk') (keeperP R H x hx w p hE he hm hV h₀ hA)
end YM.LocalTaylorR2.Reel
