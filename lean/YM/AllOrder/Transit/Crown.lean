import YM.AllOrder.Quay.Tariff
import YM.AllOrder.Transit.Refuge
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Transit
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Bid Planned.JetPort PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Trio Lantern High
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm JointLoad.Clockwork
open Burn Carillon Cap
open Rosary.Repair
open Transit Transit.Moon Transit.Moon.Kit
open Floe Floe.StateE
open Step PlanV Roost
variable {G:Gauge}{X:Metals G}{D:Rolls X.p} (R: Roots (G:=G) X.p.profile X.K X.p.kernel) (Q:R.Tab D)(A:Alloy X D)(F:Factor A)
namespace WheelP
variable {m n k N:ℕ} (h:Pass R Q A F)
local notation "S"=> X.p
set_option quotPrecheck false
local notation "a"=> A.B.a
local notation "C"=> X.p.profile
local notation "E"=>A.B.a.clock.J m
local notation "Y"=> A.B.a.clock.J (m+1)
local notation "V"=> A.B.a.budget m
local notation "y"=> A.B.a.clock.hatBeta m
local notation "L"=> D.L Y
local notation "t"=> betaF G y L
local notation "s"=> (C E)
local notation "W"=> A.B.a.budget (m+1)
local notation "B"=> radiusB y
local notation "g"=> A.B.a.S.block m
local notation "T"=> F.target Y E
local notation "P!"=> (F.expense Y E)
local notation "p"=> A.B.a.params m
local notation "z"=> Burn.horizon k
variable (g0:G.Simple)(hm:m<N)(hk:Burn.horizon k+2≤ A.B.a.clock.J m)
variable (Xξ: Org.Bolt A)
-- At actual TOP horizon. prove PeriodFuture begins. alternative Starter.
open WilsonStartup -- qualified hZ
open Quay
open Progress.DirectedRecipe Ovens
section dawn
local notation "T'"=> F.book
section
variable {P:Protection D} (W':Delays P)
def Header: Prop:= ∀ i j k:ℕ, k ≤ i → StepStages j i →∀ x≥ W'.betaEntry j,Quay.BandTar G (C i) k x
lemma demands : ∃ Vξ:Delays P, DelayLe W' Vξ∧ ∀ Wξ:Delays P, DelayLe Vξ Wξ→ Header Wξ:=by
 obtain ⟨t',-,hx,hy⟩:= collect_upper W'.betaEntry _ (fun j=> eventually_transitions j _ _ fun i hi=> (Filter.eventually_all_finset (Finset.Iic i)).mpr (fun k hk=> Quay.thaw k (C i))|>.mono (fun i h' k hk=> h' k (Finset.mem_Iic.mpr hk))); exact ⟨{ W' with betaEntry:=t'},⟨hx,le_rfl,le_rfl,le_rfl⟩,fun W' h i j k hk hi l hl=>hy _ _ ((h.beta j).trans hl) i hi k hk⟩
end
include h hk g0
lemma started(hV: Header A.delay) : ∃ u',A.B.bake.Starter m n u' ∧ Appearance A Xξ (Crest.tile (p).clip G) m n m k u':= by
 let w' := V; let v':=Quay.coupon; let o:= (p); let y':=(y); let i:=E; let u:= Xξ.history m n m; let β:=u.beta; have hy:0<y':= zero_lt_one.trans (A.B.a.fits.delayed _); let T0:= h.formal.terra; let hz:=T0.startup m; have hBand:β∈ band a m:= ((Xξ.sticks m n).prices m (Nat.zero_le _) le_rfl).2
 have hκ: k ≤ i:= (by unfold i; unfold horizon at hk; omega);
 have hp : Quay.BandTar G o k y':= by unfold o; rw [PriceCompiler.params_eq A.B.valid m]; exact hV _ _ _ hκ (step_paid A.B.a m) _ (A.B.valid.pays m)
 let W₀:= hp w' rfl rfl ⟨rfl,rfl,rfl⟩ β hz.clip hBand.1 hBand.2; obtain ⟨s',k',γ,hL,hP⟩:= W₀.pin; have hm' := W₀.ticket; let Γ:= (A.B.kin.path m m); have he: Γ= WilsonStartup.Design.top G o.clip:= T0.top m
 let Ξ:= Crest.tile o.clip G; let p0:= Till.Tilt.price w' G z w'.B (strengthP y) (gStep β) (Age.scope (z+2)); have hb: 0<β:= (half_pos hy).trans_le hBand.1
 let x:= A.B.a.S.side m n; have hn:4≤ x.val:= le_trans (by norm_num : 4≤20) (Return.enough_room A.B m n).le;
 let v:= offerS G w' Ξ (Age.scope (z+2)) (gStep β); let α:= A.B.a.clock.allowance m; let α':= A.B.a.clock.forcedAllowance m; have hM(i':Site x): Till.Fairness w' i' (Till.court i' w'.B) (v x i') p0:= Till.Tilt.paint Ξ (Age.scope (z+2)) _ (R.pre z (E)) ((Step.PlanV.begun R A F Q h.formal hk)) g0 _ _ hn _ _ (R.shape _|>.pos _) (fun i hi=> le_trans (Nat.mul_le_mul_left 4 (i.pricey.trans (Nat.add_le_add_right (Age.in_scope.mp hi) 2))) hm'.cuts); have hx := Quay.e_all («a»:=A.B.a) (n:=m) rfl hy;
 have hξ:= Quay.serves z w' o.clip β hL hz.clip hBand.1 hz.radius W₀.margin (hm'.cuts) hb hM (k'-1) ((hx.2).symm ▸ hP)
 have hs:Real.exp w'.supportExponent*p0 ≤ silver y:= hm'.near β (trial_in hBand); rw [← he] at hξ; obtain ⟨X,d,hI,hE,Vz,hJ⟩:= hξ
 let P₀:= fromTop A.B.kin m n β X d; have he' : P₀.eval = Wilson.bare β:= hE; have hJ : Ingredients X d w' α α':= Use.compatible_ingredients hI ((add_le_add hs W₀.books).trans (W₀.silver.trans_eq hx.1.symm)) le_rfl -- hJ shadow
 have hZ : SurfacePay A.B.kin (permissions A.B.a) m n β X d:= ⟨hJ,fun U=> ((hJ.unshifted Γ o.clip β 0 U).symm.trans (congr_fun he' U)), trivial⟩
 have hY : Lives A.B.bake m m n P₀:=by rw [F.machine.ready]; exact ⟨rfl,rfl,rfl,⟨A.B.support.cap m m le_rfl,hJ.gates ..⟩, PeriodFuture.begin hBand hZ⟩
 have hE:P₀.eval=(u).eval:= he'.trans (Xξ.sticks m n|>.fromTop.raw).symm
 refine ⟨P₀, (by rw [F.machine.ready]; exact starter hZ hBand _ _),rfl,hY,hE,Vz,(Candor.loosen (R:=P₀) ?_ hs W₀.books)⟩ -- hs defeq?
 assumption
end dawn
end WheelP
end YM.AllOrder.Transit
