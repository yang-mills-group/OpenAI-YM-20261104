import YM.AllOrder.Transit.Invite
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
local notation "G0"=> Shop.parking (Shop.tall E) ((T).halo)
local notation "Δ0"=> 1+cloak D (Y)
local notation "δ"=> (A.B.a.params m|>.width)
variable (X': Card D R (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) (A.B.a.clock.adm (m+1)) (Burn.horizon k))(hh:Journey R A (m:=m) (N:=N) X') -- syntax
local notation "Ω"=> litP R A Q hk X'
local notation "Plead"=> lead R Q A hk X'
local notation "W'"=> (C Y)
local notation "fφ"=>R.pre z Y
set_option quotPrecheck false
local notation "E'"=> A.B.kin.alpha N m
-- real.Seeds. preserve Bills uses true Guide & Vern.R.Actual Progress.Period
variable (x:ℝ)(hx:x∈ band A.B.a (m+1))
local notation "f"=>A.B.a.S.side (m+1) n
local notation "c!"=> A.B.a.S.side m n
local notation "S★"=> A.B.a.clock.op m n
local notation "Y!"=> Pane.panel A m ((A.B.a.S.oneStep m n).exact_size)
local notation "π"=> (A.B.a.S.oneStep m n).exact_size
local notation "Φ"=>goldN R Q A hk X' x
variable {U: RG.Rep G (A.B.a.S.side (m+1) n)} (hu:U.beta=x)
    (hp:Lives A.B.bake N (m+1) n U) (C₁:Burn.Seed U (M0 k 0 (A.B.a.budget (m+1)) (X'.extra) x))
    (hu':Candor (A.B.a.budget (m+1)) U.activities (Set.range C₁.model) (silver (betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1))))) (young (betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1)))) k))
    (K:Guide A.B F.shape N m n U)(hc:Opera.Price A.B F.shape N m n U K)
local notation "M"=> Set.range C₁.model
local notation "h′"=> LinkPat A F π K k M
local notation "Γ"=> A.B.kin.alpha N m
local notation "Θ"=> poem R A F X' π x K C₁
local notation "Op"=> Chi.canonical
local notation "v★"=> (heap G s (1/16)*young t k)
local notation "V₀"=> 2*v★
section Daze
local notation "Yz"=> Time.forecastE (a) m
local notation "Wz"=> Time.forecastK (a) m F.scout x
local notation "D₀"=> Time.fraction (a) m
local notation "D₁"=> Time.quoteHard (a) m F.book x
local notation "Ys"=> PostP.θ1 G s y k
local notation "Λ"=> (A.B.kin.path N m)
open UVNext.CouplingReset
open Progress.DirectedRecipe Ovens
local notation "B'"=> (p).clip
lemma sameCost : let f':=PostP.beg y; (a).clock.allowance m=f' ∧ (D₀)=f'/32 ∧ (Yz)≤ y:= by
 intro f'; have hp :1<y:=A.B.a.fits.delayed _; have ht:0< y:=zero_lt_one.trans hp; have hv : (a).clock.allowance m=f':=by
    change (Real.sqrt y)⁻¹ ^ (11/5:ℝ)= _; rw [Real.sqrt_eq_rpow,← Real.rpow_neg ht.le,←Real.rpow_mul ht.le]; exact congr_arg (fun z':ℝ=>y ^ z') (show (-(1/2:ℝ))*(11/5:ℝ)=-(11/10:ℝ) from (by norm_num))
 refine ⟨hv,congr_arg (fun x:ℝ=>x/32) hv,?_⟩; unfold Time.forecastE; rw [hv]; apply le_trans (b:=f') _ ((Real.rpow_le_one_of_one_le_of_nonpos hp.le (by norm_num : -(11/10:ℝ) ≤0)).trans hp.le); exact mul_le_of_le_one_left (Real.rpow_nonneg ht.le _) ((Time.authorized G (a|>.params m)|>.1).trans (by norm_num))
variable {X₀:Listing G (A.B.a.S.side m n)} {u₀:Collection.Source G (A.B.a.S.side m n)} {q b ℓ:ℝ}
-- ready old input.D comparison only needs witnesses at frame.H.Sensor.Base. Not assumption if Move supplies.Spec.N.S.
structure Ancillary (F:Factor A)(x:ℝ)(m n N:ℕ)(U: RG.Rep G (A.B.a.S.side (m+1) n))(d:ℝ):Prop where
    rents : ∃ X u ℓ, Collection.Local X (A.B.a.budget m) u (Time.forecastE A.B.a m) (Time.forecastK A.B.a m F.scout x)∧d=Averaging.delta (X.read u) ∧ ∀ V₁,(A.B.a.clock.op m n).push x U.eval V₁= earlyValue X (A.B.kin.path N m) (A.B.a.params m).clip (A.B.a.budget m) u x ℓ (A.B.kin.alpha N m) V₁
    near : Near (A.B.a.clock.hatBeta m) (x+A.B.kin.alpha N m+d) -- ¬ if out. actual pulse in interval assured history.
    step : |d|≤1
variable (hn: Ancillary A F x m n N U q)
local notation "βo"=> (x+Γ+q)
lemma cardP {P:Side} (R:RG.Rep G P) (h : ∀ i,R.activities.E i 1=0): R.eval 1=Real.exp (R.v* Fintype.card (Site P)):= by
 let p':=R.p; let A':Template G P:=⟨R.path,R.clip,R.p,fun _ _=>R.activities⟩; let w₀(x:ℝ):=R.beta; have hv:A'.trial w₀ 0 0 R.v=R:=(by unfold Template.trial w₀; rw [add_zero]); exact (congr_arg (fun H : RG.Rep G _=> H.eval 1) hv.symm).trans (A'.trial_one _ h)
include hp hn hm hu hx g0
lemma advance (P:Pipes G (c!))(Vθ:Tap G (c!))(H:Ingredients P Vθ (V) D₀ D₁)
    (he: (finish Λ B' V P Vθ βo ℓ).eval=(S★).push x U.eval): A.B.Move N m n (finish Λ B' V P Vθ βo ℓ) U:= by
 let S':=(S★); let v:=(βo); let Z:=finish Λ B' V P Vθ v ℓ; let Z':=trunk Λ B' V P Vθ v 0; let t'(i:ℝ):RG.Rep G _:= U; let c:=Fintype.card (Site (c!)); have hx' : Z.eval = S'.push U.beta U.eval:=by rw [hu]; exact he
 obtain ⟨H₁,H₂⟩:= F.machine.passes (Q:=t') hm (l:=Set.univ) (fun i hi=> ⟨hp,(show U.beta ∈ band (a) (m+1) from hu ▸ hx)⟩)
 obtain ⟨X,V',q',hb,ht,hV'⟩:=hn.rents; have hb': (V).threshold^2* |q|≤ Yz:=by rw [ht]; exact Averaging.delta_bound g0 hb.projects
 have hP:=H.gates Λ B' v ℓ; have he': Z.eval 1=Real.exp (ℓ*(c:ℝ)):= cardP Z hP.regular.at_flat
 have hf : ∀ W₁,Z'.eval W₁* Real.exp (∑' i,Vθ.logarithm i W₁)=(S'.push U.beta U.eval W₁)/(S'.push U.beta U.eval 1):=by
    intro W₁; rw [← hx', he', eq_div_iff (Real.exp_pos _).ne', mul_comm]; exact (H.exact_eval ..).symm
 have hδ : D₁=Time.quoteHard A.B.a m F.book U.beta:= (congr_arg (Time.quoteHard A.B.a m F.book) hu.symm)
 obtain ⟨hA,hB⟩:= H₁.closes x (Set.mem_univ _) Z.activities (show Z.activities.Valid V _ (Time.quoteHard (a) m F.book U.beta) from hδ ▸ hP); -- Coerce.D₀ uses.
 have heT:predictor A.B N t' x+q=v:=by change U.beta+ _ +_= _; rw [hu]
 have hy:= H₂ x (Set.mem_univ _) hp (show U.beta∈ _ from hu ▸ ‹x∈ band A.B.a (m+1)›) q P Vθ; dsimp only at hy; rw [heT] at hy; have hl :flatRate (a) m n U=ℓ:= by change Real.log (S'.push ..)/ (c:ℝ)= _; rw [← hx', he',Real.log_exp, mul_div_cancel_right₀ ℓ (by change (Fintype.card (Site (c!)):ℝ) ≠0; positivity)]
 obtain ⟨hx1,hx2⟩:= hy (show Ingredients P Vθ V D₀ (Time.quoteHard (a) m F.book U.beta) from hδ ▸ H) hb' hf
 have ht': flatRate (a) m n (t' x) = ℓ:= hl; rw [ht'] at hx1 hx2
 refine ⟨hx',hx2,⟨?_,rfl,rfl,⟨A.B.support.cap N m hm.le,hA⟩,hx1⟩,hB,?_⟩; · rw [A.B.bases]; rfl
 change |x+Γ+q-U.beta-Γ|≤1; rw [hu]; exact le_trans (le_of_eq (congr_arg abs (show x+Γ+q-x-Γ=q by ring))) hn.step
end Daze
end WheelP
end YM.AllOrder.Transit
