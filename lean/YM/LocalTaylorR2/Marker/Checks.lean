import YM.LocalTaylorR2.Marker.Doctor
import YM.LocalTaylorR2.License
import YM.LocalTaylorR2.Scaling
/-!
 # Price single Mark: post-K
 Uses from Daisy.Clutch.central. Signs untouched, inventory projected only once.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Marker
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Art Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes Census Itinerary
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Leaf R) (X:Coat T F) (H:Cash W x μ L Q o C T R)
    {Z : Support c} {k k':Finset ℕ}{u v : Air f G}

local notation "i₀" => M.turn.badge S
open Port Charge
open Reserves Tender Gas Ursell Trees Mixed
variable {j k n l : ℕ} {v₀ r d A D x' C' ζ η c' y: ℝ} {χ : Chi} (Ξ:Utopia H j v₀ d r C' χ)
open Candle Daisy.Charity
open scoped Classical
variable {k l:ℕ} (p:H.ThinP)
variable {b D K B v r w q' θ c' ρ ζ : ℝ} (N:Captain H j C' d v w A b r B q' (n+j) χ) (U:StoresR2 H j v d A D k x' n χ)(hr:Tinted G x K d o.a L χ j)
set_option quotPrecheck false
local notation "Z"=>N.conduit
local notation "d0"=> jewelDebt M Q L x
local notation "ρB"=> (l+1:ℝ)*θ*ρ
variable (h : 1≤betaF G x L) (hζ:0≤ζ) (hp:1≤ρ) (hy:1≤y) (hI:LocalBookingsR2 ζ c' N.conduit) (hθ:1≤θ)(ht:Charge.Allows l j θ)
    (hs:ρ*c'≤1) (hq: ρ^(l+1) ≤ betaF G x L^ζ) (hh:betaF G x L^ζ ≤ Real.exp (Q.mark L μ x))

variable (hA:Herd H N.conduit A B (n+j)) (hd:foam Q L)(hv:R.p.B ≤2*radiusB x)
variable (he:degreePrice (radiusB x) (massb Q L μ x θ ρ l c') Q.δ≤1/2)
    (hm:degreePrice (radiusB x) (current Q L μ x + (((l+1:ℝ)*θ*ρ)*c'+y*ribbon Q L x)) Q.δ ≤ 1/2)

local notation "Ncost"=> Price.result N θ ζ ρ D x' l
local notation "D'!" =>fun i=> Marker.wage0 M H i N θ ζ y K x' D ρ l
local notation "Zcut"=> Ncost+(D'!)
local notation "Yy" => refund M Q L x y

include N U hr h hζ hp hy hI hθ ht hs hq hh hA
lemma papers : Mind H M χ l v j (Price.schemePrice N D x' θ) (fun p => period M H p N x' D K y θ) (Zcut) ρ (Yy):=by
   let h:=Price.credentials N hI U h hζ hp hθ hs hq hh ht -- h.shadow below
   refine ⟨{h with bounds:= fun i=> ?_}, fun i q=> ⟨ letterSafe M H i N hA q, periodN M H i N hy _ hθ hr (zero_le_one.trans U.sure) U.fuel, fun V hV=> ?_⟩,fun i=>?_, div_nonneg (dew M H|>.2.1) (zero_le_one.trans hy)⟩
   · exact (h.bounds i).trans (le_add_of_nonneg_right (wageN M H i N U hr (by assumption) hζ hp hy hθ))
   · exact sustainsO M H i N U hr (by assumption) hζ hp hy hI hA hθ ht hs q V hV
   exact (saving M H i N U hr (by assumption) hζ hp hy hI hθ hs hq hh).trans
      (le_add_of_nonneg_left (Price.tall N U (by assumption) hζ hp hθ i))

abbrev teacher (Q: YM.ConnectedActivityE6.Target G P)(L:Side)(l n j:ℕ) (μ x θ x' K r B y D ρ c':ℝ):ℝ :=
    2*(Price.secondQ Q L μ x θ ρ D x' B r c' l n j + qol Q L l n j μ x θ x' K r B y D ρ c')
omit ht hs hq hh hA
include hm he hd hv
lemma authorizes {w' e a:ℝ} (hz : teacher Q L l n j μ x θ x' K r B y D ρ c' ≤ w')(hδ:0<e)(hw:0<w') (hu:a+e+e≤ Q.exp)
    (hF:degreePrice (radiusB x) w' e≤1/2) : Ready H.smallAt (radiusB x) (fun i=>2*(2^j*(Zcut) i)) (a+e) w' e (1/2):=by
   let X:= fun i=>2*(2^j*(Zcut) i); let v i:= 2^j*Ncost i; let w i:= 2^j*(D'!) i -- Ncost i syntax?
   have hx : Ac.Hit H.smallAt (radiusB x) v (a+e+e) (Price.secondQ Q L μ x θ ρ D x' B r c' l n j):= Price.funds N hI U h hζ hp hθ he hu
   have hQ:= downPayment M H N U hr h hζ hp hy hI hθ hd hv hm hu
   have hn i:X i≥0:=mul_nonneg zero_le_two (mul_nonneg (by positivity) (add_nonneg (Price.tall N U h hζ hp hθ _) (wageN M H i N U hr h hζ hp hy hθ)))
   refine ⟨hw,hδ,hF,(by norm_num),hn,?_⟩
   intro i; apply budget_loosen _ hz; have he:= budget_scale (show (0:ℝ)≤2 by norm_num) (budget_plus (hx i) (hQ i))
   convert he using 1; funext j'; split_ifs
   · unfold v; simp only [Pi.add_apply]; ring
   simp
end YM.LocalTaylorR2.Marker
