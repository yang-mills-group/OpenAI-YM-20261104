import YM.LocalTaylorR2.Marker.Book
import YM.LocalTaylorR2.License
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

def wage0 (θ ζ y K x' D ρ:ℝ)(l:ℕ) : ℝ := (B+prismCash x' D K r l j)*boosted M H N.conduit y (n+j) ((l+1:ℝ)*θ*ρ) ζ p.val
local notation "hP"=> period M H p N x' D K y θ (l:=l)
include h hζ hp hy hr hθ U
lemma wageN : 0≤ wage0 M H p N θ ζ y K x' D ρ l:=by
   have hZ:1≤ρB:= one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_left (Nat.cast_nonneg _)) hθ) hp
   have hQ:= hope M H N.conduit h hζ hZ hy p.val (n+j); have hv:= U.fuel; have hm:= U.sure; have hf:= hr.salt
   have hh:= (Z).active
   unfold wage0; exact mul_nonneg (add_nonneg N.balance (by unfold prismCash speedS; positivity)) hQ
include hI hs hq hh
lemma saving : (∑ i:Orders l, (hP) i *ρ^i.val) ≤ wage0 M H p N θ ζ y K x' D ρ l:=by
   by_cases he:treads M H p; swap; · simp_rw [period, lush,he,false_and,and_false,ite_false,zero_mul,sum_const_zero]; exact wageN M H p N U hr h hζ hp hy hθ
   let d := prismCash x' D K r l j
   have hd : 0≤d:=by unfold d prismCash speedS; have hm:= U.sure; have hf:= U.fuel; have hp:= hr.salt; have h:=N.conduit.active; positivity
   let g:=(1+H.shapeW p.val)^(n+j); have hg:0≤g:=by unfold g; have hx := H.positive_volume p.val; positivity
   let t:= boosted M H N.conduit y (n+j) (ρB) ζ p.val; let s:= entry (Z) (ρB) ζ; let z:= y*jewel M Q L x; let T:= partners M p.val
   have hz:0≤z:=mul_nonneg (zero_le_one.trans hy) (dew M H|>.1.le)
   have hZ:1≤ρB:= one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_left (Nat.cast_nonneg _)) hθ) hp
   have hQ:= hope M H N.conduit h hζ hZ hy p.val (n+j)
   have hU : t=(z*∏ i∈T, s i)*g:=by unfold t boosted; rw [if_pos ((H.attends _).2 he.1.1), ← mul_prod_erase _ _ he.2, show hook M H _ _ _ _ (i₀)=z from if_pos rfl]; exact congr_arg (fun v=> z*v*g) (prod_congr rfl fun _ h=> if_neg (ne_of_mem_erase h))
   unfold period; change _ ≤ (B+d)*t
   by_cases hx:Clear (partners M p.val); rw [add_mul]; swap -- handle const
   · simp_rw [if_neg (show ¬ lush M H p from fun h=> hx h.2)]; unfold Clear at hx; push Not at hx; obtain ⟨q,hj,hx⟩:=hx
     rw [sum_eq_single (perch l),if_pos ⟨rfl,he⟩]; rotate_left; · intro i _ hi; rw [if_neg (fun h=> hi h.1),zero_mul]
     · simp
     set a:= ∏ i∈T, (Z).fare i with ha
     have hD : persona M H C' (Z).flair 0 (n+j) 0 p.val=jewel M Q L x*a*g:= by
       unfold persona; rw [if_pos ⟨(H.attends _).2 he.1.1,he.2⟩,← mul_prod_erase _ _ he.2, nose]
       exact congr_arg (fun v=> jewel M Q L x*v*g) (prod_congr rfl fun _ hi=> sleeve M H _ _ _ (ne_of_mem_erase hi)) -- syntax bind inferred
     have hR: ρ^(l+1)*a≤∏ i∈T,s i:=by
       rw [ha,← mul_prod_erase T _ hj,← mul_prod_erase T s hj,← mul_assoc]; apply mul_le_mul ?_ (prod_le_prod (fun _ _=> (Z).fares _) (fun _ _=> cheap (Z) h hζ hZ _)) (prod_nonneg fun _ _=> (Z).fares _) ((Z).fares _|>.trans (cheap _ h hζ hZ _)); exact ((mul_le_mul_of_nonneg_right hq ((Z).fares _))).trans (polluter_cost (Z) h hZ p.val he.1.2 hh (Finset.mem_of_mem_erase hj) hx)
     refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hd) hQ); rw [hD,hU]
     change B*(y*(jewel M Q L x*a*g))*ρ^(l+1)≤ B*((z*_)*g)
     refine Eq.trans_le ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR hz) hg) N.balance); unfold z; ring
   simp_rw [if_pos (show lush M H p from ⟨he,hx⟩)]
   apply le_trans _ (le_add_of_nonneg_left (mul_nonneg N.balance hQ))
   refine (Candle.money (U:=T) (l:=l) (fun q=>toll M H p N q x' D K y θ) (fun i=> tollN M H p N hy i hθ hr (zero_le_one.trans U.sure) U.fuel) hp).trans ?_
   rw [hU]; apply le_trans _ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Tender.inflated _ hI h hζ hθ T (isPure hx) hp hs) hz) hg) hd)
   apply le_of_eq; rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]; exact sum_congr rfl fun q _=> by change z*forge _ θ q*d*g*_=_; ring

variable (hA:foam Q L) (hK:R.p.B≤2*radiusB x)
local notation "kw"=> (current Q L μ x + (ρB*c'+y*ribbon Q L x))
variable (hv:degreePrice (radiusB x) (current Q L μ x + (((l+1:ℝ)*θ*ρ)*c'+y*ribbon Q L x)) Q.δ ≤ 1/2)
omit hs hq hh
include hI hA hK hv
def qol (Q:YM.ConnectedActivityE6.Target G P)(L:Side)(l n j:ℕ) (μ x θ x' K r B y D ρ c':ℝ):ℝ := 2^j*((B+prismCash x' D K r l j)* (Reserves.extract Q.ε (n+j) 0 0 * Reserves.treeYield (current Q L μ x + (((l+1:ℝ)*θ*ρ)*c'+y*ribbon Q L x)) (1/2) 0))
lemma downPayment {u:ℝ} (hx:u ≤ Q.exp): Ac.Hit H.smallAt (radiusB x) (fun p'=>2^j * wage0 M H p' N θ ζ y K x' D ρ l) u (qol Q L l n j μ x θ x' K r B y D ρ c'):=by
   have hz:1≤ρB:= one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_left (Nat.cast_nonneg _)) hθ) hp
   have hd := desk M H (Z) h hζ hz hy hI hA hK hv (n+j)
   apply AnalyticBridge.VerifiedReset.Quotes.hit_scale (by positivity : 0 ≤ (2:ℝ)^j) -- edit
   have he:B+prismCash x' D K r l j≥0:= add_nonneg N.balance (by unfold prismCash speedS; have ht:= U.sure; have hp:= U.fuel; have hS:= (Z).active; have h:=hr.salt; positivity)
   have ht:= AnalyticBridge.VerifiedReset.Quotes.hit_scale he hd; intro i; have hq:= budget_pull (fun i:H.ThinP=> i.val) Subtype.val_injective (ht i); apply budget_mono hq ?_ ?_
   · intro p; split
     next=> exact mul_nonneg (wageN M H p N U hr h hζ hp hy hθ) (Real.exp_pos _).le
     exact le_rfl
   intro j; dsimp only; split
   next h₁=> rw [if_pos (show i∈H.unionP j.val from h₁)]
             exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg _))) (wageN M H j N U hr h hζ hp hy hθ)
   exact hq.1 j
end YM.LocalTaylorR2.Marker
