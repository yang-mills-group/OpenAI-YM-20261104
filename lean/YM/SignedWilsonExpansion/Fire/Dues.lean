import YM.SignedWilsonExpansion.Fire.Timer
import YM.SignedWilsonExpansion.Dancer.Sweet
import YM.SignedWilsonExpansion.Chron.Planners
/-!
# Set about duties for Candle. Knobs after reserve.High height affordable *not* used for physical receipts.
- Borrow V* meters after ext. Cost comparison p→ g.Core. burners.Coop.
-/
set_option autoImplicit false
set_option maxHeartbeats 630000
noncomputable section
namespace YM.SignedWilsonExpansion.Fire
open Function Filter Asymptotics Gauge Wilson RG Real Lattice
open Purchases UVClock Schedules Dancer Dancer.Supper WilsonCoeffUV WilsonCoeffUV.Bank PathCost
open Commission Purchases.HalfRoof.Cooking Purchases.HalfRoof Purchases.HalfRoof.Minty
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa MarqueQ Stair PorchK Source
open Pert.Asymptotics Integration.Exporter.Loans
open XSpace FVA2 MS MS.High MS.Land MS.Native MS.Tide MS.Fleet MS.Book
open WardBin
open scoped Classical BigOperators Topology
variable {G:Gauge} {ι κ: Type} {H:Levels G} {a b d n h u ξ q p K e V:ℕ}{U:Filter ι}{L:Filter κ}
variable {B r X A:ι→ℝ} {f y z c v N j l k:ι→ℕ} {s : κ→ι}
section

variable (w:G.Simple)(W:GentleS H)(g:Tendsto r U Trace.Pilot.trail) (Z:AgeRead a b ξ U H r (cck G ∘ r) f k v j B)
-- k reserved birthday. v capture. j older stop. horizon h & e modest. S issued
include w W g Z
lemma moves (hu:Tendsto s L U) : AgeRead a b ξ L H (r∘ s) (cck G∘r∘ s) (f∘s) (k∘s) (v∘s) (j∘s) (B ∘ s):=by
   obtain ⟨A,hA,p⟩:= Z.bought; exact ⟨hu.eventually Z.fast,hu.eventually Z.far,hu.eventually Z.owner, hu.eventually Z.sizeAt,hu.eventually Z.buried,⟨A,hA,hu.eventually p⟩, hu.eventually Z.stop_age,fun _=>( Z.grasp ( Z.capture w W ( radius_clock w g ) (g.eventually self_mem_nhdsWithin) (EventuallyEq.rfl))).comp_tendsto hu,hu.eventually Z.step⟩
end
variable (R:Realm G (e+1) Credit.leanC){F:Labels.Frames G}{Ω : Council F}{F':Initialize G}{Q:∀h,Rays G h F'.hol}
variable (Y:Normalize.Store G)(Kb: Rose.Pick Y){T:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{S':Prescription (Press.portDeck G)}(M:Speed.Quoted F' Kb T S')
variable (headV:6≤d)
/-- thermal feints. `a` room estimate, `b` physical steps. These are unrelated to wound aura `b0`. -/
def βNeed (a b:ℕ):ℕ:= a+b+2
def goalX (p V d A:ℕ):ℕ:= V*d*A+p+2
def needH (p V d a b:ℕ):ℕ:= max d ( goalX p V d (βNeed a b) )
def ℐ (E:ℕ):ℝ:= 1+4*(E:ℝ)+(E:ℝ)/MS.Tide.mildG
def demandΦ (p V d a b:ℕ):ℕ:= (2*V*d*(βNeed a b))+p+2
def target₀ (p V d a b:ℕ):ℕ:= max ( demandΦ p V d a b ) (4*(goalX p V d (βNeed a b))+2)
lemma indexP (w: G.Simple)(g:Axis) (hd:d≤ h) :∃ (u K:ℕ), Ample h u (h+e) ∧ u≤K ∧ h+e ≤ K ∧ (bankSize G F' Kb M w g h (headV.trans hd))*h ≤ u ∧ (bankSize G F' Kb M w g h (headV.trans hd))*h ≤ K ∧ V*h≤ u ∧ (goalX p V d (βNeed a b))*2 ≤ u:=by
     let x:= bankSize G F' Kb M w g h (headV.trans hd); let y:=x*h; let U:= V*h; let J:= (goalX p V d (βNeed a b))*2; let W:= h*h; let T:=h+e; let z:= h+1; let r:= h+z; let s:=z*T; let u:= max U (max y (max J (max W (max r s)))); let k:=max u T; refine ⟨u,k,⟨by omega,by change s≤ u;omega,by omega⟩, le_max_left ..,le_max_right ..,by change y≤u;omega,by change y≤k; have hv:y≤u:= (by omega); exact hv.trans (le_max_left ..),by omega,by omega⟩
lemma dutyP (w: Fin (n+1)→ℕ)(hd:∀i,w i≤ d)(hz:n+1≤V)(p':V*h≤u)(q: u≤K):
     Duty w p K u h h (goalX p V d (βNeed a b)) (demandΦ p V d a b) (βNeed a b):=by
     let x:= (Nat.mul_le_mul_right h hz).trans p'; refine ⟨x,x.trans q,⟨ V*d,(Finset.sum_le_sum (fun i _=> hd i)|>.trans ( b:=(∑ i:Fin (n+1),d) ) (?_)),?_,?_⟩ ⟩
     · -- finite the bound.Ty
       simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using Nat.mul_le_mul_right d hz -- simp both sides
     · unfold goalX; push_cast; nlinarith [ Nat.cast_nonneg (α:=ℝ) p]
     unfold demandΦ; push_cast; nlinarith
section
variable (w:G.Simple)(W:GentleS R.draws)(g:Tendsto r U Trace.Pilot.trail)(Z:AgeRead a b ξ U R.draws r (cck G ∘ r) f k v j B)
variable (pv:∀ i,0<r i)(s:Axis)
local notation "J" => R.draws
local notation "X₁" => cck G ∘ r
local notation "ξ₀"=> βNeed a b
local notation "Y₀"=> goalX p V d ξ₀
local notation "ℨ"=> demandΦ p V d a b
local notation "M₀"=> ℐ Y₀
local notation "ℓ₀"=> ell₁ J r X₁
local notation "m₀"=> m₁ J r X₁
local notation "C₁"=> corn J X₁ M₀ k
variable [U.NeBot](Pb:0<b)(ha:h=needH p V d a b)(ht:d≤h)(gp:(p:ℝ)/2<b)
variable (unit: u≤K)(tier:h+e≤K)(px: goalX p V d (βNeed a b)*2 ≤ u)(tu: (bankSize G F' Kb M w s h (headV.trans ht))*h ≤ u)(α:Ample h u (h+e))(b₁: target₀ p V d a b ≤ ξ)(he: demandΦ p V d a b ≤ e)
include Z g W M headV pv Pb ha ht gp unit tier px tu α b₁ he
lemma recruitment {st:ℕ}(Φ:Hol G) (p₁:∀i,(Ω i).Sound Φ)(p₂:∀i,Bid.pop (Ω i))(P:Install Φ (Master.mk F.level Ω p₁ p₂) R K)(hZ:R.y= Ticket.zz R.draws)(Y': Campfire ι G e R.draws R.paid F' st)(z:IsEquivalent U X ( needle G ∘ r )) :
    ∃ (ℜ Y₁:ι→ℝ) (ζ: ι→ PorchK F' F Q Ω R h h u), Club Y Kb R ζ U ℓ₀ m₀ f k C₁ j X₁ Y₁ r ℜ X pv p d ℨ K (ξ₀:ℝ) (Y₀:ℝ) M s:=by
    let E:ℝ:=Y₀; have hp:0 < mildG:=MS.Tide.mild_p; have hu:0<M₀:=by unfold ℐ; positivity
    have hz:= radius_clock w g; let t:= Z.camp w W hz ( g.eventually self_mem_nhdsWithin ) (EventuallyEq.rfl); obtain ⟨U₁,Y₁,ζ,B'⟩:= raving R p₁ p₂ P pv W hZ Y' unit tier (le_refl h) α Q t M₀ hu
    let v':= g.eventually ( Trace.Pilot.trail |> fun _=> self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Set.Ioi 0) ); let r':= EventuallyEq.rfl (f:=cck G∘r) (l:=U)
    have E':0<E:=by unfold E goalX; positivity
    refine ⟨U₁,Y₁,ζ,B',headV,ht, le_rfl,tier,unit,tu,tu.trans unit,he,?_,⟨( isEquivalent_iff_tendsto_one ((hz.eventually_gt_atTop 0).mono fun i hi=> (inv_pos.mpr (sqrt_pos.mpr hi)).ne')).mp z⟩,⟨ b,gp,Z.closes w W hz v' r' (by linarith)⟩,Z.lower w W hz v' r', (?_:0<(ξ₀:ℝ)),E'.le,?_,?_⟩
    · unfold demandΦ; omega
    · unfold βNeed; positivity
    · refine awakenG (e:=e) w W hz v' r' Z R (δ:=Y₀) rfl ?_ ?_ hu ?_ ?_
      · apply le_trans _ (show (h:ℝ) ≤ (h:ℝ) * b from le_mul_of_one_le_right (Nat.cast_nonneg _) (Nat.one_le_cast.mpr Pb) ) -- name
        exact_mod_cast (show Y₀ ≤ h from (le_max_right d Y₀).trans_eq ha.symm)
      · have he : (Y₀:ℝ)*2 ≤ u:=by exact_mod_cast px
        linarith only [he]
      · unfold ℐ; have hv:0≤ E/MS.Tide.mildG:=(by positivity); change 4 * E ≤ 1 + 4 * E + E/MS.Tide.mildG; linarith only [hv]
      have hv: (4*(Y₀:ℝ)+2) ≤ ξ:= by exact_mod_cast ( (le_max_right (ℨ) (4*Y₀+2)).trans b₁ )
      linarith only [hv]
    · apply peerP_chip (z:=M₀) pv hz (corn_size hz W w r' v' ( campUnity R pv W t ) hu); unfold ℐ; have hv:E=E/MS.Tide.mildG * MS.Tide.mildG:= ( div_mul_cancel₀ E hp.ne' ).symm; change E ≤ (1 + 4 * E+ E/MS.Tide.mildG) * _; nlinarith only [ hv,E',hp,mul_pos hp E' ]
end
end YM.SignedWilsonExpansion.Fire
