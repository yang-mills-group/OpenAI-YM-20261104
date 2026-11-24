import YM.RGComparison01.Marks.Archival
import YM.RGComparison01.Marks.Staircase
import YM.RGComparison01.Pencils
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
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
namespace Reels
open Foreman Checks Baked Palette Pillow Resin Season Ink Heron
open Switch Mallow Ovens OmitClusters Song Refrain Motion Next.Scheduling ConnectedActivityE6.Blaze.March
open Set Metric MeasureTheory Gauge Tensor WilsonStartup Input Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations.Sector Next.SectorChange Fare Sienna Token
open Push.Uniform Sienna PhysicalNext PhysicalNext.Repeat AuxJets AuxFabric AuxStage AuxSpell AuxWeigh Pencils
variable [Fintype ι]
variable (M:ι→Lotus.Leaf R)(g:ι→ℝ)(H:Cash W s μ L Q o C T R)
variable (P' P₀ :BudgetPoint) (O:ChartRatio G) (F:Forest S.ratio) (ρ: Bid.Dir G c→ AxisChart G F) (i:S.Choices)
variable (e:Config G f→ℝ)(E:Poll.Body (Precision.Key F G)→ℝ×Positions (Uniform.Primary c G)→ℝ)
variable (W': Finset ι→ Poll.Body (Precision.Key F G) → ℝ×Positions (Uniform.Primary c G)→ℝ)
    {m q q' p p' y x' D' n' : ℕ} {T₀ C₀ ψ β v' D D'' b u Q' J' X R' Y R₀ : ℝ}
local notation "Xp"=> Tickets (Palette.sign M S)
local notation "Pn"=> Pledge.Heron.bouquet M g H (χ:=χ)
local notation "Xs"=> Positions (Uniform.Primary c G)
set_option quotPrecheck false
local notation "g₀"=>gStep β
open Staircase
lemma continuous (G:Gauge)(c: Side): Continuous (fun x:Positions (Uniform.Primary c G)=> Boulevard.actual x) := continuous_pi (fun i=> ((show Continuous (fun x:Bid.Dir G c=> represent x i) from (by unfold represent increment Exterior.collect; simp only [Pi.one_apply,mul_one]; exact G.lieExp_cont.comp (continuous_apply _)))).comp (ContinuousLinearEquiv.continuous _))
abbrev allotV (p : Finset ι)(V:Config G c) := Switch.jet (Heron.bouquet M g H V (χ:=χ)) p

def publisher (T:Tube G S) (q q' n:ℕ) :=fun t=> AuxBeam.markCo O T F ρ i E (W' t) q q' n
local notation "Z"=> publisher O F ρ i E W' T q q' n
variable (z: Positions (Uniform.Primary c G))
variable (hp:Staircase.grows M) (hx:Staircase.TrueSector M g (S:=S) (Heron.bouquet M g H (χ:=χ)) P')
     (hX : Pencils.Mate T P₀ R e β) (hT: ∀ V,∃ v, Paid (fun _:Unit=> Heron.bouquet M g H V (χ:=χ)) v)
     (hV: AuxSpell.Tower O T F i ρ P₀ β e E n k j q q' y T₀ C₀ X D'' b d⁻¹ R' Y R₀ z) -- z specify prior
variable (hF : ∀ p:Finset ι,p≠∅ → Probe (W' p) k y q' R' D'' b b ∧ AuxPackage.Render F ρ P₀ β (cardTest M g S p) (W' p) q' R' D'' Y)
variable (hm:Fintype.card ι ≤ m) (p:Finset ι)
include hp hX hx hT hV hF H hm
lemma premier (hh : 0 ≤ gStep β)(h : gStep β≤1) (hd:0≤ d) (hz : Boulevard.actual z∈ Boulevard.sunny P') : AuxStage.Points (Archival.fee n j m |X| m) d⁻¹ g₀ n j (allotV M g H (χ:=χ) p ∘ Boulevard.actual) z (Archival.imageSet Z m m p):= by
   let J x:= Staircase.projection M g (S:=S) (Boulevard.actual x); let W:=Heron.bouquet M g H (χ:=χ)
   have he t (hp : t≠∅) (x:Xs): J x t = AuxBeam.read_J T P₀ β e (cardTest M g S t) x:=by
      unfold J Staircase.projection AuxBeam.read_J
      simp only [AuxBeam.weighLess,AuxWeigh.weighed,Pi.div_apply,hX.1,hX.2]; unfold AuxPackage.gross; rw [mul_one,mul_assoc]
   refine (Archival.source (F:=J) (inv_nonneg.mpr hd) hh h hm (abs_nonneg X) (fun t ht=> ?_) m p).adjust ?_
   · simp_rw [he t ht]; exact ((hV.marked _ (W' t) (hF t ht).1 (hF t ht).2).2.funding (le_abs_self X) hh le_rfl)
   filter_upwards [(Reels.continuous G c).continuousAt.preimage_mem_nhds ((Boulevard.sky P').mem_nhds hz)] with x hxx
   have ha:= hx.active _ (Boulevard.smoky (show Boulevard.actual x∈ Boulevard.sunny P' from hxx))
   exact press M g H hp (Pn) m hm _ ha.1 ha.2 (by simp only [Heron.bouquet,Ink.blanker,tsum_zero]) ((hT _).choose_spec) p
omit hp hX hx hT hV hF H hm
open Spline
omit [Fintype ι] in
lemma pollen (q q' n:ℕ)(p:Finset ι) : Spline.Field (n+(q'+q*n)+(n+(0+q*n))*n) n (publisher O F ρ i E W' T q q' n p) := (Spline.Field.Laced (Lapis.gram F T.up T.high ρ i 0)⁻¹ (AuxMiles.shot O F T ρ i) E _ n q q').weave ((Spline.Field.Laced (Lapis.gram F T.up T.high ρ i 0)⁻¹ (AuxMiles.shot O F T ρ i) E _ n q 0).pacify _ _ n)

/-- Lease certificate for any proposal. Cost authenticated only by
 earned Co at origin. Real output tape shape must be supplied; it
 is not defined by this check. ROOT offer includes all Hub-coordinates before projection onto tasks. -/
structure Posed (P:BudgetPoint)(V:Config G c→ℝ)(f:ℝ × Positions (Uniform.Primary c G) → ℝ)(β:ℝ)(w k : ℕ) (r v : ℝ) : Prop where
  price (y:ℝ × Positions (Uniform.Primary c G)) (hy:y∈ Metric.ball 0 r): Brush k v 1 f y
  flat : FlatAt w f 0
  active (y:Positions (Uniform.Primary c G))(hy : ‖y‖ <r)(he:Boulevard.actual y∈Boulevard.sunny P): V (Boulevard.actual y)= (gStep β)⁻¹^w*f (gStep β,y)
lemma stated (P:BudgetPoint)(V:Config G c→ℝ)(f:ℝ × Positions (Uniform.Primary c G) → ℝ)(z:Positions (Uniform.Primary c G))
    (hV:Posed P V f β p' k (d*gStep β) v)(hj:j≤k)(hp:n+p'<k) (hd:1<d) (h₀:0<gStep β)(hv:d*gStep β ≤ 1)(hx:‖z‖< d*gStep β)(he:Boulevard.actual z∈Boulevard.sunny P): AuxStage.Points (ritual_fee p' n v 0 d) (d*g₀)⁻¹ g₀ n j (V ∘ Boulevard.actual) z (ritual f p'):=by
   have hz:= hV.price 0 (mem_ball_self (mul_pos (zero_lt_one.trans hd) h₀))
   apply (ritual_P hp hj (hz.smaller hp.le).smooth hV.flat h₀ hd hv hx hV.price (u:=0) (by rw [sub_self,zero_mul]; exact AuxCurtain.constant (u:=0) zero_le_one norm_zero.le)).adjust
   refine Eventually.mono (inter_mem ((Reels.continuous G c).continuousAt.preimage_mem_nhds ((Boulevard.sky P).mem_nhds he)) (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hx))) (fun y he=> hV.active _ (mem_ball_zero_iff.mp he.2) he.1)

variable (f':ℝ × Positions (Uniform.Primary c G) → ℝ) (V:Config G c→ℝ)
def régisseur (m n q q' p':ℕ) (p:Finset ι):= Archival.imageSet (publisher O F ρ i E W' T q q' n) m m p + (-1:ℝ) • ritual f' p'
local notation "EP"=> Reels.régisseur O F ρ i E W' f' (T:=T) m n q q' p' p -- syntax
abbrev bunk (m n q q' p':ℕ):= Archival.waf m (n+(q'+q*n)+(n+(0+q*n))*n) m+(n+p')
local notation "S'"=>bunk m n q q' p'
def Transfer (T:Tube G S)(p:Finset ι) (m n q q' p':ℕ)(β d u:ℝ) := let Zt:= Reels.régisseur (T:=T) O F ρ i E W' f' m n q q' p' p; let k:= bunk m n q q' p'; ∀ j ≤ n, ∀ i≤ k, normJ i (headAt Zt (gStep β) j) 0 * (d*gStep β)^i ≤ u*gStep β^(n+1)

def tab (n j m q q' p':ℕ) (X v d u:ℝ):=let k:=bunk m n q q' p'; let r:=ritual_fee p' n v 0 d; Archival.fee n j m |X| m + r+(n+1:ℕ)*(k+1:ℕ)*u
local notation "t'"=>tab n j m q q' p' X v d u
include hX hx hT hF hm H hp
lemma author (ht:AuxSpell.Tower O T F i ρ P₀ β e E n k j q q' y T₀ C₀ X D'' b (d*gStep β)⁻¹ R' Y R₀ z)
   (hh:0<gStep β) (hj:j≤k) (hi:n+p'<k) (hd:1<d) (h₀:d*gStep β ≤ 1) (hz:‖z‖ < d*gStep β) (he:Boulevard.actual z∈ Boulevard.sunny P')
   (hG:Posed P' V f' β p' k (d*gStep β) v) (hM:Transfer O F ρ i E W' f' T p m n q q' p' β d u) : Brush j ((t') * gStep β^(n+1)) (d*gStep β)⁻¹ ((allotV M g H (χ:=χ) p - V) ∘ Boulevard.actual) z:= by
   let r:=d*g₀; let c':=bunk m n q q' p'
   have hh' := (stated P' V f' z hG hj hi hd hh h₀ hz he).scale (-1); rw [norm_neg,norm_one,one_mul] at hh'
   have hV:=premier M g H P' P₀ O F ρ i _ _ W' _ hp hx hX hT ht hF hm p hh.le ((le_mul_of_one_le_left hh.le hd.le).trans h₀) (hh'.pos |> inv_nonneg.mp) he
   let F':= (allotV M g H (χ:=χ) p - V) ∘ Boulevard.actual; let f'':= Reels.régisseur (T:=T) O F ρ i E W' f' m n q q' p' p
   have hx:F'= (allotV M g H (χ:=χ) p ∘ Boulevard.actual)+(fun i=> (-1:ℝ)*(V ∘ Boulevard.actual) i):= by ext i; simp only [F',Function.comp_apply,Pi.add_apply,Pi.sub_apply]; ring
   have hf := (hV.add hh').adjust (g:=F') (Filter.EventuallyEq.of_eq hx)
   have hs : Spline.Field c' n f'':= Spline.Field.add ((Archival.artist (M:=publisher O F ρ i E W' T q q' n) (pollen O F ρ i E W' _ _ _) m m p)|>.weaken (Nat.le_add_right _ _)) (Field.smul (Field.weaken (Field.ritualP _ _ _) (Nat.le_add_left _ _)) _)
   let e':ℝ:=(c'+1:ℕ)*(u*g₀^(n+1))
   have he b₀ (hz' : b₀ ≤ n) : Brush j e' r⁻¹ (headAt f'' g₀ b₀) z := by
       let L := g₀⁻¹ • ContinuousLinearMap.id ℝ Xs
       exact Spline.all_taxes (Spline.smul ((hs b₀ hz').through L) (g₀^b₀)) r hz h₀ (hM b₀ hz')
   have hx := Brush.spree (Finset.range (n+1)) (headAt f'' g₀) (fun _=> e') hf.pos (fun i hi=> he i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
   rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hx
   apply (hf.tail.gathering hx).climb (le_of_eq ?_) le_rfl|>.shimmy _
   · unfold tab e' c'; dsimp only; ring
   exact Eventually.of_forall fun x:Xs=> (sub_add_cancel (F' x) (AuxStage.price f'' g₀ n x)).symm
end Reels
end YM.RGComparison01.Pledge
