import YM.MS.Tide.Rank
/-!
# Estimate theorem: genuine UV and inversion quotient IR REMOVAL for perturbative QFT on Wilson adjacency vs κMS. Sets of fields use Deck & LitBook.
 This step still does not refer to t-scheme of manuscript. It gives the independent matching,
 with coupled choice of lattice knobs. Ward and evanescent policies described in sources.
 We will distinguish position spectra and actual frames subsequently.

 Physical geometry parameter θ is log(1/a) in physical units; exposed hypotheses are purely geometric: equivalent to super-poly periods with indicated margins and all positions in bounded subsets of shape. μ below = log ν.
 Even n set by dimT ( i↦ two*L i ); margins use hp.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Tide
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Lattice Land Frame Latch Job Heat Detect Book Convolve Program
open Native Wilsonian High Wind Rake Rake.Geo Vista Vane Port City Orbit Cog Orbit.LogReal
open Puff Engine SplitP Actors Dynamics Puff.Mom
open Fleet Swirl Swirl.Near SpaceOut Menus Echo
open scoped Topology ContDiff Interval
variable {W I:Type}{P:Geo I}{V:Visa I}{L:I→Side}{x: Faces I}{G:Gauge}{b:Bool} [LinearOrder W]
    {B:Local.Physical.Deck G}{M:Land.Booked B}{F:Finset W}{φ: LitBook B}{A: Land.Prescription B}{S: MS_Data G M}{n:ℕ}{μ:ℝ}
    (u:W→Label B)(c:Berth ( W:=W ) ( I:=I )) {l: Filter I}
    {X:Rake.Dance G I W}{Z:Terrify W I}
set_option quotPrecheck false
local notation "Yr"=> ApplyM φ A.team A u
local notation "Ur"=> ApplyM φ ( Stripped A.team ) A u
local notation "g"=> (Label.h ∘ u)
open PeakT (ordZ)
-- hypotheses.No bank, specify origin-bounded positions; any cardinal W.
abbrev Profile (P:Geo I)(c:Berth ( W:=W ) ( I:=I )): Prop:= ∀ w, ∃ r:ℝ,0<r∧∀ i,‖ Tone.embed ( c w i )‖≤ r*exp ( P.θ i )
variable (h:Profile P c) (hx:∀ i, P.η i=μ-P.θ i)
   (hu:Tendsto P.θ l atTop)(hp: Super l L P.θ)
include h hx hu hp
lemma qualifies : ∃ V:Visa I, WidthW V P.η c∧ NearPlan l P V L μ:= by
    let B(i:I):= exp (P.θ i)*(1+|μ|); let V': Visa I:=⟨ B,fun i=>one_le_mul_of_one_le_of_one_le ( Real.one_le_exp ( P.room i ) ) (by simp) ⟩; have hv(i:I):exp (P.θ i)≤B i:= le_mul_of_one_le_right (exp_pos _|>.le) (by simp)
    refine ⟨ V',⟨ fun i=> ?_,fun w=>?_⟩,⟨ hu,hp,hx,2,?_⟩⟩; · rw [hx]; change 1+|μ-P.θ i|≤B i; obtain ht:= Real.add_one_le_exp ( P.θ i ); obtain hb:=abs_sub μ ( P.θ i ); rw [abs_of_nonneg ( P.room _ )] at hb; unfold B; nlinarith [abs_nonneg μ,Real.one_le_exp ( P.room i )]
    · obtain ⟨a,ha,hA⟩:= h w; refine ⟨ a,ha,1,fun i=>?_⟩; rw [Pi.one_apply,pow_one,mul_one]; exact (hA i).trans ( mul_le_mul_of_nonneg_left (hv i) ha.le )
    have H:∀ᶠ i in l,1+|μ|≤ exp ( P.θ i ):=( tendsto_exp_atTop.comp hu ).eventually ( eventually_ge_atTop .. ); filter_upwards [H] with i hi; change B i≤exp _; rw [two_mul, exp_add ]; unfold B; gcongr
-- The scalePhysics data range over the full label and position families.
structure scalePhysics (P:Geo I)(M:Land.Booked B)(S:MS_Data G M)(μ:ℝ)(T':Land.Prescription B)(V:LitBook B)(u:W→Label B)(c:Berth ( W:=W ) ( I:=I ))(x: Faces I)(L:I→Side)(b:Bool)(l:Filter I) (Z:Terrify W I)(Y:Rake.Dance G I W): Prop where
     native : ∀ i s,PhysicalSum G T'.team ( P.η i ) (dimT L i) b s ( fun w=> c w i ) ( x i ) ( ApplyM V ( Stripped T'.team ) T' u ) (bury i s Z)
     empty : Z ∅=0
     scheme : DOrd M ( frameF I μ ) S u ( lifted P c ) Y
     huge : ∀ s:Finset W,s.Nonempty→∀ n,Verdict (frameF I μ) ( Vane.charge (Label.h ∘ u) s ) 0 ( Y s n ) -- `Verdict.economic` etc
     compares : ∀ s n, PeakT.twin l P mildG (fare ( Label.h ∘ u ) P Z s n) ( Fleet.toZ Y s n ) ∧ PeakT.twin l P mildG ( fare ( Label.h ∘ u ) P (ordZ Z) s n ) ( ordZ ( Fleet.toZ Y ) s n )
-- norm.
variable (hG:G.Simple) (hc:Clearance L x)(hw:Vista.width L x)(hm:Mesh P ( info c ))
include hG hc hw hm
lemma called (hZ:TaylorOK S φ A)(b:Bool): ∃ Z Y,scalePhysics P M S μ A φ u c x L b l Z Y:= by
    obtain ⟨V,hV,hV'⟩:= qualifies c h hx hu hp; obtain ⟨Z,Y,⟨hn,hU,hN⟩,hz,ht,hQ⟩:= CCP u c hG hZ hc hw hV hm hV' b
    refine ⟨Z,Y,hN,hn,hz,hQ, fun s n=>⟨(ht s n).symm,?_⟩⟩; rw [← funext (fun i=> PeakT.ν_norm g ( s:=s ) ( P:=P ) ( n:=n ) i Z) ]; exact PeakT.projection ht s n
omit hG hc hw hm h hx hu hp
-- one S.G.witness applies to every.
theorem remove (ϕ:LitBook B)(S:MS_Data G M)(h:G.Simple) : ∃ A:Land.Prescription B, TaylorOK S ϕ A ∧ ∀ (I W:Type)(_ :LinearOrder W) (P:Geo I) (L:I→Side)(x:Faces I)(b:Bool)(l:Filter I) (v:W→Label B)(c:Berth ( W:=W ) ( I:=I ))(μ:ℝ), Profile P c→ (∀ i,P.η i=μ-P.θ i)→ Tendsto P.θ l atTop→ Super l L P.θ→ Clearance L x→Vista.width L x→Mesh P ( info c )→ ∃ Z Y,scalePhysics P M S μ A ϕ v c x L b l Z Y := by
    obtain ⟨A,hA⟩:= High_stops h S ϕ; refine ⟨ A,hA,fun I W _ P L x b l v c μ hK hS hp hF hN hY hm=>?_⟩; exact called v c hK hS hp hF h hN hY hm hA b
-- note ∀ (_:LinearOrder W) parenthesized instance not applied? Lean auto-chooses? adjust
end YM.MS.Tide
