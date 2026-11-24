import YM.Integration.WilsonPhysicalExteriorResolvedFleet
import YM.FVAAlt2.Plus.Dial

/-! Finite-regulator counterterms against arbitrary separated moving marks:
only a polynomial bound on the actual unwrapped lattice addresses is required. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorResolvedCutoff
open YM.MS Tide WilsonPhysicalExteriorUVStory
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Lattice Land Frame Latch Job Heat Detect Book Convolve Program
open Native Wilsonian Paint High Wind Rake Rake.Geo Vista Vane City Orbit Cog Orbit.LogReal
open Puff Engine SplitP Actors Dynamics Puff.Mom
open Fleet Swirl Swirl.Near SpaceOut Menus Echo
open scoped Topology ContDiff Interval
open Book.Convolve Rake.Geo
section
variable {I W : Type} {P:Geo I} {l:Filter I} {L:I→Side} {μ:ℝ}
def Reach (P:Geo I) (c:Berth (W:=W) (I:=I)) : Prop :=
  ∀ w,∃ A:ℝ,0<A ∧ ∃ d:ℕ,∀ i, ‖Tone.embed (c w i)‖≤A*(exp (P.θ i))^d

theorem sparse (c:Berth (W:=W) (I:=I)) (hx:Resolved P (Fleet.info c))
    (hθ:Tendsto P.θ l atTop) : Echo.Sparse l c := by
  intro v w h
  obtain ⟨C,hC,hx⟩:=hx v w h
  refine tendsto_atTop_mono ?_ ((tendsto_exp_atTop.comp hθ).const_mul_atTop (inv_pos.mpr hC))
  intro i
  have hb : C⁻¹*P.roots i≤‖Fleet.info c v i-Fleet.info c w i‖ := by
    calc C⁻¹*P.roots i ≤ C⁻¹*(C*‖Fleet.info c v i-Fleet.info c w i‖) :=
          mul_le_mul_of_nonneg_left (hx i) (inv_nonneg.mpr hC.le)
      _ = _ := by rw [←mul_assoc,inv_mul_cancel₀ hC.ne',one_mul]
  apply hb.trans_eq
  simp only [Pi.sub_apply,emb_sub];rfl

theorem presented (c:Berth (W:=W) (I:=I)) (hx:Resolved P (Fleet.info c)) :
    Resolved (frameF I μ) (lifted P c) := by
  intro v w h
  obtain ⟨C,hC,hx⟩:=hx v w h
  refine ⟨C,hC,fun i=>?_⟩
  have hq : (frameF I μ).roots i=exp (-(P.θ i))*P.roots i := by
    simp [roots,←exp_add]
  rw [hq]
  change _ ≤ C*‖exp (-(P.θ i)) • Fleet.info c v i-exp (-(P.θ i)) • Fleet.info c w i‖
  rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (exp_pos _)]
  exact (mul_le_mul_of_nonneg_left (hx i) (exp_pos _).le).trans_eq (by ring)

theorem qualify (c:Berth (W:=W) (I:=I)) (h:Reach P c) (hx:∀i,P.η i=μ-P.θ i)
    (hu:Tendsto P.θ l atTop)(hp:Super l L P.θ) : ∃ V:Visa I, WidthW V P.η c∧ NearPlan l P V L μ:= by
    let B(i:I):= exp (P.θ i)*(1+|μ|); let V': Visa I:=⟨ B,fun i=>one_le_mul_of_one_le_of_one_le ( Real.one_le_exp ( P.room i ) ) (by simp) ⟩; have hv(i:I):exp (P.θ i)≤B i:= le_mul_of_one_le_right (exp_pos _|>.le) (by simp)
    refine ⟨ V',⟨ fun i=> ?_,fun w=>?_⟩,⟨ hu,hp,hx,2,?_⟩⟩; · rw [hx]; change 1+|μ-P.θ i|≤B i; obtain ht:= Real.add_one_le_exp ( P.θ i ); obtain hb:=abs_sub μ ( P.θ i ); rw [abs_of_nonneg ( P.room _ )] at hb; unfold B; nlinarith [abs_nonneg μ,Real.one_le_exp ( P.room i )]
    · obtain ⟨a,ha,n,hA⟩:= h w; refine ⟨ a,ha,n,fun i=>?_⟩; rw [Pi.one_apply,mul_one]; exact (hA i).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (exp_pos _).le (hv i) n) ha.le)
    have H:∀ᶠ i in l,1+|μ|≤ exp ( P.θ i ):=( tendsto_exp_atTop.comp hu ).eventually ( eventually_ge_atTop .. ); filter_upwards [H] with i hi; change B i≤exp _; rw [two_mul, exp_add ]; unfold B; gcongr
end

section
variable {I W:Type}{P:Geo I}{V:Visa I}{L:I→Side}{x: Faces I}{G:Gauge}{b:Bool} [LinearOrder W]
    {B:Local.Physical.Deck G}{M:Land.Booked B}{F:Finset W}{φ: RichBook B}{A: Land.Prescription B}{S: MS_Data G M}{n:ℕ}{μ:ℝ}
    (u:W→Label B)(c:Berth ( W:=W ) ( I:=I )) {l: Filter I}
    {X:Rake.Dance G I W}{Z:Terrify W I} {w:W→ℕ}
set_option quotPrecheck false
local notation "Yr"=> ApplyMPl φ A.team A u
local notation "Ur"=> ApplyMPl φ ( Stripped A.team ) A u
local notation "Qa"=> goalsK c P.η Yr
-- P.roots= spacing^{-1}.
local notation "Cgx"=> lifted P c
local notation "g"=> (Label.h ∘ u)
variable (h:G.Simple)(hp:TaylorOKPl S φ A)(he: Clearance L x)(hv: Vista.width L x)(hw: WidthW V P.η c)(hm: Resolved P ( info c ))(hP: NearPlan l P V L μ)
include h hp he hv hw hm hP
theorem connected (b:Bool): ∃ (Z:Terrify W I)(X:Rake.Dance G I W), ( Z ∅=0 ∧ Fleet.toZ X ∅=0 ∧ ∀ i s,PhysicalSum G A.team (P.η i) (dimT L i) b s (fun w=>c w i) ( x i ) Ur (bury i s Z)) ∧ DOrd M (frameF I μ) S u Cgx X ∧ (∀ s n,PeakT l P mildG (fare g P Z s n-toZ X s n)∧PeakT l P 0 ( Fleet.toZ X s n ))∧∀ s:Finset W,s.Nonempty→∀ n,Verdict (frameF I μ) ( Vane.charge g s ) 0 ( X s n ) := by
   have hs:= sparse c hm hP.vanish; obtain ⟨Ω,X,hQ,hX,hD,hK,hY⟩:= WilsonPhysicalExteriorResolvedFleet.assembly u c h he hv hw hm hs b hp; obtain ⟨Z,Y,H,hJ,hV⟩:= WilsonPhysicalExteriorResolvedFleet.covers φ S A u (frameF I μ) h (presented c hm) hp; refine ⟨ Ω,Y,⟨ hK.blanks.1,zeroZ hJ.1,hX ⟩,hJ, fun s n=>?_, fun s hs n=> hV s hs n |>.2.1 ⟩; obtain hh : fare g P ( toZ X )=toZ Y:= clockShape P Cgx u hP.dimm hJ ( by rw [ ← re_n ]; exact hD ) (fun s hs n=> hV s hs n|>.2.1.1 )
   refine ⟨ hh ▸ dealP c hK hP,?_ ⟩; by_cases hs:s.Nonempty; exact Verdict.economic _ _ (hV s hs n|>.2.1.2.2); rw [Finset.not_nonempty_iff_eq_empty.mp hs, zeroZ hJ.1]; exact PeakT.zero -- orientation ▸ may motive
end

section
open scoped Topology ContDiff Interval
variable {W I:Type}{P:Geo I}{V:Visa I}{L:I→Side}{x: Faces I}{G:Gauge}{b:Bool} [LinearOrder W]
    {B:Local.Physical.Deck G}{M:Land.Booked B}{F:Finset W}{φ: RichBook B}{A: Land.Prescription B}{S: MS_Data G M}{n:ℕ}{μ:ℝ}
    (u:W→Label B)(c:Berth ( W:=W ) ( I:=I )) {l: Filter I}
    {X:Rake.Dance G I W}{Z:Terrify W I}
set_option quotPrecheck false
local notation "Yr"=> ApplyMPl φ A.team A u
local notation "Ur"=> ApplyMPl φ ( Stripped A.team ) A u
local notation "g"=> (Label.h ∘ u)
open PeakT (ordZ)
-- hypotheses.No bank, specify origin-bounded positions; any cardinal W.
variable (h:Reach P c) (hx:∀ i, P.η i=μ-P.θ i)
   (hu:Tendsto P.θ l atTop)(hp: Super l L P.θ)
variable (hG:G.Simple) (hc:Clearance L x)(hw:Vista.width L x)(hm:Resolved P ( info c ))
include hG hc hw hm h hx hu hp
theorem physical (hZ:TaylorOKPl S φ A)(b:Bool): ∃ Z Y,scalePhysicsPl P M S μ A φ u c x L b l Z Y:= by
    obtain ⟨V,hV,hV'⟩:= qualify c h hx hu hp; obtain ⟨Z,Y,⟨hn,hU,hN⟩,hz,ht,hQ⟩:= connected u c hG hZ hc hw hV hm hV' b
    refine ⟨Z,Y,hN,hn,hz,hQ, fun s n=>⟨(ht s n).symm,?_⟩⟩; rw [← funext (fun i=> PeakT.ν_norm g ( s:=s ) ( P:=P ) ( n:=n ) i Z) ]; exact PeakT.projection ht s n
omit hG hc hw hm h hx hu hp
end

end YM.Integration.WilsonPhysicalExteriorResolvedCutoff
