import YM.MS.Tide.Cost
/-!
# Ambient geometric.Log parameter clock to installed MS scheme at physical scale.
Includes natural P.bill.*. μ variable here is log ν in chosen physical units.
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
variable {I W:Type}{P:Geo I}{V:Visa I}{L:I→Side}{x: Faces I}{G:Gauge}{b:Bool} [LinearOrder W]
    {B:Local.Physical.Deck G}{M:Land.Booked B}{F:Finset W}{φ: LitBook B}{A: Land.Prescription B}{S: MS_Data G M}{n:ℕ}{μ:ℝ}
    (u:W→Label B)(c:Berth ( W:=W ) ( I:=I )) {l: Filter I}
    {X:Rake.Dance G I W}{Z:Terrify W I} {w:W→ℕ}
set_option quotPrecheck false
local notation "Yr"=> ApplyM φ A.team A u
local notation "Ur"=> ApplyM φ ( Stripped A.team ) A u
local notation "Qa"=> goalsK c P.η Yr
-- P.roots= spacing^{-1}.
abbrev frameF (I:Type)(μ:ℝ): Geo I := ⟨ 0,(fun _=>μ),fun _=>le_rfl ⟩
def lifted (P:Geo I)(c:Berth ( W:=W ) ( I:=I )): Position W I:= fun w i=> exp (-P.θ i) • info c w i
local notation "Cgx"=> lifted P c
lemma re_n : info c= Port.moved P.θ Cgx:= by funext w i; simp_rw [Port.moved, lifted,smul_smul, Real.exp_neg,mul_inv_cancel₀ (Real.exp_ne_zero _),one_smul]
-- P.roots exponent.M.Height. ascending `Z`.
lemma scaleF (i:I){p q:W}: (Cgx p - Cgx q) i= exp (-P.θ i) • ( info c p - info c q ) i:= by unfold lifted; simp only [Pi.sub_apply,smul_sub]
lemma posed (hp:Mesh P ( info c )): Mesh (frameF I μ) Cgx:= by
    intro p q he; obtain ⟨ ⟨b,hb,hB⟩,d,hd,hD⟩:= hp p q he; have hv(i:I): ‖( info c p - info c q ) i‖= P.roots i * ‖( Cgx p-Cgx q ) i‖:= by rw [ scaleF,norm_smul_of_nonneg (exp_pos _|>.le), ← mul_assoc, roots, ← exp_add ]; rw [add_neg_cancel, exp_zero, one_mul]
    refine ⟨ ⟨ b,hb,fun i=>?_⟩,⟨ d,hd,fun i=>?_⟩⟩; · obtain hp:= hB i; rw [hv] at hp; rw [frameF,roots]; dsimp only [Pi.zero_apply]; rw [exp_zero,mul_one]; apply ( mul_le_mul_iff_right₀ ( exp_pos _ ) ).mp ( by rw [mul_comm b] at hp; exact hp ) -- order
    obtain hp:= hD i; rw [hv] at hp; simp only [frameF,roots,Pi.zero_apply,exp_zero,mul_one]; exact ( mul_le_mul_iff_right₀ ( exp_pos _ ) ).mp ( by rw [mul_comm d] at hp; exact hp )
abbrev higher (P:Geo I)(d:ℕ)(i:I):ℂ:= Port.τ d (P.θ i)
lemma high_nn (P:Geo I)(d:ℕ)(i:I): ‖higher P d i‖=exp (( d:ℝ )*P.θ i):= by rw [higher,Port.τ,Complex.norm_real,norm_eq_abs,abs_of_nonneg,Real.exp_nat_mul]; rfl; positivity
--lemma height_f (hp: S= S) : S=S := rfl -- remove
-- shape.X & DOrd.Phree conversion
abbrev fare (T: W→ℕ)(P:Geo I)(U:Terrify W I) : Terrify W I:= fun s n=> higher P (Vane.charge T s)* U s n
lemma significant {F:I→ℂ}{w:ℕ}{t:ℝ}(h:PeakT l P ((w:ℝ)+ t ) F): PeakT l P t ( higher P w * F ):= by
    rcases h with ⟨C,hC,hk⟩; refine ⟨ C,hC,hk.mono (fun i hi=>?_)⟩; rw [Pi.mul_apply,norm_mul,high_nn]; apply (mul_le_mul_of_nonneg_left hi (exp_pos _).le)|>.trans_eq; rw [mul_left_comm, lake,← Real.exp_add,lake]; congr 2; ring
lemma dealP {Y:Terrify W I}(h:Judge P c V Y Z L l w)(he:NearPlan l P V L μ): PeakT l P mildG ( fare w P Y F n-fare w P Z F n ):= by
    rcases h.stamp with ⟨f,p,_,_,H,hM,hk⟩; by_cases hz:F.Nonempty; swap; · unfold fare; rw [ Finset.not_nonempty_iff_eq_empty.mp hz,h.blanks.1,h.blanks.2, sub_self ]; exact PeakT.zero
    unfold fare; rw [ ← mul_sub ]; apply significant; have hv:= NearPlan.costG he (hM F hz n) (( Vane.charge w F:ℝ )+mildG); obtain hp:= he.gain ( H F hz n|>.1 ); apply PeakT.fromζ ( hv.plus hp ); filter_upwards [hk n F] with i hi; simp only [ Pi.sub_apply,Pi.add_apply,hi ]; abel -- need `memo below`
lemma clockShape {v:Rake.Dance G I W}(P:Geo I)(x:Position W I)(T:W→Label B) (h: ∀ i, P.η i= μ-P.θ i)(hp:DOrd M (frameF I μ) S T x v) (hx:DOrd M P S T ( Port.moved P.θ x ) X)(he:∀ (s:Finset W),s.Nonempty→∀ n i,Allow (v s n) i): fare ( Label.h∘T ) P ( Fleet.toZ X )= toZ v:= by
   funext s n i; unfold fare Fleet.toZ; by_cases hs:s.Nonempty; swap; · rw [Finset.not_nonempty_iff_eq_empty.mp hs,hx.1,hp.1 ]; simp only [Pi.mul_apply, Pi.zero_apply, (Fleet.allow_zero ( G:=G ) i).2, mul_zero ]; -- ambiguous show
   rw [ Pi.mul_apply, show ( Vane.blade _ i ) = _ from congr_fun ( Port.MoonB S ( fun i=> sub_eq_iff_eq_add.mp (h i).symm ) hp hx s n ( he s hs n ) ) i ]; unfold higher; rw [ ← mul_assoc, T_add,add_neg_cancel ]; unfold Port.τ; simp -- parameter eq λ
namespace Verdict
lemma economic (x:I→ℂ)(w:ℕ)(h:title (frameF I μ) 0 w x): PeakT l P 0 x:= by
    rcases h with ⟨C,hC,k,hk⟩; refine ⟨ C*(1+|μ|)^k,by positivity,Eventually.of_forall (fun i=>?_ )⟩; apply ( hk i ).trans_eq; unfold moneyX tarB habitat lake; change C* (( _ * (1+0))^k * exp (_*0)) = _; push_cast; simp -- _
end Verdict
local notation "g"=> (Label.h ∘ u)
variable (h:G.Simple)(hp:TaylorOK S φ A)(he: Clearance L x)(hv: Vista.width L x)(hw: WidthW V P.η c)(hm: Mesh P ( info c ))(hP: NearPlan l P V L μ)
include h hp he hv hw hm hP
lemma CCP (b:Bool): ∃ (Z:Terrify W I)(X:Rake.Dance G I W), ( Z ∅=0 ∧ Fleet.toZ X ∅=0 ∧ ∀ i s,PhysicalSum G A.team (P.η i) (dimT L i) b s (fun w=>c w i) ( x i ) Ur (bury i s Z)) ∧ DOrd M (frameF I μ) S u Cgx X ∧ (∀ s n,PeakT l P mildG (fare g P Z s n-toZ X s n)∧PeakT l P 0 ( Fleet.toZ X s n ))∧∀ s:Finset W,s.Nonempty→∀ n,Verdict (frameF I μ) ( Vane.charge g s ) 0 ( X s n ) := by
   have hs:= payTune c hm hP.vanish; obtain ⟨Ω,X,hQ,hX,hD,hK,hY⟩:= assembly u c h he hv hw hm hs b hp; obtain ⟨Z,Y,H,hJ,hV⟩:= Covers φ S A u (frameF I μ) h (posed c hm) hp; refine ⟨ Ω,Y,⟨ hK.blanks.1,zeroZ hJ.1,hX ⟩,hJ, fun s n=>?_, fun s hs n=> hV s hs n |>.2.1 ⟩; obtain hh : fare g P ( toZ X )=toZ Y:= clockShape P Cgx u hP.dimm hJ ( by rw [ ← re_n ]; exact hD ) (fun s hs n=> hV s hs n|>.2.1.1 )
   refine ⟨ hh ▸ dealP c hK hP,?_ ⟩; by_cases hs:s.Nonempty; exact Verdict.economic _ _ (hV s hs n|>.2.1.2.2); rw [Finset.not_nonempty_iff_eq_empty.mp hs, zeroZ hJ.1]; exact PeakT.zero -- orientation ▸ may motive
end YM.MS.Tide
