import YM.ForFlash.MS.Assembly
/-! Adapted from the YM modules indicated. Only lower gap hypothesis on the Mesh arguments,
see Phase for the change in the estimate itself. -/
set_option autoImplicit false
noncomputable section

/- Widening MS/Tide/Coi -/
namespace YM.MS.Tide
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Lattice Land Frame Latch Job Heat Detect Book Convolve Program
open Native Wilsonian Paint High Wind Rake Rake.Geo Vista Vane City Orbit Cog Orbit.LogReal
open Puff Engine SplitP Actors Dynamics Puff.Mom
open Fleet Swirl Swirl.Near SpaceOut Menus Echo
open scoped Topology ContDiff Interval
variable {W I:Type}{P:Geo I}{V:Visa I}{L:I→Side}{x: Faces I}{G:Gauge}{b:Bool} [LinearOrder W]
    {B:Local.Physical.Deck G}{M:Land.Booked B}{t:Team}
    {F:Finset W}{φ: LitBook B}{A: Land.Prescription B}{S: MS_Data G M}{n:ℕ}
    (u:W→Label B)(c:Berth ( W:=W ) ( I:=I )) {l: Filter I}
    {X:Rake.Dance G I W}{Z:Terrify W I}

lemma payTuneForFlash (hE: MeshForFlash P ( info c ))(ht:Tendsto P.θ l atTop): Sparse l c:= by
   intro i j hi; obtain ⟨a,ha,hx⟩:= hE i j hi|>.floor; refine tendsto_atTop_mono ?_ (( tendsto_exp_atTop.comp ht ).const_mul_atTop ha)
   intro p; apply ( hx p ).trans_eq; simp only [Pi.sub_apply, emb_sub]; rfl
end YM.MS.Tide

/- Widening MS/Tide/Lion -/
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
local notation "Cgx"=> lifted P c
lemma posedForFlash (hp:MeshForFlash P ( info c )): MeshForFlash (frameF I μ) Cgx:= by
    intro p q he; obtain ⟨d,hd,hD⟩:= (hp p q he).floor; have hv(i:I): ‖( info c p - info c q ) i‖= P.roots i * ‖( Cgx p-Cgx q ) i‖:= by rw [ scaleF,norm_smul_of_nonneg (exp_pos _|>.le), ← mul_assoc, roots, ← exp_add ]; rw [add_neg_cancel, exp_zero, one_mul]
    refine ⟨ d,hd,fun i=>?_⟩
    obtain hp:= hD i; rw [hv] at hp; simp only [frameF,roots,Pi.zero_apply,exp_zero,mul_one]; exact ( mul_le_mul_iff_right₀ ( exp_pos _ ) ).mp ( by rw [mul_comm d] at hp; exact hp )
end YM.MS.Tide

/- Widening MS/Tide/Stated -/
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
abbrev ProfileForFlash (P:Geo I)(c:Berth ( W:=W ) ( I:=I )): Prop:= ∀ w, ∃ r:ℝ,0<r∧∃ n:ℕ,∀ i,‖ Tone.embed ( c w i )‖≤ r*exp ( P.θ i )^n
variable (h:ProfileForFlash P c) (hx:∀ i, P.η i=μ-P.θ i)
   (hu:Tendsto P.θ l atTop)(hp: Super l L P.θ)
include h hx hu hp
lemma qualifiesForFlash : ∃ V:Visa I, WidthW V P.η c∧ NearPlan l P V L μ:= by
    let B(i:I):= exp (P.θ i)*(1+|μ|); let V': Visa I:=⟨ B,fun i=>one_le_mul_of_one_le_of_one_le ( Real.one_le_exp ( P.room i ) ) (by simp) ⟩; have hv(i:I):exp (P.θ i)≤B i:= le_mul_of_one_le_right (exp_pos _|>.le) (by simp)
    refine ⟨ V',⟨ fun i=> ?_,fun w=>?_⟩,⟨ hu,hp,hx,2,?_⟩⟩; · rw [hx]; change 1+|μ-P.θ i|≤B i; obtain ht:= Real.add_one_le_exp ( P.θ i ); obtain hb:=abs_sub μ ( P.θ i ); rw [abs_of_nonneg ( P.room _ )] at hb; unfold B; nlinarith [abs_nonneg μ,Real.one_le_exp ( P.room i )]
    · obtain ⟨a,ha,n,hA⟩:= h w; refine ⟨ a,ha,n,fun i=>?_⟩; rw [Pi.one_apply,mul_one]; exact (hA i).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (exp_pos _).le (hv i) _) ha.le )
    have H:∀ᶠ i in l,1+|μ|≤ exp ( P.θ i ):=( tendsto_exp_atTop.comp hu ).eventually ( eventually_ge_atTop .. ); filter_upwards [H] with i hi; change B i≤exp _; rw [two_mul, exp_add ]; unfold B; gcongr
end YM.MS.Tide

/- Widening FVA2/Full/Stated -/
namespace YM.MS.Tide
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Lattice Land Frame Latch Job Heat Detect Book Convolve Program
open Native Wilsonian High Wind Rake Rake.Geo Vista Vane Port City Orbit Cog Orbit.LogReal
open Puff Engine SplitP Actors Dynamics Puff.Mom
open Fleet Swirl Swirl.Near SpaceOut Menus Echo
open scoped Topology ContDiff Interval
variable {I W:Type}{P:Geo I}{V:Visa I}{L:I→Side}{x: Faces I}{G:Gauge}{b:Bool} [LinearOrder W]
    {B:Local.Physical.Deck G}{M:Land.Booked B}{F:Finset W}{φ: FullBook B}{A: Land.Prescription B}{S: MS_Data G M}{n:ℕ}{μ:ℝ}
    (u:W→Label B)(c:Berth ( W:=W ) ( I:=I )) {l: Filter I}
    {X:Rake.Dance G I W}{Z:Terrify W I} {w:W→ℕ}
set_option quotPrecheck false
local notation "Yr"=> ApplyMF φ A.team A u
local notation "Ur"=> ApplyMF φ ( Stripped A.team ) A u
local notation "Qa"=> goalsK c P.η Yr
local notation "Cgx"=> lifted P c
local notation "g"=> (Label.h ∘ u)
variable (h:G.Simple)(hp:TaylorOKF S φ A)(he: Clearance L x)(hv: Vista.width L x)(hw: WidthW V P.η c)(hm: MeshForFlash P ( info c ))(hP: NearPlan l P V L μ)
include h hp he hv hw hm hP
lemma CCPFForFlash (b:Bool): ∃ (Z:Terrify W I)(X:Rake.Dance G I W), ( Z ∅=0 ∧ Fleet.toZ X ∅=0 ∧ ∀ i s,PhysicalSum G A.team (P.η i) (dimT L i) b s (fun w=>c w i) ( x i ) Ur (bury i s Z)) ∧ DOrd M (frameF I μ) S u Cgx X ∧ (∀ s n,PeakT l P mildG (fare g P Z s n-toZ X s n)∧PeakT l P 0 ( Fleet.toZ X s n ))∧∀ s:Finset W,s.Nonempty→∀ n,Verdict (frameF I μ) ( Vane.charge g s ) 0 ( X s n ) := by
   have hs:= payTuneForFlash c hm hP.vanish; obtain ⟨Ω,X,hQ,hX,hD,hK,hY⟩:= assemblyFForFlash u c h he hv hw hm hs b hp; obtain ⟨Z,Y,H,hJ,hV⟩:= CoversFForFlash φ S A u (frameF I μ) h (posedForFlash c hm) hp; refine ⟨ Ω,Y,⟨ hK.blanks.1,zeroZ hJ.1,hX ⟩,hJ, fun s n=>?_, fun s hs n=> hV s hs n |>.2.1 ⟩; obtain hh : fare g P ( toZ X )=toZ Y:= clockShape P Cgx u hP.dimm hJ ( by rw [ ← re_n ]; exact hD ) (fun s hs n=> hV s hs n|>.2.1.1 )
   refine ⟨ hh ▸ dealP c hK hP,?_ ⟩; by_cases hs:s.Nonempty; exact Verdict.economic _ _ (hV s hs n|>.2.1.2.2); rw [Finset.not_nonempty_iff_eq_empty.mp hs, zeroZ hJ.1]; exact PeakT.zero
end YM.MS.Tide
namespace YM.MS.Tide
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Lattice Land Frame Latch Job Heat Detect Book Convolve Program
open Native Wilsonian High Wind Rake Rake.Geo Vista Vane Port City Orbit Cog Orbit.LogReal
open Puff Engine SplitP Actors Dynamics Puff.Mom
open Fleet Swirl Swirl.Near SpaceOut Menus Echo
open scoped Topology ContDiff Interval
variable {W I:Type}{P:Geo I}{V:Visa I}{L:I→Side}{x: Faces I}{G:Gauge}{b:Bool} [LinearOrder W]
    {B:Local.Physical.Deck G}{M:Land.Booked B}{F:Finset W}{φ: FullBook B}{A: Land.Prescription B}{S: MS_Data G M}{n:ℕ}{μ:ℝ}
    (u:W→Label B)(c:Berth ( W:=W ) ( I:=I )) {l: Filter I}
    {X:Rake.Dance G I W}{Z:Terrify W I}
set_option quotPrecheck false
local notation "Yr"=> ApplyMF φ A.team A u
local notation "Ur"=> ApplyMF φ ( Stripped A.team ) A u
local notation "g"=> (Label.h ∘ u)
open PeakT (ordZ)
variable (h:ProfileForFlash P c) (hx:∀ i, P.η i=μ-P.θ i)
   (hu:Tendsto P.θ l atTop)(hp: Super l L P.θ)
include h hx hu hp
variable (hG:G.Simple) (hc:Clearance L x)(hw:Vista.width L x)(hm:MeshForFlash P ( info c ))
include hG hc hw hm
lemma calledFForFlash (hZ:TaylorOKF S φ A)(b:Bool): ∃ Z Y,scalePhysicsF P M S μ A φ u c x L b l Z Y:= by
    obtain ⟨V,hV,hV'⟩:= qualifiesForFlash c h hx hu hp; obtain ⟨Z,Y,⟨hn,hU,hN⟩,hz,ht,hQ⟩:= CCPFForFlash u c hG hZ hc hw hV hm hV' b
    refine ⟨Z,Y,hN,hn,hz,hQ, fun s n=>⟨(ht s n).symm,?_⟩⟩; rw [← funext (fun i=> PeakT.ν_norm g ( s:=s ) ( P:=P ) ( n:=n ) i Z) ]; exact PeakT.projection ht s n
end YM.MS.Tide

/- Widening MS/Dial/Slope -/
namespace YM.MS.Dial
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Osc Snap City Job Geo Land Local.Physical Port Tide Fleet Puff Engine Actors Puff.Mom
open PeakT
open Vane
open scoped Topology ContDiff
variable {I W E:Type} {G:Gauge} {v t:ℝ}{r:ℕ}[LinearOrder W]{l:Filter I}
variable {B:Deck G}{M:Booked B}(A:MS_Data G M)(u:W→Rake.Label B)
variable {U:Rake.Dance G I W}{F:Finset W}{x:Position W I}(v:ℝ)
local notation "R"=> frameF I v
variable ( h: MeshForFlash (frameF I v) x)(ht: DOrd M (frameF I v) A u x U) (p:I)
include h
lemma detailIForFlash : Injective (pointI x p):= by
    intro a b he; by_contra ht; obtain ⟨d,hd,hD⟩:= (h a b ht).floor; specialize hD p; change x a p=x b p at he; simp only [roots,frameF,Pi.zero_apply,exp_zero,mul_one,Pi.sub_apply,he,sub_self,norm_zero] at hD; linarith
include ht
lemma PointIForFlash (s:Finset W)(k:ℕ): U s k p=spine A u v (pointI x p) s k ():= by
    have he:= valid_copy u ht (fun (_:Unit)=>p) ( Q:=frameF Unit v ) (fun i=>rfl); obtain hp:spine A u v (pointI x p)= copy (fun (_:Unit)=>p) U:= perfect (pin A u v (detailIForFlash v h p)) he; rw [hp]; rfl
lemma Point_tForFlash (F:Finset W) (n:ℕ): Fleet.toZ U F n p=book A u v (pointI x p) F n:= by unfold Fleet.toZ book Vane.blade; rw [PointIForFlash A u v h ht p];
lemma shape_fForFlash (F:Finset W)(n:ℕ): ordZ (Fleet.toZ U) F n p=tour A u v (pointI x p) F n := by
    have he : ( fun s k=> Fleet.toZ U s k p)=book A u v (pointI x p):= funext fun s=> funext fun k=> Point_tForFlash A u v h ht p s k; unfold ordZ bury tour; rw [he]
end YM.MS.Dial

/- Widening MS/Dial/Set -/
namespace YM.MS.Dial
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Osc Snap City Job Geo Land Local.Physical Port Tide Fleet Puff Engine Actors Puff.Mom
open PeakT
open Vane
open scoped Topology ContDiff
variable {I W E:Type} {G:Gauge} {v t:ℝ}{r:ℕ}[LinearOrder W]{l:Filter I}
open Orbit Rake Tide Vista Lattice
variable {P:Geo I}
lemma unposeForFlash (p:Berth ( I:=I ) ( W:=W ))(h:MeshForFlash (frameF I v) (lifted P p)): MeshForFlash P ( Fleet.info p ):= by
    intro a b he; let X:=P.roots; have ht : ∀ i, 0<X i:= fun i=> exp_pos _; let q:= lifted P p; let V:= info p; have hp (i:I) : ‖( V a-V b ) i‖= X i * ‖( q a-q b ) i‖:= by rw [scaleF p i, norm_smul_of_nonneg (exp_pos _|>.le)]; unfold X roots; rw [ Real.exp_neg,← mul_assoc,mul_inv_cancel₀ (exp_pos _|>.ne'),one_mul ]
    obtain ⟨A,hA,hB⟩:=(h a b he).floor; simp only [roots,frameF,Pi.zero_apply,exp_zero,mul_one] at hB; refine ⟨ A,hA,fun i=>?_⟩
    rw [ show ‖(info p a-info p b) i‖=_ from hp i ]; rw [ mul_comm A ]; exact mul_le_mul_of_nonneg_left (hB i) ( ht i|>.le )
variable (T:Trial I W)
structure UsesForFlash (T:Trial I W)(l:Filter I)(η:ℝ): Prop where
    total: ProfileForFlash T.profile T.off
    knit: MeshForFlash T.profile ( Fleet.info T.off )
    reality i: T.profile.η i=η-T.profile.θ i
    upright:Tendsto T.profile.θ l atTop
    super: Super l T.side T.profile.θ
    clear: Clearance T.side T.head
    wind: Vista.width T.side T.head
lemma microForFlash (h:MeshForFlash T.profile (info T.off)) : ∀ i, Injective (testP T i):= fun _=> detailIForFlash 0 (posedForFlash T.off h) _
end YM.MS.Dial

/- Widening FVA2/Full/Stated -/
namespace YM.MS.Dial
open Set Function Filter Finset Metric MeasureTheory Real High
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Osc Snap City Job Geo Land Local.Physical Port Tide Vista Fleet
open Lattice
open scoped Topology ContDiff
open Vane PeakT Program Menus Swirl Swirl.Near
open Native Wilsonian
variable {W I:Type} {μ:ℝ}{n:ℕ}[LinearOrder W] {l:Filter I}
variable {G:Gauge}{B: Deck G}{M:Booked B}(S:MS_Data G M)(φ: FullBook B)(p:W→Label B)
   (T:Trial I W){A:Prescription B}
local notation "sV"=> p
local notation "gj"=> (Label.h ∘ p)
variable {V:Terrify W I}
lemma check_tFForFlash (h:TaylorOKF S φ A)(U:UsesForFlash T l μ)(hp:G.Simple)(b:Bool): ∃ V:Terrify W I,coherentF M S φ p T μ b A l V:= by
    obtain ⟨ Z,Y,hY⟩:= Tide.calledFForFlash p T.off U.total U.reality U.upright U.super hp U.clear U.wind U.knit h b; have hv:=posedForFlash (μ:=μ) T.off U.knit; have hh(s:Finset W)(n:ℕ): Fleet.toZ Y s n=(fun i=> book S p μ ( testP T i ) s n):= funext fun i=> Point_tForFlash S p μ hv hY.scheme i s n;
    refine ⟨Z,hY.empty,fun i s=>?_,fun i u=> hh i u ▸ ( hY.compares i u ).1,fun i t=>?_ ⟩; exact U.reality i ▸ hY.native i s; rw [ ← show ordZ ( Fleet.toZ Y ) i t=(fun s=> tour S p μ ( testP T s ) i t) from funext fun s=> shape_fForFlash S p μ hv hY.scheme s i t ]; exact ( hY.compares i t|>.2 )
end YM.MS.Dial

end
