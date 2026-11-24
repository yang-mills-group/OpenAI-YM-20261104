import YM.FVA2.Glare
/-!
# Continuous group of scale calibrations. Assemble mass law for the indicated conversion and
at all its needed horizons. This is a genuine formal scale law on independent perturbative
regulator operations; doesn't use phase or exact theory. Scales multiplicatively, shown in
logarithmic unit (increase s means moving to shorter length). Gives cB relation and comparison to
 detector solves. Convent for $β$ will follow. Doesn't extrapolate to top `$\beta$` scheme costs.
-/
set_option autoImplicit false
set_option maxHeartbeats 360000
noncomputable section
namespace YM.FVA2.Forge
open Function Filter Set MeasureTheory Pert Pert.Position Lattice Maxwell Maxwell.Free Pert.RawLabels PositionX PositionX.Jet PositionX.Ribbon PositionX.Detector PositionX.Bend Elegant PayAll Verne Panel Strat ColorCode Ember Pic Legacy Taper
open MS MS.Plane MS.Land MS.Landau MS.Rake MS.High MS.Menus MS.Theater MS.Logarithm MS.Tide MS.Book MS.Book.Program MS.Book.Convolve Clock
open Hop
open scoped Topology ContDiff Classical
variable {G:Gauge} {F:Labels.Frames G} {r:ℝ}
variable {W:ℝ→ Hop F}{A:Panel F}(D:(d:ℕ)→ Detector F d)(R:Booth r F)
structure Month (A:Panel F)(W:ℝ→ Hop F)(D:(d:ℕ)→ Detector F d){r:ℝ}(R: Booth r F): Prop where
   first:Fresh A -- adjust
   funds: A.tangible D R
   eats (t:ℝ): Flo A t ( W t )
   freshS: glowT W
namespace Month
abbrev ψ (W:ℝ→ Hop F)(t:ℝ):= (W t).f
variable {D R}(H:Month A W D R) (s t:ℝ)
def B (W:ℝ→Hop F)(D:(d:ℕ)→ Detector F d)(s:ℝ): Strat F:= refresh D ( W s ).Z ( W s ).tangent
-- variable omitted -- parse.Tricky local
local notation "Bx" t=> B W D t
local notation "φ" t=> (ψ W t)
include H
lemma timed : W (s+t)= W t * glance t (W s):= Hop.flow_focus _ s t _ _ H.first H.funds W H.eats -- A first? check
lemma compositionψ : ψ W (s+t)= Jet.ren (ψ W s) (ψ W t):= congr_arg Hop.f ( timed H s t ) -- rfl ?
lemma origin : W 0=1 := Hop.distinct ( W 0 ) 1 _ D R H.first H.funds ( Eq.trans (Eq.symm (H.eats 0)) ((Panel.z1 A).trans (dormant A).symm) )
lemma capsizeV (t:ℝ)(p:Hop F) : A.swell t=act A p ↔ p=W t:= ⟨fun h=>Hop.distinct p _ A D R H.first H.funds (h.symm.trans (H.eats t)), fun h=> h.symm ▸ H.eats _⟩
omit H in
lemma warm (W:ℝ→ Hop F)(D:(d:ℕ)→ Detector F d): Strat.pulse ( B W D s ) ∧ Strat.only (B W D s) * only (W s).Z=1 ∧ B W D s * ( W s ).Z=1 ∧ ( W s ).Z * B W D s=1 := by
   obtain ⟨hp,hq,hk⟩:= Strat.right_refresh D ( W s ).Z (W s|>.tangent); refine ⟨hp,?_,hk,hq⟩; rw [ ← onlyT,B,hk, onek ] -- B unfold needed

lemma actions : ( A.swell s ).flip (B W D s)= A.join (ψ W s):= by rw [show Panel.swell A _= _ from H.eats _, Hop.act, flip_mul, (warm s W D).2.2.2, leading ]
lemma stages : Strat.pulse (B W D (s+t)) ∧
             B W D (s+t) = ( Λ F (-t)*B W D s*Λ F t ) * Strat.resume ( B W D t ) (ψ W s):= by
    refine ⟨ (warm (s+t) W D).1,?_ ⟩;
    let v:= Strat.resume (B W D t) (ψ W s); let f:= ( W (s+t) ).Z; let T:=Λ F t; let σ:= Λ F (-t); have hs:= warm s W D; have ht:= warm t W D;
    have hv : Strat.resume ( W t ).Z (ψ W s) * v=1:= by unfold v; rw [ ← resumeT _ _ ( W s ).rooted, ht.2.2.2,resume0 ]
    suffices hd : f * ((σ * B W D s*T)*v)=1 by rw [show (σ * B W D s*T)*v= B W D (s+t)*(f*((σ*B W D s*T)*v)) from Eq.symm (by rw [← mul_assoc, show B W D (s+t)*f=_ from (warm (s+t) W D).2.2.1, one_mul ] ), hd,mul_one ]; -- implicit proof rewriting RHS under v issues.
    unfold f; rw [ timed H s t, walkZ ]; change Strat.resume ( W t ).Z (ψ W s) * (σ*( W s ).Z*T)* _=_; rw [ mul_assoc ]; have hx: T*σ=1:=north; -- argument implicit
    have hg : σ*( W s ).Z*T * (σ* B W D s*T)=1:= by rw [← mul_assoc, mul_assoc _ T, ← mul_assoc T, hx,one_mul, mul_assoc, mul_assoc, ← mul_assoc (( W s ).Z), hs.2.2.2,one_mul]; exact south -- adjust  ];
    rw [← mul_assoc (σ*( W s ).Z*T), hg,one_mul,hv]
lemma tentative₀ : ψ W 0=headway∧B W D 0=1:= by
    obtain hp:= (warm 0 W D).2.2.1; refine ⟨ congr_arg Hop.f H.origin, ?_⟩; rw [ H.origin,eZ,mul_one ] at hp; exact hp
-- convenience implicit H parameter from user
lemma gradeB (u:ℝ)(h:( W u ).gradedStep) : (B W D u).only=B W D u:= by obtain he:=warm u W D; have hv:= he.2.1; rw [show (W u).Z.only=(W u).Z from h ] at hv; nth_rw 1 [ ← mul_one ( B W D u |>.only ) ]; rw [← he.2.2.2,← mul_assoc, hv,one_mul ] -- assoc direction
-- coefficient smooth.Inverse identity
lemma retime : Strat.resume ( ( glance s ( W (-s) ) ).Z ) ( ( W s ).f ) = B W D s:= by
   let T (t:ℝ):= W t; obtain hv:= H.timed (-s) s; rw [neg_add_cancel, H.origin] at hv; let t:=T s; let q:=glance s ( T (-s) );
   have hp:T (0:ℝ)=1:= H.origin; have hz : ren ( ψ W (-s) ) ( ψ W s )=headway:= Eq.symm ( (congr_arg Hop.f hv) ); have hu : ren ( ψ W s ) ( ψ W (-s) )=headway:= by rw [ ← compositionψ H s (-s),add_neg_cancel ]; exact H.tentative₀.1
   have he : Strat.resume t.Z q.f * q.Z=1:= Eq.symm ( congr_arg Hop.Z hv );
   let p:=Strat.resume q.Z t.f;
   have hm:t.Z*p=1:= by
      have hk:= congr_arg (fun p:Strat F=> p.resume t.f) he; rw [ resumeT _ _ t.rooted, resumeM _ t.rooted q.rooted, show ren t.f q.f=headway from hu, resumeHead,resume0 ] at hk; exact hk
   change p=_; conv_lhs => rw [← one_mul p, ← show B W D s * t.Z=1 from (warm s W D).2.2.1, mul_assoc ]
   rw [ hm,mul_one ]
lemma scales_live (d:ℕ): Taper.soft (fun s=> B W D s|>.wire d):= by
   let T (t:ℝ):= glance t ( W (-t) ); have hp: glowT (fun x:ℝ=>W (-x)):= by obtain ⟨ hp,hk⟩:= H.freshS; exact ⟨ fun i j=> ( hp i j ).comp contDiff_id.neg, fun i=> ( hk i ).comp contDiff_id.neg ⟩; -- defeq id
   have he:= glow_gl _ hp; intro i; simp_rw [← H.retime, resume_wire ]; exact Taper.relay_u _ (he.1 d) _ (H.freshS.2) i
lemma polyScales (h:habit W) (d:ℕ): Legacy.polynomial fun s=> (B W D s).wire d := Legacy.guarding ( D d ) (fun t=> (W t).Z.wire d) ( h.1 d ) ( fun t=>(W t).tangent d )
end Month
variable (V : Warehouse G) {O:Booked (wings G)}{q:ℝ}(h:G.Simple)(M:MS_Data G O)(T:Booth q V.F)(v s t:ℝ)(Sx: Pic.pass V h M T)
local notation "Fv"=> V.F
local notation "θ"=> nested V.F h (BoxOffice.warehouse V)
abbrev Xray := fun s=> Forge.xflow V M T s v Sx
abbrev Mray := fun s=> Forge.diffuse V M T s v Sx
abbrev Cray := fun s=> Forge.cflow V M T s v Sx
local notation "U"=> Forge.Mray V h M T v Sx
local notation "U₁"=> Forge.Cray V h M T v Sx
local notation "X"=> Pic.X V h M v T
-- installed PS and rays
lemma real_ms : Month (Pic.marked V M v) (Forge.Mray V h M T v Sx) θ T:= ⟨ freshMark .., vital_m V M T v Sx, fun t=>Forge.notate_m V M T t v Sx, habitT _ (Legacy.debut_m ..) ⟩
lemma real_c : Month (Forge.Check V M T v Sx) (Forge.Cray V h M T v Sx) θ T:= ⟨ nearW ..,(vitalW ..).2, fun t=> Forge.shade V M T t v Sx, habitT _ ( Taper.fixstep .. ) ⟩
lemma real_X : Month X (Forge.Xray V h M T v Sx) θ T:= ⟨ Pic.innerX .., Forge.vitalX V M T v Sx, fun t=> Forge.directV V M T t v Sx, Taper.trajectory .. ⟩
lemma cal_s (d:ℕ) : let B:= Month.B ( Forge.Xray V h M T v Sx ) θ s; ( θ d ).report ( ( (X).swell s ).lives d )= B.wire d  := by
    intro p; let P:=Forge.Xray V h M T v Sx; let f:= ( P s ).f; obtain ht:= Forge.real_X V h M T v Sx; -- shadow
    let x:= (X).swell s; have hx: Fresh x:= by unfold x; rw [ show Panel.swell X s= _ from ht.eats s ]; exact Hop.approach (P s) X ( Pic.innerX .. );
    symm; obtain hv:= Elegant.solves_only ( θ d ) ( x.lives d ) ( hx.2 d ); refine hv.2.2 _ ( Month.warm s _ θ |>.1 d ) ?_; unfold Detector.announce; rw [ ← Panel.turn_book _ p hx.1, show Panel.flip _ _=_ from Month.actions ht s, Panel.total_book _ _ (ht.first.1), Jet.ren_writes ]; obtain he:= Pic.nearX V M _ _ d ( h:=h ); unfold Detector.announce at he; rw [Verne.float ] at he; rw [ he,Jet.ren_static ( V:=Buffer V.F d ) _ ( P s ).rooted ]
-- preserve within-grade conjugation explicitly and scaling ζ flows
lemma scales_equate : let g:=Forge.transfer V M T v Sx; g * Forge.cflow V M T s v Sx = Forge.diffuse V M T s v Sx * g:= by
    intro g; rw [ Forge.transported, Taper.beam s _ (gradedT ..) ]
end YM.FVA2.Forge
