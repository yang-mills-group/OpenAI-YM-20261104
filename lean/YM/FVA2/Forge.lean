import YM.FVA2.Hop
/-!
# One physical f and Z for the independently normalized perturbative correlation predictions.

Using a now arbitrary subtraction height v; X coupling at *fixed* diagnostics sets physical
length unit; does not assert f(t) is OP for different relative normalization heights chosen
ad hoc; instead show scale flows.Separated point statement, repeated usage scalar estimates.
-/
set_option autoImplicit false
set_option maxHeartbeats 210000
noncomputable section
namespace YM.FVA2.Forge
open Function Filter Set Pert Pert.Position Lattice Maxwell Maxwell.Free Pert.RawLabels PositionX PositionX.Jet PositionX.Ribbon PositionX.Bend Elegant PayAll Verne Panel Strat ColorCode Pic Sail
open MS MS.Plane MS.Land MS.Landau MS.Rake MS.High MS.Menus MS.Theater MS.Logarithm MS.Tide
open Hop Ember
open scoped Topology ContDiff Classical
variable {G:Gauge} (V: Warehouse G) {h:G.Simple} {O: Booked (wings G)} (M:MS_Data G O)
variable {q:ℝ} (R: Booth q V.F) (s v t:ℝ){d:ℕ}  -- adjust
local notation "F"=> V.F

local notation "K"=> BoxOffice.warehouse V
local notation "θ"=> nested V.F h (BoxOffice.warehouse V)
local notation "Xv"=> Pic.X V h M v R
local notation "Xs"=>Pic.X V h M
local notation "Lø" s=> Pic.L V M s h -- single spacing
local notation "Ω"=> Pic.marked V M
variable (Sx: Pic.pass V h M R)
lemma stock (s:ℝ): plain V ( Ω s ):= by
    intro d k r w; unfold Draw; simp_rw [ Pic.scaled ]; let p:= Polynomial.C s-Polynomial.X; convert poly_rot p (time_marked V M r w) using 1; ext; simp [p] -- M at s-t not converted.
lemma profits (A:Hop V.F) (C:Panel V.F) (hp:plain V C)(ht:A.gradedStep): plain V ( Hop.act C A ):= by obtain h:= shapeM V (C.join A.f) A.Z (shapeμ V C hp A.rooted); rw [ show A.Z.only=A.Z from ht ] at h; exact h
include h
-- independent MS coordinate conversion (X) before final mass shift
local notation "Λ'"=> Pic.L V M v h -- avoid operator confusion.
local notation "ξ'" y=> Elegant.ξ h V M y R
def Pay (Sx:Pic.pass V h M R)(y:ℝ): Hop V.F:=
   let f:= inverse (ξ' y); { f:= f, rooted:= Jet.lives _, primary:= by unfold f; rw [ tip_inv ( Sx.lens y ), Sx.lane, inv_one ], Z:= Strat.resume ( Lø y ) f, tangent:= Strat.pulse.near _ ( pulseL V M y (h:=h) ) ( Jet.lives _ ) }
local notation "ηP"=> Pay V M R Sx
lemma corresponding : Pic.X V h M v R=Hop.act (Ω v) (ηP v):= Panel.join_flip _ _ _ ( Jet.lives _ ) -- proof presentation.
lemma epsilon_t : (ηP v).f 1=1:= (ηP v).primary
-- N to strip lower increments, independent definition Check behind X.N
abbrev strict (a:Strat V.F) : Prop:= a.only=1
-- canonical adjustment from pure moment facts! use strict lower and MS powerlog. Avoid implicit context binder.L
structure Selected (W:Panel V.F)(A:Strat V.F): Prop where
    stable: Strat.pulse A
    head : A.only=1
    budget: Ember.plain V ( W.flip A )
include Sx
omit Sx in
lemma unique_pick (C:Panel V.F) (hv:C.Fresh){a b: Strat V.F}(hp:Selected V C a)(ht:Selected V C b): a=b:= by -- doesn't need Sx.later remove.
    let Z:=refresh θ a hp.stable; obtain ⟨hq,hA,h'A⟩:= right_refresh θ a hp.stable; let Q:= C.flip a; have he: Q.flip ( Z * b )= C.flip b:= by unfold Q; rw [Panel.flip_mul,←mul_assoc, show a*Z=1 from hA,one_mul ];
    have hR:= Ember.obstruction V Q (Z*b) θ ( Panel.Fresh.matrix C hv hp.stable ) ( Strat.pulse.grow _ _ hq ht.stable ) hp.budget ( he.symm ▸ ht.budget );
    have hy: only Z=1:= by
        nth_rw 1 [ ← mul_one ( only Z ) ]; nth_rw 1 [ ← hp.head ]; 
        rw [← onlyT,show Z*a=1 from h'A,onek]; -- rw changes 1 rhs too (rw old use nth)

    have Hb : Z*b=1:= by rw [ ← hR, onlyT,ht.head,hy,mul_one ];
    rw [ show b= a*( Z*b ) from ?_,Hb,mul_one ]; rw [← mul_assoc,show a*Z=1 from hA,one_mul ]
-- since build inverse proves via pure scheme. easy formula N
local notation "𝓟" y=> Pay V M R Sx y
-- WARNING macros
local notation "ι"=> θ
def chooseN : Strat V.F:= refresh θ (ηP v).Z (ηP v).tangent * only (ηP v).Z
lemma reflect0 : (ηP v).Z * chooseN V M R v Sx= only (ηP v).Z := by unfold chooseN; rw [← mul_assoc, (right_refresh _ _ _).2.1,one_mul ]
lemma tall0 : pulse (chooseN V M R v Sx):= by unfold chooseN; exact Strat.pulse.grow _ _ ( right_refresh _ _ _ ).1 ( Strat.pulse.adj _ (ηP v).tangent )
-- uniqueness by normstab.* Proof-order compatibility covered.L.Hierarchy.
lemma focusN : Selected V Xv (chooseN V M R v Sx):= by
    let T:=ηP v; let f:=T.f; let A:=T.Z; let Z:= refresh θ A T.tangent; let G:=chooseN V M R v Sx; obtain ⟨hp,hk,hq⟩:= right_refresh θ A T.tangent; refine ⟨ tall0 V M R v Sx,?_,?_ ⟩;
    · change only (Z * only A)=1; rw [ onlyT, diagonal_o,← onlyT,show Z*A=1 from hq, onek ]
    rw [corresponding V M R v Sx ]; unfold Hop.act; rw [ Panel.flip_mul,reflect0 ]; exact shapeM _ _ _ ( shapeμ _ _ ( stock V M _ ) ( T.rooted ) ) -- arity h param.
-- note Act conform.N & output
abbrev transfer : Hop V.F:= let T:=Pay V M R Sx v; ⟨T.f,T.rooted,T.primary, Strat.only T.Z,Strat.pulse.adj _ T.tangent ⟩
def Check : Panel V.F:= ( Pic.X V h M v R ).flip (chooseN V M R v Sx)
lemma agrees : Check V M R v Sx=Hop.act ( Ω v ) (transfer V M R v Sx):= by unfold Check; rw [corresponding V M R v Sx ]; unfold Hop.act; rw [Panel.flip_mul,reflect0]
lemma vital_m : Panel.tangible (Ω v) θ R := by unfold tangible; rw [ Pic.realizer ]; exact Sx.lens _
lemma unique_transfer {A: Hop V.F}(he:Check V M R v Sx=Hop.act ( Ω v ) A): A=transfer V M R v Sx:= Hop.distinct A (transfer V M R v Sx) (Ω v) θ R ( freshMark .. ) (vital_m V M R v Sx) (he.symm.trans (Forge.agrees ..))
lemma plainW : plain V (Check V M R v Sx):= (focusN ..).budget
lemma gradedT : (transfer V M R v Sx).gradedStep:= Strat.diagonal_o _
lemma nearW : Fresh (Check V M R v Sx):= Panel.Fresh.matrix _ ( Pic.innerX V M v R ) ( focusN V M R v Sx ).stable -- clear also
lemma currencyX (p: Strat V.F)(ht:p.pulse): testable ((Xv).flip p) θ R=headway:= (Panel.money Xv θ R ( innerX .. ) ht ).symm.trans ( Pic.modeX V M v R Sx ) -- Xv.`dot`
lemma vitalX : tangible Xv θ R:= by unfold tangible; rw [Pic.modeX V M v R Sx ]; exact ⟨head_light, tip_head.symm ▸ one_ne_zero⟩
lemma vitalW : testable (Check V M R v Sx) θ R=headway ∧ tangible ( Check V M R v Sx ) θ R:= by
   have H:testable (Check V M R v Sx) θ R=headway:= currencyX V M R v Sx _ ( tall0 V M R v Sx ); exact ⟨H, show Genuine _ from H.symm ▸ (show Genuine headway from ⟨head_light, tip_head.symm ▸ one_ne_zero ⟩ ) ⟩
-- rate laws: realize one Hop acting at all μ geometry.Prior to ∆-shift. MS first by expressing step ν9 via another MS arrays via X unique from schedule comparison arbitrary q family. independent not via brute Λ clock.
-- coordinate order type.Eva.
def diffuse : Hop V.F:= ηP v * Hop.undoV ( ηP (v-s) ) θ
lemma notate_m : Flo (Ω v) s ( Forge.diffuse V M R s v Sx ):= by
   unfold Flo diffuse; rw [ Pic.scaled, ← act_step,← corresponding, Pic.across V M R Sx v (v-s), corresponding V M R (v-s) Sx, act_step, lefto,dormant ]
lemma grade_m : (Forge.diffuse V M R s v Sx).gradedStep:= Hop.day_eq V (Ω v) θ (freshMark ..) ( Forge.stock V M v ) (( Forge.notate_m .. ) ▸ shapeS _ _ _ (Forge.stock V M v) ) -- shapeS namespace
-- generate X and checked flow by conjugation.
def slideOf (s:ℝ)(T U:Hop V.F): Hop V.F:= ( undoV T θ * U ) * glance s T
omit Sx
lemma onFrame {P:Panel V.F} (A B:Hop V.F)(hv: Flo P s A): Flo (Hop.act P B) s ( slideOf V s B A (h:=h) ):= by
   unfold Flo; rw [Hop.bevel, show Panel.swell P s= _ from hv, act_step, act_step ]; unfold slideOf; rw [ ← mul_assoc B, ← mul_assoc B,lefto,one_mul ]
include Sx
def xflow : Hop V.F:= slideOf V s ( ηP v ) (Forge.diffuse V M R s v Sx) (h:=h)
def cflow : Hop V.F:= slideOf V s ( transfer V M R v Sx ) (Forge.diffuse V M R s v Sx) (h:=h)
lemma shade : Flo ( Check V M R v Sx ) s ( cflow V M R s v Sx ):= by rw [Forge.agrees ]; exact onFrame V s ( h:=h ) _ _ ( Forge.notate_m .. )
lemma directV : Flo Xv s (Forge.xflow V M R s v Sx):= by rw [ corresponding V M R v Sx ]; exact onFrame V s _ _ ( Forge.notate_m .. ) -- t.
lemma grade_c : (Forge.cflow V M R s v Sx).gradedStep:= Hop.day_eq V (Check V M R v Sx) θ ( nearW .. ) ( Forge.plainW V M R v Sx ) ( (shade V M R s v Sx) ▸ shapeS _ _ _ (Forge.plainW V M R v Sx) )
lemma ψ_σ : (cflow V M R s v Sx).f = (xflow V M R s v Sx).f:= by have ht(t:Hop V.F):Hop.f (undoV t θ)=Jet.inverse t.f:= rfl; unfold cflow xflow slideOf; simp_rw [ walkF, timely, ht ]
lemma transported : let P:=transfer V M R v Sx; P*cflow V M R s v Sx=(diffuse V M R s v Sx) * glance s P:= by intro P; unfold cflow slideOf; rw [ ← mul_assoc, ← mul_assoc, show P* _=1 from lefto P θ,one_mul ]
lemma ψ_work : (xflow V M R s v Sx).f= ren (Jet.inverse ( Elegant.ξ h V M v R )) ( Elegant.ξ h V M (v-s) R ):= by
    unfold xflow diffuse slideOf; let f t:= ( ηP t ); let g:= f v; let J:=undoV ( f (v-s) ) θ; let J':=undoV g θ;
    have hu : g=ηP v:= rfl; change ( J' * (g * J) * glance s g ).f = _; rw [ ← mul_assoc J', show J'*g=1 from righto g θ,one_mul,walkF ]; congr 1; apply funext; intro n; let S:=Elegant.ξ h V M (v-s) R; have hv: Genuine S:= Sx.lens (v-s); let a:= Jet.inverse S; have ha:Genuine a:= (f (v-s)).loved;
    change inverse a n = S n; obtain hh:= congr_fun (asc ( x:=inverse a ) ( y:=a ) ( Jet.lives _ ) ( Jet.lives _ ) S) n; change ren (inverse a) (ren a S) n= ren (ren (inverse a) a) S n at hh; rw [show ren a S=headway from guarded hv, guarded ha, head_ren (Jet.lives _),ren_head ] at hh; exact hh
end YM.FVA2.Forge
