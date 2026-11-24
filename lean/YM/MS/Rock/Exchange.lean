import YM.MS.Rock.Route
import YM.MS.Heat.Build
/-!
# Dimensional extension of momentum master identities: compact version

All complex spin stencil projections with right factor. `brick` bounds normalized
 Wtr. Extend to full Gaussian later. Fluctuations independent poses. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open Landau Arts Pilot Spin Arc Wire Path
open scoped Topology ContDiff
open Metric
variable {G:Gauge}{I:Type}{b c d:Bool} {m:ℕ}{A B:ℝ}{U V Z:Rip G}{F H:Mob G}
structure Form0 (b:Bool)(F:Mob G): Prop where
   price : kPrice F
   token : Sturdy b F
structure Knot (b:Bool)(F:Rip G): Prop where
   price : rPrice F
   token : Ruddy b F
structure RockB (U:Rip G)(b:Bool): Prop extends Knot b U where
   gear : ∃ B,1≤ B∧ rock B U
-- λ grammar
lemma Form0.sync (h:Form0 b F): Sync b (fun _=>F):=sncf h.price h.token
lemma Knot.stamp (h:Knot b U): Stamp b (fun _=>U):= s_p h.price h.token
lemma RockB.volume0 {f:ℂ→ Mob G}(h:RockB U b)(he:Sync b f): Sync b (fun i=>ocean i U (f i)) := h.gear.elim fun _ hB=> he.ceil h.toKnot.stamp hB.1 (fun _ _=>hB.2)
variable [Fintype I]
lemma Knot.tr {g f:ℂ→Mob G}(h:Knot b U)(hr:reverseF U)(hx:closedF U d)(hf:Sync b f)(hg: Sync b g): Sync b (fun i=>arbor U (f i) (g i)):= hf.tree hg h.stamp (fun _ _=>hx) (fun _ _=>hr)
abbrev sym (F:Mob G): Prop:= ∀ m,Symm (field Landau.parity) (F m)
abbrev tide (F: Mob G): Prop:=∀ m,Pure (field Landau.parity) false (F m)
-- useful
lemma lamp (h:RockB U b){f:ℂ→Mob G}(hf:Sync b f)(n:ℕ): ocean n U (f n) n= Arc.pitch n • Ccy (U n) (f n n) (Px n):= by
   have ht:=hf.eye.kB (Town_nat n); exact funext fun l=> lowN ht h.price (hf.vote _ (Town_nat n)) h.token l
abbrev Paware (n:ℕ) := Px n
-- scale by ℝ in operators
variable (hf:Form0 b F)(hU:RockB U b)(hu:closedF U false)
variable {Q:Shade G}
lemma LinearMapRealm {E:Type}[AddCommMonoid E][Module ℂ E][Module ℝ E][IsScalarTower ℝ ℂ E]
 (L:E→ₗ[ℂ] E)(x:E)(k:ℝ): L (k • x)=k • L x:=map_smul (L.restrictScalars ℝ) ..
include hU hu hf
lemma capA (hz: Priced Q)(hp: CountsD b Q)(hZ: RockB Z b)(hx:∀ n,(Q n).change (U n)=Z n)(s:ℂ)(hs:s∈Town): portZ Q (ocean s U F)+ ocean s Z F=ocean s U (portZ Q F) := by
    let X:=hf.sync; refine Sync.drape (( (hU.volume0 X).port hz hp).add (hZ.volume0 X)) (hU.volume0 ( X.port hz hp)) (fun n=>?_) hs; simp only [Pi.add_apply]; rw [show ocean _ U (portZ Q F) n= _ from lamp hU ( X.port hz hp) n,lamp hZ X]; unfold portZ; rw [show ocean _ U F n= _ from lamp hU X n,LinearMapRealm,← smul_add]; congr 1; rw [← hx]; exact comm_Q (Px n) (Q n) (theory hf.price hU.price n) (by rw [hx]; exact theory hf.price hZ.price n) (hu n)
section bil
variable (hV:RockB V b)(hv:closedF V true)(he:sym F)(s:ℂ)(hs:s∈Town)
include hV hv he hs
omit hV hv he hs hU hu hf in
lemma lap_down (n:ℕ)(U:Ridge G n)(F:Rack G n)(k:ℝ): Ccy U (k • F) (Px n) = k • Ccy U F (Px n):= by funext i; simp_rw [Ccy, LinearMapRealm (trc U _)]; simp_rw [Pi.smul_apply, integral_smul]
lemma capD : ocean s V (ocean s U F)=ocean s U (ocean s V F):= by
   let X:= hf.sync; refine Sync.drape (hV.volume0 (hU.volume0 X)) (hU.volume0 (hV.volume0 X)) (fun n=>?_) hs; rw [show ocean _ V _ n= _ from lamp hV (hU.volume0 X) n, show ocean _ U (ocean (n:ℂ) V F) n= _ from lamp hU (hV.volume0 X) n,lamp hU X,lamp hV X,lap_down,lap_down]; congr 2; rw [comm_T (Px n) (hu n) (hv n) ( theory hf.price hU.price n) (theory hf.price hV.price n) (he n)]; obtain ⟨A,hA,hL⟩:= hU.gear; obtain ⟨B,hB,hW⟩:= hV.gear; exact fun l=> tt_double hf.price hV.price hU.price n l hW hL -- shadow. check congr overshoots
omit hV hv he hs hU hu hf in
lemma bule (K:Ridge G m)(p:Rack G m)(c:ℝ)(u:Rack G m): tree Landau.parity K (c • p) u=c • tree Landau.parity K p u:= LinearMapRealm (boulevard Landau.parity K |>.flip u) p c
omit hV hv he hs hU hu hf in
lemma raceR (K:Ridge G m)(p:Rack G m)(c:ℝ)(u:Rack G m): tree Landau.parity K u (c • p)= c • tree Landau.parity K u p:= LinearMapRealm (boulevard Landau.parity K u) p c
lemma capT (hH:Form0 b H)(hw:sym H)(hp:tide F)(hr:reverseF U)(hP:reverseF V):
    ocean s V (arbor U F H)+arbor V (ocean s U F) H+arbor V F (ocean s U H)=ocean s U (arbor V F H)+arbor U (ocean s V F) H+arbor U F (ocean s V H) := by
   let Cx:= hV.toKnot; let Cy:= hU.toKnot -- metavars for polymorphic volume0 remove
   let P:=hf.sync; let W:=hH.sync; let A:= Cy.tr hr hu P W; let B:= Cx.tr hP hv P W
   refine Sync.drape (((hV.volume0 A).add (Cx.tr hP hv (hU.volume0 P) W)).add (Cx.tr hP hv P (hU.volume0 W))) (((hU.volume0 B).add (Cy.tr hr hu (hV.volume0 P) W)).add (Cy.tr hr hu P (hV.volume0 W))) (fun n=>?_) hs; simp only [Pi.add_apply]; rw [show ocean (n:ℂ) V _ n= _ from lamp hV A n, show ocean (n:ℂ) U (arbor V F H) n= _ from lamp hU B n]; unfold arbor; rw [lamp hU P, lamp hV W, lamp hV P, lamp hU W, bule,bule,raceR,raceR, ← smul_add,← smul_add,← smul_add,← smul_add]; congr 1; obtain ⟨B,hB,hR⟩:=hU.gear; obtain ⟨C,hC,h0⟩:= hV.gear
   exact exchange_term (Px n) (theory hf.price hV.price n) (theory hH.price hV.price n) (theory hf.price hU.price n) (theory hH.price hU.price n) (maintenance hf.price hH.price hU.price hV.price n h0 (hP n)) (maintenance hf.price hH.price hV.price hU.price n hR (hr n)) (hP n) (hr n) (he n) (hw n) (hp n) (hu n) (hv n)
end bil
end YM.MS.Rock
