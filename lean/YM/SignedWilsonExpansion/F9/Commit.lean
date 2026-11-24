import YM.SignedWilsonExpansion.F9.Paste
/-!
# Evaluate after frame and coupling positioning for the whole Reporter vocabulary

The tempo direction of `Tape` is actual bare → *festival gear* on SouthQ (effective clock ℓ). `tangent` real coupling as a formal regulator coupling, not physical.Need ride near one. Keeper.
-/
set_option autoImplicit false
set_option maxHeartbeats 495000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b T N M i j l r d p u n :ℕ}
variable {B Q D Z X Y η t a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
variable {F:Frames G}{H:Hol G}{A':∀ h, Survey G H h}{K:∀ h,Rays G h H}
local notation "Rι"=> (F.level h)
namespace Stair
open Cirrus
open Normalize (Sec Formal reversal_exists)
open Tape
variable (W:Initialize G){A'' :∀ h,Rays G h W.hol}{Ω:Council F}{P':Normalize.Store G}
-- inverse when exists, public. epoch holds Past with h, solve once through height.
def inverseH (V:Normalize.Store G)(x:Mesh)(h:ℕ): Normalize.Guard G h:= if p:Normalize.Formal (Normalize.deck (V.layout W x h)) then (Normalize.reversal_exists p).choose else 1
lemma guardH (x:Mesh)(h:ℕ) : Normalize.Formal (inverseH W P' x h):= by unfold inverseH; split; exact (Normalize.reversal_exists (by assumption)).choose_spec.1; exact Normalize.Formal.one ..
lemma ladderH (x:Mesh)(h:ℕ)(v:Normalize.Formal (Normalize.deck (P'.layout W x h))): let P:= Normalize.deck (P'.layout W x h); inverseH W P' x h*P=1 ∧ P* inverseH W P' x h=1:=by intro P; unfold inverseH; rw [dif_pos v]; exact (Normalize.reversal_exists v).choose_spec.2
local notation "AZ"=> Stair Ω (launch F W.hol W.surveys A'' k) R.draws R.paid m c c h e k u Z
variable (P':Normalize.Store G)(Y:Rose.Pick P')(p': Stair Ω (launch F W.hol W.surveys A'' k) A Ñ m c c h e k u Z)
lemma paid_layout (x:Sample n) (p:Fin n→ Tape (Sec G h))(v:P'.Meets W x.F h): tabular (live W h x) p=tabular (Rose.cooked W P' h x) (fun i=> respond (facet (inverseH W P' x.F h)) (p i)):=by
    let Q:= Normalize.deck (P'.layout W x.F h); let H:= inverseH W P' x.F h; have hx (p:Tape (Sec G h)): respond (facet Q) (respond (facet H) p)= p:=by rw [← respond_mul, (ladderH W _ _ v.1).2, respond_one]
    rw [show Rose.cooked W P' h x=Tape.horizon Q _ from rfl,← Tape.layover]; exact congr_arg (tabular (live W h x)) (funext fun i=> (hx (p i)).symm)
lemma measured_phase (x:Sample n): Rose.measureₓ W Y h x=composed (Rose.cooked W P' h x) (Rose.χ W Y x.F):=by
    let y:= Rose.cooked W P' h x; let z:= Rose.χ W Y x.F; funext i; ext1 p; rw [Rose.measure_paid, Rose.turn_coins]; exact (congr_arg (coeff i) (comp_clock y z (Rose.χzero ..) p)).trans (coeff_mk ..)
lemma measured_head (x:Sample n)(H: Rose.Use W Y x.F): composed (Rose.measureₓ W Y h x) (Rose.chosen W Y x.F)=Rose.cooked W P' h x:=by rw [measured_phase,comp_cover _ _ _ (Rose.χzero ..) (Rose.zero_choice ..), Rose.χverts W Y x.F H,composed_id]
-- fare clock at ℓ.
abbrev starFlight (x:Cost): InkQ:= insertQ (x* PowerSeries.X)
lemma flight_zero (x:Cost): constantCoeff (starFlight x)=0:=by simp [starFlight,insertQ]
lemma flight_sub (x:Cost)(p:InkQ): flyQ x p= p.subst (starFlight x):=by rw [flyQ,aimSh,starFlight,map_mul,map_X]
variable {P'}
abbrev verso (X:Mesh)(A:Levels G)(Ñ:ChartRatio G)(T l c:ℕ): InkQ:=southQ A Ñ T l c (Rose.chosen W Y X)
def lineTape (Q:Normalize.Store G)(x:Mesh)(l:ℕ)(ρ:ℝ)(i:(F.level h).Index): Tape (Sec G h):= tempo (starFlight (relativeF A Ñ c l (c-l))) (respond (facet (inverseH W Q x h)) (p'.bareTape W x ρ i))
variable (q: Stair Ω (launch F W.hol W.surveys A'' k) R.draws R.paid m c c h e k u Z)
-- holds as formal series EXACT for the same certificate clock
lemma commission (x:Sample (n+1))(v:P'.Meets W x.F h)(H:Rose.Use W Y x.F)(L:Fin (n+1)→Cover)(S:ℕ→Cover)(hg:∀ i,chartV x i=wrap x.F.p.side (S c+L i))(f:Fin (n+1)→(F.level h).Index)(ρ:ℝ)(l:ℕ): q.cloudW (W.tree x.F.p) S l L f ρ=tabular (composed (Rose.measureₓ W Y h x) (verso W Y x.F R.draws R.paid c l c)) (fun i=> q.lineTape W P' x.F l ρ (f i)):=by
    unfold cloudW; rw [q.reveals W x _ hg, paid_layout W P' _ _ v, ← measured_head W P' Y x H]; unfold southQ verso; rw [flight_sub,comp_tape _ _ (flight_zero _)]; simp_rw [comp_cover _ _ _ (Rose.zero_choice ..) (flight_zero _),southQ,flight_sub]; rfl
-- ζ realized at ℓ formal. need τ version at r. North, compose Clock.Account.CenterFT
lemma verso_zero (x:Mesh)(A:Levels G)(Ñ:ChartRatio G)(T l c:ℕ): constantCoeff (verso W Y x A Ñ T l c)=0:=by
    unfold verso southQ; rw [flight_sub,← coeff_zero_eq_constantCoeff_apply,FPS.coeff_substituted _ (flight_zero _),zero_add,Finset.range_one,Finset.sum_singleton,coeff_zero_eq_constantCoeff_apply,Rose.zero_choice,zero_smul]
abbrev realInk (Z:InkQ):= PowerSeries.map (starRingEnd ℂ) Z=Z
lemma realZx (Z:Cost): realInk (insertQ Z):= PowerSeries.ext fun i=> by rw [coeff_map,inked]; simp
def WReal (f:Tape (Sec G d)): Prop:=∀ i,Normalize.reel d (f i)=f i -- def
lemma polR (V:InkQ) (h:realInk V)(k:ℕ): realInk (V^k):=by unfold realInk at *; rw [map_pow,h]
lemma realLevel (Z:InkQ)(p:realInk Z)(k:ℕ): star (coeff k Z)=coeff k Z:= by unfold realInk at p; exact ((coeff_map ..).symm).trans (congr_arg _ p)
lemma verso_real (x:Mesh)(A:Levels G)(Ñ:ChartRatio G)(T l c:ℕ): realInk (verso W Y x A Ñ T l c):=by
    have hv : PowerSeries.map (starRingEnd ℂ) (Rose.chosen W Y x)=Rose.chosen W Y x:= PowerSeries.ext fun i=> (coeff_map ..).trans (Rose.real_c ..)
    unfold realInk verso southQ; rw [flight_sub,FPS.substitute_ringHom (starRingEnd ℂ) _ (flight_zero _), hv, show ∀ p:Cost,PowerSeries.map (starRingEnd ℂ) (starFlight p)=_ from (fun x=>realZx _)] -- type
lemma flight_one (p:InkQ)(h:constantCoeff p=0) (x:Cost)(v:constantCoeff x=1): coeff 1 (flyQ x p)=coeff 1 p:=by
    rw [flight_sub,FPS.coeff_substituted _ (flight_zero _),Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, coeff_zero_eq_constantCoeff_apply,h,zero_smul, zero_add, pow_one]; rw [starFlight,inked, show coeff 1 (x* PowerSeries.X)= coeff 0 x from (?_), coeff_zero_eq_constantCoeff_apply,v,Complex.ofReal_one, smul_eq_mul,mul_one]; simpa only [pow_one] using coeff_mul_X_pow x 1 0 -- check order
lemma verso_one (x:Mesh)(A:Levels G)(Ñ:ChartRatio G)(h:l≤c)(g:G.Simple)(p: LocalRatio Ñ): coeff 1 (verso W Y x A Ñ c l c)= coeff 1 (Rose.chosen W Y x):= flight_one _ (Rose.zero_choice ..) _ (angularF g p (by omega))
end Stair
end YM.WilsonCoeffUV.Mer.Xa
