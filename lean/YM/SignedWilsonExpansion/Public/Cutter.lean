import YM.SignedWilsonExpansion.Public.Dazzle
import YM.SignedWilsonExpansion.Kane.Cancel
/-! # Proper faces. Finite true masks (through own caps/layout refs in Accounts) represent literally normalized smaller moments. After regulator removals the same calculation **can be written in arity n+1 with units or by any single-slot deletion, both before or after the compensated pure-degree choice** (with the projection eventually taken for each horizon); so the forecast for measured-clock moments at the proper faces really is that for the smaller words with UNCHANGED frames. Iterate freely. Including nullary. This does NOT claim exact numerical equality of the projection forecast at finite physical or diagram cut (bounds & erasure instead). Use the original joint test over the ball whenever comparing terms (f.applyTo). -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Answer.ContinuumLimit
open Lattice RG MeasureTheory Function Filter Wilson Integration Integration.Election Climb Extraction Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open MS MS.High MS.Native MS.Land MS.Fleet PhysMS PhysMS.Frame Next.UVStress Order Spin OPE OPE.Orbits
open FVA2 FVA2.Register FVA2.Scale.Level FVA2.Scale SignedWilsonExpansion SignedWilsonExpansion.Belle SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Asymptotics WilsonPositionHomogeneousComparison
open PowerSeries XSpace.Cirrus Entree Future
open scoped BigOperators Classical ContDiff Topology
universe u
namespace Vision
variable {G:Gauge}{H:G.Simple}{e:Axis}{ε:ℝ}{O:OrderS G}{E:Construction.{u} H ε e O}{ξ:Extraction.Order}{V:Vision E ξ}
variable {Z:WilsonPrescription G}{dial:Bool}{Q:Perspective H Z dial}
open Frames Frames.Cortex Dancer
open PowerSeries Scale Jury WilsonCoeffUV.Mer.Xa MarqueQ Crops
variable (M:Garnishes V Q){t a:Bool}
variable {n d b:ℕ}
local notation "Ξ₀"=> ( V.T Z )
local notation "θ"=> ( Lamplight Z a d )
include M
-- auxiliary uniqueness consequence, for none only. Collect predictor price even in Position world from ANY coefficient of outlook/start. Does not shift to Post to talk about masks.
lemma forecastP0 (b:ℕ)(x:Scale.Stage n)(u:Tags G d n) : (fun i:ℝ=> Act Z V a none i d n x.val u- ∑ j∈Finset.range (b+1), (Ξ₀ i:ℂ)^j * ( θ n x j u ))=o[trail] (Ξ₀ ^ b) :=by
     have hp : Serves trail (fun i y=> Act Z V a none i d n y u) (fun i y=> Path.mote ( Lamplight Z a d ) b y (Ξ₀ i) u) {x.val} (Ξ₀ ^ b):=by
         have hx:Roi {x.val}:= ⟨ isCompact_singleton,Set.singleton_subset_iff.mpr x.property⟩
         cases a; exact M.accounts.position d b (fun _=>none) id tendsto_id {x.val} hx u; let D:= V.pupil; exact Frames.alert D.last D.J D.VFrame.2 Z Q.matching id tendsto_id M.accounts.calibrated.calendar (D.WFrame Z.store) D.VFrame.1 V.sc D.foundation d n b u (fun _=>none) hx -- D.WFrame needs Z.store param
     exact ( hp.read ( u:=fun _=>x.val ) ( Eventually.of_forall fun _=> Set.mem_singleton _ ) ).congr_left fun i=>by unfold Path.mote; simp_rw [ Jury.exactC θ x ]
-- generic uniqueness lemma. physically equal eventually ⇒ both sequences agree (Wilson match then any ν). Can use between different arities & either position & pure (leaf stays unit), heterogeneous projection investigate wanted.
lemma forecastsPay {m d':ℕ}(x:Scale.Stage n)(u: Tags G d n)(y:Scale.Stage m)(v:Tags G d' m)(h:∀ᶠ i in trail, Act Z V a none i d n x.val u= Act Z V t none i d' m y.val v): θ n x b u= Lamplight Z t d' m y b v:=by
     set Pstr:= fun b=>θ n x b u; set χ:= fun i=> Lamplight Z t d' m y i v; refine congr_fun ( billZero Ξ₀ ( M.accounts.calibrated.calendar.clock.positive ) Pstr χ (?_) ) b -- check binder names
     intro b'; refine (( forecastP0 M (a:=t) b' y v ).sub ( forecastP0 M (a:=a) b' x u )).congr' (?_) EventuallyEq.rfl; filter_upwards [h] with i hi; rw [←hi]; unfold χ Pstr; simp_rw [ _root_.mul_sub, Finset.sum_sub_distrib ]; abel
abbrev ZeroTag (d:ℕ):= Normalize.leaf G d
-- orientation finite support leaves exact with arbitrary face. Smaller one keeps same cap words. Include explicit masks reindexing to avoid conflating separate profiles.
abbrev curtain (i:Fin (n+1))(p:Finset (Fin (n+1))): Finset (Fin n) := Finset.univ.filter ( fun j=>i.succAbove j∈p )
abbrev land (v:Tags G d n)(p: Finset (Fin n)) : Tags G d n:= coversB (fun _=>d) p v
abbrev slide (i:Fin (n+1))(u: Tags G d (n+1)):= u ∘ i.succAbove
omit M in
lemma maskT (i:Fin (n+1))(p:Finset (Fin (n+1)))(u: Tags G d (n+1))(q:i∉p): land u p=i.insertNth ( ZeroTag (G:=G) d ) ( land ( slide i u ) ( curtain i p ) ):=by
     funext j; induction j using Fin.succAboveCases i <;> simp [land,coversB,q,ZeroTag,curtain,slide] -- likely finishes earlier
lemma cutScene (a:Bool) : ∀ᶠ r in trail,∀ (X:Peers V) (i:Fin (n+1))(x:Scale.Stage (n+1))(v:Tags G d n), Act Z V a X r d (n+1) x.val ( i.insertNth (ZeroTag (G:=G) d) v )= Act Z V a X r d n ( ease i x ).val v:=by
     have hp : ∀ᶠ r in trail, walk ( slotW Z V a ) r d ( Normalize.leaf G d )= V.pupil.S.unit d:=by
         cases a; exact ( M.accounts.calibrated.spin d ).1.mono fun i hi=> hi.1; exact ( M.accounts.calibrated.spin d ).2.mono fun i hi=> hi.1
     filter_upwards [hp,self_mem_nhdsWithin] with i hi ht Y j x v; exact Frames.deleted V.pupil.last ( slotW Z V a ) d ht _ hi j v x Y
lemma maskForecast (a:Bool)(i:Fin (n+1))(p:Finset (Fin (n+1)))(q:i∉p)(v:Tags G d (n+1))(x:Scale.Stage (n+1)): Lamplight Z a d (n+1) x b ( land v p ) = Lamplight Z a d n ( ease i x ) b ( land ( slide i v ) (curtain i p) ):= forecastsPay M _ _ _ _ (( cutScene M a ).mono fun j hj=> (by rw [ maskT i p v q, hj ]))
-- exactly empty (with NO lottery tag). Also used at n>0 all units. omit uniqueness between ν (independent ν vanishes via powderMatches).
omit M in
lemma vacuumAct (r:ℝ)(v:Tags G d 0)(x:Points 0)(q:Peers V): Act Z V a q r d 0 x v=1:=by let T:= fun i:Fin 0=> V.pupil.S.representative d ( walk (slotW Z V a) r d ( v i )); exact (spectate V.pupil.last q).laws.trivial (fun i=>⟨ d,T i ⟩) (r•x)
lemma nullaryGives (a:Bool)(b:ℕ)(v:Tags G d 0)(x:Scale.Stage 0) : Lamplight Z a d 0 x b v=if b=0 then 1 else 0:=by
      let Δ(i:ℕ):ℂ:= if i=0 then 1 else 0; let Pstr:= fun b=> Lamplight Z a d 0 x b v; refine congr_fun ( billZero Ξ₀ ( M.accounts.calibrated.calendar.clock.positive ) Pstr Δ (?_) ) b; intro k; exact ( forecastP0 M (a:=a) k x v |>.neg_left ).congr_left fun i=> by rw [ vacuumAct ]; unfold Pstr; simp_rw [ _root_.mul_sub,Finset.sum_sub_distrib ]; rw [ Finset.sum_eq_single 0 (f:=fun j=>(Ξ₀ i:ℂ)^j*Δ j) ]; simp[Δ]; (intro j h u; simp[u,Δ]); simp
lemma emptyOf (a:Bool)(b n d:ℕ)(x:Scale.Stage n)(v: Tags G d n): Lamplight Z a d n x b ( land v ∅ ) =if b=0 then 1 else 0:=by
     induction n with
     | zero=> exact nullaryGives M a b (land v ∅) x
     | succ n ih=>rw [ maskForecast M a (0:Fin (n+1)) ∅ (by simp) v,curtain,show (Finset.univ.filter _) = (∅:Finset (Fin n)) from ?_ ]; exact ih _ _; simp -- check ?_

-- now for museum cap layouts. Important each omitted slot still a `Fin(n+1)` tag, cuts only under marker absent.
lemma horizonNeutral {d':ℕ}(x:Scale.Stage n)(w:Caps n)(p:∀i,w i≤d)(t:∀i,w i≤d')(z:∀i,Sec G ( w i )):
    Lamplight Z a d n x b (Frames.toView w d p G z)= Lamplight Z a d' n x b (Frames.toView w d' t G z):=by
    apply forecastsPay M; filter_upwards [ boot_rise M ( r:=id ) tendsto_id w p a,boot_rise M ( r:=id ) tendsto_id w t a ] with r hr ht; exact ( hr none x z ).symm.trans ( ht none x z )
variable (i:Fin (n+1))(w:Caps (n+1))(p:Finset (Fin (n+1)))(c:∀j,w j≤d)
abbrev capSlide:Caps n:= w ∘ i.succAbove
local notation "wc*"=> ( capSlide i w )
abbrev slideSec (v:∀ j:Fin (n+1), Sec G ( w j )) : ∀ j:Fin n,Sec G (capSlide i w j):= fun j=> v (i.succAbove j)
variable (v:∀j:Fin (n+1),Sec G (w j))
omit M
lemma MaskHorizon {n:ℕ}(w:Caps n)(c:∀j,w j≤d)(v:∀j:Fin n, Sec G ( w j ))(p:Finset (Fin n)) : Frames.toView w d c G (coversB w p v)= land (Frames.toView w d c G v) p:=by
   funext j; by_cases h:j∈p; simp[h,coversB,land,Frames.toView]; simp only [land,coversB,h,if_false,Frames.toView]; rfl
local notation "mC*"=> ( fun j=> c ( i.succAbove j ) )

local notation "vc*"=> ( slideSec i w v )
include M c
lemma lifeCancel (a:Bool) (h:i∉p) : ∀ᶠ r in trail,∀ (X:Peers V)(x:Scale.Stage (n+1))(v:∀j:Fin (n+1),Sec G (w j)), Life Z V a r w ( coversB w p v ) x.val X=Life Z V a r wc* ( coversB wc* ( curtain i p ) (slideSec i w v) ) ( ease i x ).val X:=by
   filter_upwards [ boot_rise M (r:=id) tendsto_id w c a,boot_rise M (r:=id) tendsto_id wc* mC* a,cutScene M ( n:=n ) ( d:=d ) a ] with r hr ht hc y x v
   rw [ ←id_eq r, hr,ht y ( ease i x ), MaskHorizon,MaskHorizon, maskT i p _ h]; exact hc y i x _ -- check syntax
lemma lifeForecast (h:i∉p)(x: Scale.Stage (n+1)): Lamplight Z a d (n+1) x b (Frames.toView w d c G ( coversB w p v ))= Lamplight Z a d n ( ease i x ) b (Frames.toView wc* d mC* G (coversB wc* ( curtain i p ) vc* )):=by
   rw [ MaskHorizon, MaskHorizon ]; exact maskForecast M a i p h _ x


end Vision
end YM.Answer.ContinuumLimit
