import YM.MatchingLedger.Compass.Pine
import YM.UVExtension.Oasis.Flora
/-! # Couple to exactly the Earth's rotation
  Answer is delivered on the actual path, every cutoff, period. No phase renaming permitted here,
  can compose with requests before activating. Include exact torque on ALL real shooting
  representatives of the `Floral` port in its real domain explicitly. Constituent pricing
  via the beta-germ program Uses plates; issue explicitly in these coordinates BEFORE
  field valuations. -/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Compass.Sail
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat
open Progress.DirectedRecipe MeasureTheory Push Push.AbsoluteSums
open RG.Supply Precision RG.Shoot Org Input
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext Mallow
open WilsonStartup Time Next.Foundations UVNext.CouplingReset Legato
open UVExtension Dales Camp Mast Spire Oasis Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge}

def allot (x:ℝ) := x ^ (-(8/100):ℝ)
structure Profile (C:Family G) (X: MatchingLedger.Compass.Harvest C.path.levels) : Prop where
   fromBooks: Supply.AsDivisors C.S
   planned : ∃ P:ChartRatio G, LocalRatio P ∧ ∃ V: Crop C.path.levels, V.Fires P ∧ V.harvest=X ∧
       UVExtension.Reward.Ends C.path.levels V.model V.alpha ∧ ∀ n p k:ℕ,k≤n→ V.model n k=(C.path.rep n p k).path
   turn (N m p:ℕ)(he:m<N) :
       ‖C.path.β N p m-C.path.β N p (m+1)-X.alpha N m‖ ≤ allot (C.path.levels.clock.hatBeta (m+1))
   drift (N m:ℕ)(he:m<N): |X.alpha N m+G.slopeConstant*Real.log (C.S.block m).val| + 1 ≤ (C.path.levels.params (m+1)).drift

lemma modeFee {hG:G.Simple}{X:Metals G}{D:Rolls X.p}{A: Alloy X D}{Q:Factor A}(S:Uses Q hG)
    {b:ℝ}(h:(b:ℂ)∈Broad A.B.a){N m:ℕ}(hx:m<N)(p:ℕ) :
    ‖(S.realBeat b N p m).beta-(S.realBeat b N p (m+1)).beta-A.B.kin.alpha N m‖ ≤ allot (A.B.a.clock.hatBeta (m+1)):=by
  let V:= S.cart N p; let q := S.grove.coins; let H := S.fits N p
  have he := H.acts V (S.token N p) q h
  have hh := Fitted.plates S.grove.enabled S.grove.climbed H he.1 h he.2 m hx.le; let f(m'):= H.Third V q b m'; let z:= (hh.2 hx)
  have hv := (H.doors he.1 m hx).1
  let t:= Tour.bonus Q (H.charts m hx) _ (he.1.alive _ hx)
  change f m = f (m+1)+A.B.kin.alpha N m+t at hv
  rw [show (S.realBeat b N p m).beta-(S.realBeat b N p (m+1)).beta-A.B.kin.alpha N m=t from (by change f m-f (m+1)- _=_; linarith only [hv])]; exact hh.2 hx

lemma works {C:Family G}{H:G.Simple}(h: Floral (hG:=H) C) : ∃ M:MatchingLedger.Compass.Harvest C.path.levels, Profile C M:=by
  obtain ⟨M,P,A,R,S,T,t,K,w,Q,L,u,rfl,-,_,-,-,-,-⟩:= h
  let Z:= Crop.flowers A.B.kin; let X:=Z.harvest
  refine ⟨X,⟨R.floor,⟨M.O,A.B.ratio,Z,Crop.importsC A.B.kin A.B.support,rfl,u.fields, fun n p k (_:k≤n)=> rfl⟩,fun N m p he=> ?_,fun N m he=>?_⟩⟩
  · change ‖(S.realBeat 0 N p m).beta-(S.realBeat 0 N p (m+1)).beta-X.alpha N m‖ ≤ allot (A.B.a.clock.hatBeta (m+1)); rw [show X.alpha N m= _ from (if_pos he : X.alpha N m=A.B.kin.alpha N m)]; exact modeFee S (Uses.centerP _) he p
  rw [show X.alpha N m= _ from (if_pos he : X.alpha N m=A.B.kin.alpha N m)]; exact A.B.support.kinetic N m he
lemma Profile.admission {C:Family G}{X} (h:Profile C X) : Reaps C.path.levels X:= by obtain ⟨p,hp,V,hV,hA,_⟩:= h.planned; exact ⟨p,hp,V,hV,hA⟩
lemma joins {C:Family G}{H:G.Simple}(h: Floral (hG:=H) C) : ∃ (T: MatchingLedger.Compass.Harvest C.path.levels),Reaps C.path.levels T ∧ ∀ U, Reaps C.path.levels U→ T= U ∧ Profile C U:=by
   obtain ⟨M,hM⟩:=works h
   refine ⟨M,hM.admission,fun i hi=>?_⟩; have he:= standard G hM.fromBooks H M i hM.admission hi
   exact ⟨he,he ▸ hM⟩
end YM.MatchingLedger.Compass.Sail
