import YM.RG12.Joint.Stack
import YM.RG20.Tune
import YM.RG20.Leaf
/-!
# Reserve at every rung of every Keys/Cellar fixed history
Source adapted from UVExtension/Rainfall/Planet.lean (flock). Re-specialize and re-check against
the UV Rama (Rainfall/Lacing) data; no identification of independent witnesses. See ledger.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Mast
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {hG:G.Simple} {M:Metals G} {P:Rolls M.p} {A:Alloy M P} {X:Roost.Factor A} (S: Uses X hG) (v:Keys S) {C:ℕ→ℝ} {W:Bid.Worth}(R:Legato.Bandage X C W)
    (d N m n:ℕ) (z:Rose S)
set_option quotPrecheck false
local notation "D!"=> Orchard.roof S v
local notation "H"=> Orchard.Path S v
local notation "T"=> A.B.a
local notation "F"=> (frames G).level d
local notation "π"=> localSection G d
local notation "O!"=> hol G
local notation "sT"=> Legato.Bandage.waybill (A.B.a)
local notation "L!"=> Lacing.Banner («H»:=T) (F) (p:=n) (A:=hol G) m
variable (L': Lacing.Banner A.B.a ((frames G).level d) (hol G) n m)
local notation "c0"=> S.realBeat z.val N n m
local notation "c1"=> S.realBeat z.val N n (m+1)
variable (hm:m<N)(hd:d+3≤ A.B.a.clock.J m)
local notation "K0"=> (ray S N n m z hm).body
local notation "g0"=> S.realBeat (v N n).val N n (m+1)
local notation "K1"=> (ray S N n m (v N n) hm).body
local notation "Φ"=> Keeper.sufficient (slots0 S N m n z hm)
local notation "Υ"=> slots1 S N m n z hm
local notation "Υ1"=> slots1 S N m n (v N n) hm
local notation "Φ1"=> Keeper.sufficient (slots0 S N m n (v N n) hm)
local notation "V1"=> readC S R d N m n (v N n) hd
local notation "cF"=> C (A.B.a.clock.J (m+1))
set_option maxHeartbeats 640000 in
lemma flock20 (h: Waged K1 beam0 V1 Υ1 Φ1 L') : ∃ K:Set Wing,K.Finite ∧ ∃ T':Heading F, ∃ K': Keeper ((H).rep N n (m+1)).p ((H).rep N n (m+1)).activities, Manor20 π H N n m (hol G) K' (D! N n m hm) K L' T' cF
      (Doors.rate ((T).S.block m)) (sT m) :=by
    have hv:=(housed S v); let t:= (A.B.a.params (m+1)).columns; let i:=A.B.a.clock.J m; let j:=A.B.a.clock.J (m+1); have hx:= step_paid A.B.a m; have hh:d≤ i:= (le_trans (Nat.le_add_right d _) hd)
    have hC : Buys H F W m cF (Doors.rate ((T).S.block m)):= R.clock.fits H rfl m d hh
    have he' : (H).S.block m=P.L j:= Push.PriceCompiler.block_eq A.B.valid m
    have hu : sT m = 2*(Real.exp (g0).p.supportExponent* Cub.title G (M.p.profile j)):=by unfold waybill; rw [params_eq A.B.valid]; rfl
    obtain ⟨Q,hQ,T',ht⟩:= pomp20 hm R.songs R.PStage R.wait (Graces.feet hd R.clock) hv R.r K1 beam0 (ponds S N n m (v N n) hm) rfl hG R.tunes R.furthering R.corners R.shape R.clock R.stamp V1 Υ1 Φ1 h hd
    rw [← hu] at ht
    rw [show (T).S.block m=P.L j from he']
    exact ⟨Q,hQ,T',_, Rainfall.seat20 π (Vintage.YM.Extra.Histories.Issue.trail (ministry S v)) N n m (hol G) g0 _ _ Q _ _ (ponds S N n m (v N n) hm) rfl L' _ he' ht HEq.rfl⟩


lemma strongerPass (hm':m<N)(hd':d+3≤ (T).clock.J m):
    ∃ K:Set Wing,K.Finite ∧ ∃ T':Heading F, ∃ K': Keeper ((H).rep N n (m+1)).p ((H).rep N n (m+1)).activities,
      Manor20 π H N n m (hol G) K' (D! N n m hm') K (tide S R d N m n (v N n)) T' cF
           (Doors.rate ((T).S.block m)) (sT m) ∧
      0 ≤ sT m := by
    have h := flock20 S v R d N m n (tide S R d N m n (v N n)) hm' hd' (follows (hm:=hm') (hd:=hd') ..)
    obtain ⟨K,hK,t,K',hx⟩:= h
    refine ⟨K,hK,t,K',hx,mul_nonneg zero_le_two (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans ?_))⟩
    exact title_one ..

-- place reserve on same Lyrics now. Level response witnessed independently in the reserve,
-- but attached to the same raw input (not just an additive continuation density).
set_option maxHeartbeats 500000 in
lemma transmission20 {r : ℕ} {L:Music ((frames G).level d) (Orchard.Path S v) N n}
    (hL:Lyrics S v (W:=W) d N n r (fun i _ => tide S R d N i n (v N n)) L) (hm:m < N)
    (hr:r ≤ m) (he:d+3 ≤ A.B.a.clock.J m) :
    ∃ V: Voice F H n m, Heard π H N n (hol G) m V ∧ Responds π H N n W m (L.tone (m+1)) V ∧ Chorus H N n m V ∧ Carol π H N n m (D! N n m hm) (L.tone (m+1)) V (sT m) ∧
      ∀ x, Blown (V.plays x) 0 ((H).rep N n m) (V.charge x) ∧ Lacing.Face H N n (hol G) m (L.tone m) x = Lacing.Face H N n (hol G) m V x := by
   obtain ⟨K,hK,T',K',hx,hU⟩ := strongerPass S v R d N m n hm he
   have h:= Orchard.selected S v
   have hs:= hL.earned; have he' := hs.earned _ (hr.trans (Nat.le_succ _)) hm
   have hSq: Chorus H N n (m+1) (L.tone _):=by
       by_cases hh:m+1=N
       · rw [hh,hL.head]
         have ht := hs.head; rw [hL.head] at ht
         exact Vintage.YM.MergeProof.voice π H N n _ _ d h (sound ..) ht
       exact (hL.comes (m+1) (hr.trans (Nat.le_succ _)) (by omega)).2.1
   obtain ⟨V,hv,hT,hX,hZ,hY,hC⟩ := Lacing.repriseQ20 π H N n (hol G) W m (L.tone _) h hm he' R.clock.room R.clock.bank T' (D! N n m hm) K hU hK (glyphBound (A.B.a) (m+1)).2 (R.clock.fits H rfl m d ((Nat.le_add_right d 3).trans he)) K' _ hx hSq (sound ..) (fun U=> (Vintage.YM.Extra.Histories.Tour.bright H h N n _ hm U).ne')
   exact ⟨V,hv,hT,hX,hC, fun x=> ⟨hY x, ((hL.comes m hr hm).2.2 x).trans (hZ x).symm⟩⟩

variable {L:Music ((frames G).level d) (Orchard.Path S v) N n}
-- directly on ANY chosen cantors Witness
lemma kills20 {r:ℕ} (hL:Lyrics S v (W:=W) d N n r (fun i _=> tide S R d N i n (v N n)) L) (hm:m < N) (hr:r ≤ m)
    (he:d+3≤ A.B.a.clock.J m) (x:(F).Coeff) :
    let P':=(L.tone m).plays x
    Blown P' 0 ((H).rep N n m) ((A.B.a.params m).columns*(F).coeffSize ((F).core P'.x)) := by
   obtain ⟨V,hv,-,-,-,hA⟩:= transmission20 S v R d N m n hL hm hr he
   intro P'; let Z:= V.plays x; let R':= (H).rep N n m
   let b:=(A.B.a.params m).columns; let c:=Real.sqrt (A.B.a.clock.forcedAllowance m)
   have hT: Nonempty (Keeper R'.p R'.activities) := ⟨Keeper.sufficient (Vintage.YM.PhysicalNext.Repeat.Graces.Nest.samples hG (housed ..) N m n hm.le)⟩
   obtain ⟨hC,hY⟩:= hv.earns x; obtain ⟨hS,hZ⟩:= (hL.earned.earned _ hr hm.le).earns x
   obtain ⟨hV,hF⟩ := hA x; have hz: V.index x= P'.x := (hv.currents x).symm.trans (RG20.seeIndex (show Eye Z (hol G) R' c=Eye P' (hol G) R' c from hF.symm))
   have ht: Blown P' 0 R' (V.charge x):= RG20.seeBlown ⟨hT,hC,_,hY⟩ ⟨hT,hS,_,hZ⟩ (show Eye Z (hol G) R' c= Eye P' (hol G) R' c from hF.symm) hV
   exact ht.enlarge (hz ▸ hv.cone x)

section choice
variable {Bt:Org.Bolt A}(a:Upland.Arc X S Bt)(t:ℕ→ℕ)(hh:Lisle t A.B.a)
local notation "C'"=> Cellar.yard v (cellar S R a t hh)
lemma spares20 (hm: t d ≤ m) (hN:m<N) (x:((frames G).level d).Coeff) :
   let P':=((C').factory d N n).entries m x
   Blown P' 0 ((C').path.rep N n m) ((A.B.a.params m).columns*(F).coeffSize ((F).core P'.x)):=by
   intro Z; let U:= cellar S R a t hh; let L:= U.cantors v d n; let f:= L.song N
   have hl:= L.lyr N (hm.trans hN.le)
   have hF : Z=(f.tone m).plays x:=by
     change (Cellar.gate v U d N n).entries .. = _
     rw [Cellar.gate,((Cellar.launch v U d N n).choose_spec (hm.trans hN.le)).2]; rfl
   rw [hF]; exact kills20 S v R d N m n hl hN hm ((U.posts _).trans (A.B.a.fits.mono hm)) x
end choice
end YM.UVExtension.Mast
