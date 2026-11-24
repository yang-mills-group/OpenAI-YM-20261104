import YM.Integration.WilsonIndependentMovingRosterStableSale
import YM.Integration.WilsonIndependentMovingRosterStableEdge
import YM.Integration.WilsonIndependentMovingRosterStableMoney
import YM.Integration.WilsonIndependentMovingRosterLaneEdge
import YM.Integration.WilsonSeparatedPrefixMovingUnformed

/-! The genuine two-home first join consumes only the two single-field
receipts on this edge. The quiet keeps the microscopic age N in every case. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedPivotTailLocalSale
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open WilsonCoeffUV.Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedRosterLane (Lane)
open WilsonIndependentMatchedRosterTariff (offer)
open WilsonIndependentMovingRosterStableRoots (front)
open WilsonIndependentMovingRosterLaneEdge (OnEdge)
open WilsonIndependentMovingRosterStableMoney (fees)
open WilsonIndependentMatchedCoverProfile (Income)
open scoped BigOperators Topology Classical

variable {G:Gauge}{n e k u b i N:ℕ}{D:Fin ((n+1)+1)→ℕ}{E W:Credit}
open WilsonIndependentMovingRosterStableSale (homes centers)

theorem original (R:Realm G (e+1) E)(sale:SpringD R k u b W)(t m:ℕ)
    (_h:t ≤ m)(jm:m ≤ i)(ending:i < N)(live:R.anchor ≤ i)
    (l d w:Fin ((n+1)+1)→ℕ)(room:(∑s,l s) ≤ k)(φ:(s:Fin ((n+1)+1))→Rarity (D s))
    (A B:Fin ((n+1)+1)→ℝ)(y z gap:ℝ)(o:CellR)(P:Fin ((n+1)+1)→ℕ→Era G ℝ):
    let T:=paceT R.draws.S m t
    let x:=paceT R.draws.S m (i+1)
    let r:=paceT R.draws.S m i
    let δ:=paceT R.draws.S m N
    let Y:=fun s=>P s (i+1-homes t m s)
    1≤T → 0<gap → (∀s,0≤A s) → (∀s,Amplitude (φ s) (B s)) →
    (∀s,radiusH (φ s) 1 (centers y T s)≤z) →
    (∀a c:Fin (n+1),a≠c→ClearDay (φ a.succ) (φ c.succ) gap) →
    (∀a:Fin (n+1),∀p∈tsupport (φ a.succ).ψ.val,∀q∈tsupport (φ 0).ψ.val,gap≤dist p (T • q)) →
    (∀s,OnEdge R (l s) u b (homes t m s) N i (φ s) (centers y T s) o (P s)
      (fees u b d w A B z δ x T s)) →
    let J:=DeltaGap R.draws R.paid i N Y l
    Auth (∑s,l s) J ∧ Flush e u r J
      (T^(d 0+u+u)*((n+1:ℕ)*R.cash (priceWG G e k u b E W) i*pearlB u b (4*z) (gap/r)*
        nuP (coinMat k e+1) (n+1) (fun s=>offer u b (d s) (w s) z δ x (A s) (B s)))):=by
  intro T x r δ Y zoom apart positive tests caps close separated receipts J
  let Q:=ll R.draws i
  let pay:=fees u b d w A B z δ x T
  have schedule (j:ℕ):paceT R.draws.S t j=paceT R.draws.S m j/T:=
    WilsonSeparatedPrefixMovingUnformed.rulers _ _ _ _
  have day:x*Q.L.val=r:=pace_step R.draws.S m i
  have rp:0<r:=pace_pos ..
  have xp:0<x:=pace_pos ..
  have dp:0<δ:=pace_pos ..
  have zp:0≤z:=(zero_le_one.trans (fieldCap ..)).trans (caps 0)
  let roots:=front Q (fun a:Fin (n+1)=>φ a.succ) (φ 0) x y T o
  have inKeep (s):Income (Y s) (l s) e (u+b) (fun a=>roots s (parentC Q.L a)) (pay s):=by
    have heard:=(receipts s).input
    induction s using Fin.cases with
    | zero=>simpa only [Y,roots,x,Q,front,homes,WilsonIndependentMovingRosterStableSale.centers,Fin.cons_zero,schedule] using heard
    | succ s=>exact heard
  have outKeep (s):Flush e u (Fin.cons (α:=fun _=>ℝ) (r/T) (fun _:Fin (n+1)=>r) s)
      (verseI R.draws R.paid i N (l s) (Y s)) (pay s):=by
    have heard:=(receipts s).coarse
    induction s using Fin.cases with
    | zero=>simpa only [Y,r,homes,Fin.cons_zero,schedule] using heard
    | succ s=>exact heard
  let target:=T^(d 0+u+u)*((n+1:ℕ)*R.cash (priceWG G e k u b E W) i*
    pearlB u b (4*z) (gap/r)*nuP (coinMat k e+1) (n+1) (fun s=>offer u b (d s) (w s) z δ x (A s) (B s)))
  by_cases active:∀s,(VisitsT (φ s) (paceT R.draws.S (homes t m s) (i+1)) (centers y T s) o).Nonempty
  · have atFar:(VisitsT (φ 0) (x/T) (y/T) o).Nonempty:=by
      simpa only [homes,WilsonIndependentMovingRosterStableSale.centers,Fin.cons_zero,schedule] using active 0
    have atNear (a:Fin (n+1)):(VisitsT (φ a.succ) x y o).Nonempty:=active a.succ
    have full:x*Q.L.val≤1:=day ▸ pace_le R.draws.S jm
    have high (a:Fin (n+1)):radiusH (φ a.succ) (x*Q.L.val) y≤z:=
      WilsonIndependentMatchedRosterDate.radius _ (day.symm ▸ rp) full (caps a.succ)
    have low:radiusH (φ 0) ((x/T)*Q.L.val) (y/T)≤z:=by
      have tp:0<T:=zero_lt_one.trans_le zoom
      have eqn:(x/T)*Q.L.val=(x*Q.L.val)/T:=by ring
      rw [eqn]
      exact WilsonIndependentMatchedRosterDate.radius _ (div_pos (day.symm ▸ rp) tp)
        ((div_le_self (day.symm ▸ rp.le) zoom).trans full) (caps 0)
    have coarseKeep (s):Flush e u
        (Fin.cons (α:=fun _=>ℝ) ((x*Q.L.val)/T) (fun _:Fin (n+1)=>x*Q.L.val) s)
        (verseI R.draws R.paid i N (l s) (Y s)) (pay s):=by
      rw [day]
      exact outKeep s
    have raw:=WilsonIndependentMovingRosterStableEdge.original R sale live ending l room
      (fun a:Fin (n+1)=>φ a.succ) (φ 0) x y T gap z z o xp zoom full apart close separated high low
      atNear atFar Y pay inKeep coarseKeep
    have known:=raw.2
    change Flush e u (x*Q.L.val) J (((n+1:ℕ):ℝ)*R.cash (priceWG G e k u b E W) i*
      (pearlB u b (4*max z (T*z)) (gap/(x*Q.L.val))*
       nuP (coinMat k e+1) (n+1) (Fin.cons (α:=fun _=>ℝ) (T^u*pay 0) (Fin.tail pay)))) at known
    rw [day] at known
    have money:=WilsonIndependentMovingRosterStableMoney.original u b d w A B δ x T z (gap/r)
      (coinMat k e+1) zoom zp
    dsimp only at money
    dsimp only [pay] at known
    rw [money] at known
    refine ⟨raw.1,?_⟩
    convert known using 1
    ring
  · obtain ⟨s,empty⟩:=not_forall.mp active
    have none:=WilsonIndependentMatchedRosterEdge.absent R ending Y l s ((receipts s).absent empty)
    change J=0 at none
    rw [none]
    have income:0≤target:=by
      have vv:=loadN (coinMat k e+1) (n+1) (fun s=>offer u b (d s) (w s) z δ x (A s) (B s))
        (by have h₀:=coinMat_nn k e;linarith)
        (fun s=>WilsonIndependentMatchedRosterTariff.positive _ _ _ _ zp dp.le xp.le (positive s) (tests s).1)
      have tag:=zero_le_one.trans ((priceWG G e k u b E W).purchase (R.depth i live))
      dsimp [target,pearlB];positivity
    let zero:=Fringed.nullV (G:=G) (k:=∑s,l s) (e:=e) (u:=u) (η:=r) (δ:=0) le_rfl income
    exact ⟨zero.pen,zero.f_l⟩
end YM.Integration.WilsonIndependentConditionedPivotTailLocalSale
