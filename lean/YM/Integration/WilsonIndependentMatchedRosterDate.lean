import YM.Integration.WilsonIndependentMatchedRosterChronology
import YM.Integration.WilsonIndependentMatchedRosterFronts
import YM.Integration.WilsonIndependentMatchedRosterTariff

/-! One complete genuine multicolour birth, carried to the actual report.
Position choices and their supports are retained through first formation. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedRosterDate
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

open WilsonIndependentMatchedCoverProfile
open WilsonIndependentMatchedRosterLane (Lane)
open WilsonIndependentMatchedRosterTariff (offer)
open WilsonIndependentMatchedRosterChronology (born)
variable {G:Gauge}{n e k u b:ℕ}{E W:Credit}{D:Fin (n+1)→ℕ}

def wage (C W:Credit)(R:Realm G (e+1) E)(n k u b m j:ℕ)
    (t z r:ℝ)(A:Fin (n+1)→ℝ):ℝ:=
  C.buy (WilsonIndependentMatchedCoverDate.age R m j)*
    ((n:ℝ)*R.cash (priceWG G e k u b E W) j*pearlB u b (4*z) (t/r)*nuP (coinMat k e+1) n A)

lemma radius {D:ℕ}(φ:Rarity D){x y z:ℝ}(hx:0<x)(hr:x ≤ 1)(cap:radiusH φ 1 y ≤ z):radiusH φ x y ≤ z:=by
  unfold radiusH at cap ⊢;rw [abs_of_pos hx] ;rw [abs_one] at cap;linarith

theorem original (G:Gauge)(k e u b:ℕ)(l:Fin (n+1)→ℕ)(E W V:Credit):
    ∃ C:Credit,∀(R:Realm G (e+1) E)(_sale:SpringD R k u b W)(_later:Dormitory R (∑s,l s) u V)
    (m N h:ℕ)(_top:m+h ≤ N)(_hm:R.anchor ≤ m)(_room:∑s,l s ≤ k)
    (d w:Fin (n+1)→ℕ)(φ:(s:Fin (n+1))→Rarity (D s))(P:Fin (n+1)→ℕ→Era G ℝ)
    (δ t y z:ℝ)(o:CellR)(A B:Fin (n+1)→ℝ)(_hd:0<δ)(_ht:0<t)
    (_sep:∀a c,a≠c→ClearDay (φ a) (φ c) t)(_cap:∀s,radiusH (φ s) 1 y ≤ z)
    (_cash:∀s,0 ≤ A s)(_test:∀s,Amplitude (φ s) (B s))
    (_lane:∀s,Lane R (l s) (d s) m h N u b (φ s) y o δ ((w s:ℝ)/4) (A s) (B s) (P s))
    (i:ℕ)(_job:i<h),
    let j:=m+i
    let x:=paceT R.draws.S m (j+1)
    let r:=paceT R.draws.S m j
    let budget:=wage C W R n k u b m j t z r (fun s=>offer u b (d s) (w s) z δ x (A s) (B s))
    let hit:=cruises R.draws R.paid N (∑s,l s) j m (born R m N l P i)
    Auth (∑s,l s) hit ∧ Flush e u 1 hit budget:=by
  obtain ⟨C,retain⟩:=waveSeen G (∑s,l s) e u E V
  refine ⟨C,?_⟩
  intro R sale later m N h top hm room d w φ P δ t y z o A B hd ht sep cap cash test lane i job
  dsimp only
  let j:=m+i
  let x:=paceT R.draws.S m (j+1)
  let r:=paceT R.draws.S m j
  let L:ℝ:=(ll R.draws j).L.val
  let pay:=fun s=>offer u b (d s) (w s) z δ x (A s) (B s)
  let lower:=(n:ℝ)*R.cash (priceWG G e k u b E W) j*pearlB u b (4*z) (t/r)*nuP (coinMat k e+1) n pay
  have live:R.anchor ≤ j:=hm.trans (Nat.le_add_right _ _)
  have edge:j<N:=by dsimp [j];omega
  have law:x*L=r:=pace_step R.draws.S m j
  have hl:1 ≤ L:=by dsimp [L];exact_mod_cast (ll R.draws j).L.pos
  have hx:0<x:=pace_pos ..
  have hr:0<r:=pace_pos ..
  have xr:x ≤ r:=by rw [←law];exact le_mul_of_one_le_right hx.le hl
  have fine:x ≤ 1:=pace_le _ (by dsimp [j];omega)
  have coarse:r ≤ 1:=pace_le _ (Nat.le_add_right _ _)
  have zpos:0 ≤ z:=((zero_le_one.trans (fieldCap (φ 0) 1 y)).trans (cap 0))
  have buy (s):0 ≤ pay s:=WilsonIndependentMatchedRosterTariff.positive _ _ _ _ zpos hd.le hx.le (cash s) (test s).1
  have minted:0 ≤ lower:=by
    unfold lower pearlB
    have S:0 ≤ R.cash (priceWG G e k u b E W) j:=zero_le_one.trans ((priceWG G e k u b E W).purchase (R.depth j live))
    have H:=coinMat_nn k e
    have prod:0 ≤ ∏s,pay s:=Finset.prod_nonneg (fun s _=>buy s)
    rw [loadRep]
    positivity
  have taken:Auth (∑s,l s) (born R m N l P i) ∧ Flush e u r (born R m N l P i) lower:=by
    by_cases hits:∀s,(VisitsT (φ s) x y o).Nonempty
    · have inlets (s):Income (P s (i+1)) (l s) e (u+b) (OrbP (ll R.draws j) (φ s) x y o) (pay s):=by
        have h0:=(lane s).accounts.cash i job
        have bound:=WilsonIndependentMatchedRosterTariff.incoming (φ s) u b (d s) (w s) δ x y z (A s) (B s)
          hx hd (cash s) (test s).1 (radius _ hx fine (cap s))
        exact ⟨h0.1,fun c hc a v hi=>(h0.2 c hc a v hi).stepX bound hc⟩
      have outlets (s):Flush e u (x*L) (verseI R.draws R.paid j N (l s) (P s (i+1))) (pay s):=by
        rw [law,(lane s).pushed i job]
        have h0:=(lane s).billed i job.le
        have bound:=WilsonIndependentMatchedRosterTariff.outgoing (φ s) u b (d s) (w s) δ x r y z (A s) (B s)
          hx xr hd (cash s) (test s).1 (radius _ hr coarse (cap s))
        exact ⟨buy s,fun a ha v hv=>(h0.2 a ha v hv).more bound⟩
      have gain:=WilsonIndependentMatchedRosterFronts.current R sale live edge l room φ (fun s=>P s (i+1)) x y t z o hx
        (law.le.trans coarse) ht sep (fun s=>by rw [law];exact radius _ hr coarse (cap s)) hits pay inlets outlets
      change Auth _ (born R m N l P i) ∧ Flush e u (x*L) (born R m N l P i)
        ((n:ℝ)*R.cash (priceWG G e k u b E W) j*pearlB u b (4*z) (t/(x*L))*nuP (coinMat k e+1) n pay) at gain
      rw [law] at gain
      exact gain
    · obtain ⟨s,miss⟩:=Classical.not_forall.mp hits
      have gone:=WilsonIndependentMatchedRosterEdge.absent R edge (fun s=>P s (i+1)) l s ((lane s).accounts.empty i job miss)
      change DeltaGap R.draws R.paid j N (fun s=>P s (i+1)) l=0 at gone
      change Auth _ (DeltaGap ..) ∧ Flush _ _ _ (DeltaGap ..) _
      rw [gone]
      let null:=Fringed.nullV (G:=G) (k:=∑s,l s) (e:=e) (u:=u) (η:=r) (δ:=0) le_rfl minted
      exact ⟨null.pen,null.f_l⟩
  let debt:=max 0 (R.tempC j j)
  have endBill:=retain R later m j (paceT R.draws.S m) j N N lower debt
    (WilsonIndependentMatchedCoverDate.age R m j) (pace_escort hm (Nat.le_add_right m i))
    (PadRank.frugal R hm (Nat.le_add_right m i)) le_rfl edge.le edge.le (le_max_right _ _)
    _ _ (Fringed.same taken.2 taken.1 (le_max_left _ _))
  exact ⟨endBill.pen,pace_self R.draws.S m ▸ endBill.f_l⟩

end YM.Integration.WilsonIndependentMatchedRosterDate
