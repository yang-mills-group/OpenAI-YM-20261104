import YM.Integration.WilsonIndependentMatchedRosterMoney
import YM.Integration.WilsonIndependentMatchedRosterDate
import YM.Integration.WilsonIndependentMatchedRosterHome
import YM.Integration.WilsonIndependentMatchedRosterSum

/-! At the matched reporter the actual complete conditional product, on all
positions and the one Wilson vacuum, earns one stable gain per designated
front. All proper later products and the actual unit stay in the return. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedRosterReception
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

open WilsonIndependentMatchedCoverProfile
open WilsonIndependentMatchedRosterLane (Lane)
open WilsonIndependentMatchedRosterChronology (mass born)
open WilsonIndependentMatchedRosterTariff (offer)
open WilsonIndependentMatchedRosterPowers (profiles)
variable {G:Gauge}{h D k e u₀ n:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u₀ e}{E W K U:Credit}{dim:Fin (n+1)→ℕ}

def perSite (u b:ℕ)(z:ℝ)(A B:Fin (n+1)→ℝ):ℝ:=
  ∏s,WilsonIndependentMatchedRosterTariff.factor u b z*(B s*A s)

def bill (k e u b:ℕ)(l:Fin (n+1)→ℕ)(δ η t z:ℝ)(A B:Fin (n+1)→ℝ):ℝ:=
  let Z:=perSite u b z A B
  (coinMat (∑s,l s) e)^n*Z+2*(δ^(-η)*profiles n k e u b t z Z)

theorem original (run:XSpace.Run)(l d w:Fin (n+1)→ℕ)(out u b:ℕ)(W₀ U₀:Credit)(cap η:ℝ)(hp:0<η)
    (room:∑s,l s ≤ out)(clear:1 ≤ (b:ℝ)-((∑s,d s:ℕ):ℝ)-((∑s,w s:ℕ):ℝ)/4):
    ∀ᶠ idx:ℕ in atTop,∀(X:CutsP H T p v E W K U)
    (φ:(s:Fin (n+1))→Rarity (dim s))(P:Fin (n+1)→ℕ→Era G ℝ)
    (y t z:ℝ)(o:CellR)(A B:Fin (n+1)→ℝ),
    let δ:=(run.step idx).spacing
    X.vesselsC.y X.m ≤ cap→WilsonOriginalPublicPlantedStableCredit.span X X.i= -Real.log δ→
    SpringD X.vesselsC out u b W₀→Dormitory X.vesselsC (∑s,l s) u U₀→
    0<t→(∀a c,a≠c→ClearDay (φ a) (φ c) t)→(∀s,radiusH (φ s) 1 y ≤ z)→
    (∀s,0 ≤ A s)→(∀s,Amplitude (φ s) (B s))→
    (∀s,Lane X.vesselsC (l s) (d s) X.m X.i X.N u b (φ s) y o δ ((w s:ℝ)/4) (A s) (B s) (P s))→
    let product:=cruises X.ax X.tx X.N (∑s,l s) (X.m+X.i) X.m (mass P X.i)
    Auth (∑s,l s) product ∧ Flush e u 1 product
      (bill out e u b l δ η t z A B*δ^(((∑s,w s:ℕ):ℝ)/4)):=by
  obtain ⟨C,date⟩:=WilsonIndependentMatchedRosterDate.original (D:=dim) G out e u b l E W₀ U₀
  filter_upwards [WilsonIndependentMatchedCoverCap.earned (H:=H) (T:=T) (p:=p) (v:=v)
    (E:=E) (W:=W) (K:=K) (U:=U) run C (priceWG G e out u b E W₀)
    ((∑s,d s)+(∑s,w s)) cap η hp] with idx income
  intro X φ P y t z o A B δ capX clock spring dorm ht sep profile cash test lane
  let Z:=perSite u b z A B
  let M:=δ^(-η)*profiles n out e u b t z Z
  have hd:0<δ:=(run.step idx).positive
  have endDate:X.m+X.i ≤ X.N:=X.hc.trans X.hn
  have hz:0 ≤ z:=(zero_le_one.trans (fieldCap (φ 0) 1 y)).trans (profile 0)
  have Zpos:0 ≤ Z:=Finset.prod_nonneg fun s _=>by have v₁:=cash s;have v₂:=(test s).1
                                                  unfold WilsonIndependentMatchedRosterTariff.factor;positivity
  have posM:0 ≤ M:=by have base:=coinMat_nn out e;unfold M profiles;positivity
  have own (i:ℕ)(hi:i<X.i):
      let r:=paceT X.ax.S X.m (X.m+i)
      Flush e u 1 (cruises X.ax X.tx X.N (∑s,l s) (X.m+i) X.m (born X.vesselsC X.m X.N l P i))
        (M*r^((b:ℝ)-((∑s,d s:ℕ):ℝ))*(δ/r)^(((∑s,w s:ℕ):ℝ)/4)):=by
    let j:=X.m+i
    let L:ℝ:=(ll X.ax j).L.val
    let x:=paceT X.ax.S X.m (j+1)
    let r:=paceT X.ax.S X.m j
    have live:X.vesselsC.anchor ≤ j:=X.ha.trans (Nat.le_add_right _ _)
    have hl:1 ≤ L:=by dsimp [L];exact_mod_cast (ll X.ax j).L.pos
    have step:x*L=r:=pace_step X.ax.S X.m j
    have wage:=date X.vesselsC spring dorm X.m X.N X.i endDate X.ha room d w φ P δ t y z o A B hd ht sep profile cash test lane i hi
    have paid:=income X capX clock i hi.le 0 0 (by norm_num)
    simp only [zero_add,Real.rpow_zero,mul_one] at paid
    let J:=WilsonIndependentMatchedCoverDate.age X.vesselsC X.m j
    let S:=priceWG G e out u b E W₀
    have hC:0 ≤ C.buy J:=zero_le_one.trans (C.purchase (WilsonIndependentMatchedCoverCap.house X i hi.le).1)
    have hS:0 ≤ X.vesselsC.cash S j:=zero_le_one.trans (S.purchase (X.vesselsC.depth j live))
    have charge:=WilsonIndependentMatchedRosterMoney.original (k:=out) (e:=e) (u:=u) (b:=b)
      (C.buy J) (X.vesselsC.cash S j) (δ^(-η)) d w A B δ x L t z hC hS cash (fun s=>(test s).1)
      (pace_pos ..) hl hd ht hz paid
    dsimp only at wage charge ⊢
    rw [step] at charge
    exact ⟨wage.2.1.trans charge,fun j hj r hr=>(wage.2.2 j hj r hr).more charge⟩
  have home:=WilsonIndependentMatchedRosterHome.original X.vesselsC X.m X.i X.N d w l φ P δ y z o A B hd profile cash test lane
  have summed:=WilsonIndependentMatchedRosterSum.original X.vesselsC l X.m X.N X.i u b (∑s,d s) (∑s,w s)
    endDate P (fun s=>(lane s).accounts.head) (fun s=>(lane s).pushed) δ M _ hd posM clear home.2 own
  convert summed using 3
  unfold bill M Z perSite
  ring

end YM.Integration.WilsonIndependentMatchedRosterReception
