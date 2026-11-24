import YM.Integration.WilsonIndependentMatchedCoverDate
import YM.Integration.WilsonOriginalPublicPlantedStableCredit

/-! The single report-age credit pays every genuine lower visit, receiver and
its true optical block, independently of the finer top. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedCoverCap
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedCoverDate
variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}
    {H:Hol G}{T:SectionData F}{p:h<D}{v:Rails h k u e}{E W K U:Credit}

def market (C S E:Credit)(d:ℕ):Credit:=(C.prodC S).prodC (E.powC (d+1))

lemma house (X:CutsP H T p v E W K U)(i:ℕ)(hi:i ≤ X.i):
    1 ≤ WilsonIndependentMatchedCoverDate.age X.vesselsC X.m (X.m+i) ∧ WilsonIndependentMatchedCoverDate.age X.vesselsC X.m (X.m+i) ≤ X.Age:=by
  have a:=X.vesselsC.depth X.m X.ha
  have b:=scales X.ax.S (Nat.le_add_right X.m i)
  have c:=scales X.ax.S (Nat.add_le_add_left hi X.m)
  have d: (i:ℝ) ≤ (X.i:ℝ):=by exact_mod_cast hi
  change 1 ≤ X.vesselsC.y X.m+(X.ax.S.scale (X.m+i)- X.ax.S.scale X.m)+((X.m+i-X.m:ℕ):ℝ) ∧
    X.vesselsC.y X.m+(X.ax.S.scale (X.m+i)- X.ax.S.scale X.m)+((X.m+i-X.m:ℕ):ℝ) ≤
      X.vesselsC.y X.m+(X.ax.S.scale (X.m+X.i)- X.ax.S.scale X.m)+(X.i:ℝ)
  simp only [Nat.add_sub_cancel_left]
  constructor <;> linarith only [a,b,c,d,Nat.cast_nonneg (α:=ℝ) i]

theorem block (X:CutsP H T p v E W K U)(C S:Credit)(d i:ℕ)(hi:i ≤ X.i)
    (α β:ℝ)(rank:α+β ≤ 1):
    let j:=X.m+i
    let L:ℝ:=(ll X.ax j).L.val
    C.buy (WilsonIndependentMatchedCoverDate.age X.vesselsC X.m j)*X.vesselsC.cash S j*(L^d*L^(α+β)) ≤
      (market C S E d).buy X.Age:=by
  let j:=X.m+i
  let L:ℝ:=(ll X.ax j).L.val
  have hj:X.vesselsC.anchor ≤ j:=X.ha.trans (Nat.le_add_right _ _)
  have src:=house X i hi
  have first:=C.elder src.1 src.2
  have hot:=X.vesselsC.depth j hj
  have cmp:X.vesselsC.y j ≤ X.Age:=X.windowC.covers hi
  have second:=S.elder hot cmp
  have paid:L ≤ E.buy X.Age:=(X.vesselsC.taxes j hj).height.trans (E.elder hot cmp)
  have pos:L ≥ 1:=by dsimp [L]; exact_mod_cast (ll X.ax j).L.pos
  have law:L^(α+β) ≤ L:=by simpa only [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_le pos rank)
  have kth:L^d*L^(α+β) ≤ (E.buy X.Age)^(d+1):=by
    rw [pow_succ]
    exact mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans pos) paid d)
      (law.trans paid) (Real.rpow_nonneg (zero_le_one.trans pos) _) (pow_nonneg ((zero_le_one.trans pos).trans paid) _)
  dsimp only
  rw [market,Credit.products,Credit.products,Credit.power]
  apply mul_le_mul _ kth (mul_nonneg (pow_nonneg (zero_le_one.trans pos) _) (Real.rpow_nonneg (zero_le_one.trans pos) _))
    (mul_nonneg (zero_le_one.trans (C.purchase X.windowC.warm)) (zero_le_one.trans (S.purchase X.windowC.warm)))
  exact mul_le_mul first second (zero_le_one.trans (S.purchase hot)) (zero_le_one.trans (C.purchase X.windowC.warm))

theorem earned (V:XSpace.Run)(C S:Credit)(d:ℕ)(B θ:ℝ)(positive:0<θ):
    ∀ᶠ j:ℕ in atTop,∀(X:CutsP H T p v E W K U), X.vesselsC.y X.m ≤ B →
    WilsonOriginalPublicPlantedStableCredit.span X X.i= -Real.log (V.step j).spacing →
    ∀ i ≤ X.i,∀ α β:ℝ,α+β ≤ 1 →
    let n:=X.m+i
    let L:ℝ:=(ll X.ax n).L.val
    C.buy (WilsonIndependentMatchedCoverDate.age X.vesselsC X.m n)*X.vesselsC.cash S n*(L^d*L^(α+β)) ≤
      (V.step j).spacing^(-θ):=by
  filter_upwards [WilsonOriginalPublicPlantedStableCredit.credit (H:=H) (T:=T) (p:=p) (v:=v)
    (E:=E) (W:=W) (K:=K) (U:=U) V (market C S E d) B θ positive] with j price
  intro X home clock i hi α β rank
  exact (block X C S d i hi α β rank).trans (price X home clock)

end YM.Integration.WilsonIndependentMatchedCoverCap
