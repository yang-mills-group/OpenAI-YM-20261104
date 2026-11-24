import YM.Integration.WilsonMarkedIndependentNormalizedElection
import YM.WilsonCoeffUV.Product.Report.UVLimit

/-! The inverse-normalized Wilson source travels on the independent program
elected on the same levels, ratio and original microscopic label sections. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentNormalizedReporter
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open scoped Topology BigOperators Classical
variable {G:Gauge}{a h D k u e:ℕ}(R:Run G)

open WilsonMarkedIndependentNormalizedElection (deck normalized)

/-- Fixed-mesh comparison of the complete normalized independent report. -/
def Reading {F:Frame G h}(Q:Fin (a+1)→SealR G)(L:Levels G)(O:ChartRatio G)(y:ℕ→ℝ)
    (S:SectionData F)(p:h<D)(k e:ℕ)(c wallet:Credit)(j:ℕ)(X:Herit Q)(A:Fin (a+1)→ℝ):Prop:=
  ∀b m:ℕ,j ≤ b → b ≤ m → ∀(φ:Wilt Q)(B:Fin (a+1)→ℝ)(z:ℝ),Compar L.S y j m ≤ z →
    Bough Q φ (paceT L.S m b) z B → ∀i≤e,∀ f:Alma F,
    let val:=fun N=>PowerSeries.coeff i (Reports L O S p φ (normalized L O Q X m N) m b j N k f)
    let limit:=PowerSeries.coeff i (lodgeIn L O S p φ (normalized L O Q X m) m b j k f)
    Tendsto val atTop (𝓝 limit) ∧ ∀s N:ℕ,m ≤ s → s ≤ N →
      twain (c.buy z*(∏i,B i*(wallet.buy (y m)*A i))) (trailC L.S m s) (val N) limit

private theorem estimate {F:Frame G h}(Q:Fin (a+1)→SealR G)(S:SectionData F)(p:h<D)
    (rails:Rails h k u e)(cap:capP Q ≤ k):
    ∃c wallet:Credit,∀(Y:Torch (hol G) S p rails Credit.leanC Credit.leanC Credit.leanC)
    (W:ChorusLine (hol G) S p e Credit.leanC Credit.leanC Credit.leanC),W.arch=Y.L →
    HorizonP (hol G) Y.L.V Credit.leanC Credit.leanC Q → SpringD Y.L.V (capP Q) u (capP Q+2) Credit.leanC →
    Dormitory Y.L.V (capP Q) u Credit.leanC → FramesR (hol G) Y.L.V Credit.leanC Credit.leanC Q Credit.leanC →
    ∀X:Herit Q,∃A:Fin (a+1)→ℝ,Reading Q Y.L.V.draws Y.L.V.paid Y.L.V.y S p k e c wallet Y.L.V.anchor X A:=by
  obtain ⟨c,report⟩:=reportUV (hol G) Q S p rails cap Credit.leanC Credit.leanC Credit.leanC
    Credit.leanC Credit.leanC Credit.leanC
  obtain ⟨bill,lens⟩:=steering (hol G) Q e Credit.leanC Credit.leanC Credit.leanC Credit.leanC
  refine ⟨c,bill,?_⟩
  intro Y W agree ready spring dorm frames X
  obtain ⟨A,stock⟩:=shipments_one X e
  refine ⟨A,?_⟩
  intro b m jb bm φ B z legs shape i he f
  have stored:=lens Y.L.V frames m (jb.trans bm) A (fun _=>X) (stock Y.L.V.draws.S m)
  exact report Y W agree ready spring dorm m b Y.L.V.anchor φ
    (normalized Y.L.V.draws Y.L.V.paid Q X m) (fun i=>Y.L.V.cash bill m*A i) B z
    le_rfl jb bm legs shape stored i he f

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (p:h<D)(rails:Rails h k u e)(l d:Fin (a+1)→ℕ)(admit:∀i,l i<d i)
    (cap:capP (deck (G:=G) l d admit) ≤ k):
    let Q:=deck (G:=G) l d admit
    let L:=R.family.path.levels
    let S:SectionData ((primes G).F h):=(primes G).T h
    ∃c wallet:Credit,∀ᶠ j:ℕ in atTop,∀X:Herit Q,∃A:Fin (a+1)→ℝ,
      Reading Q L R.metals.O (zz L) S p k e c wallet j X A:=by
  intro Q L S
  obtain ⟨c,wallet,fundedRead⟩:=estimate Q S p rails cap
  refine ⟨c,wallet,?_⟩
  filter_upwards [WilsonMarkedIndependentNormalizedElection.original R simple v funded p rails l d admit cap] with j filed
  obtain ⟨W,Y,level,cash,clock,date,agree,dorm,spring,frames,ready⟩:=filed
  have priced:=fundedRead Y W agree ready spring dorm frames
  rw [level,cash,clock,date] at priced
  exact priced

end YM.Integration.WilsonMarkedIndependentNormalizedReporter
end
