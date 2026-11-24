import YM.Integration.WilsonIndependentMatchedCoverJoined
import YM.WilsonCoeffUV.Product.Report.Age
import YM.Integration.WilsonIndependentMatchedJoinFare

/-! A single genuine join after propagation to the reporting field, at the
native charge of both seated operands and their individual scale gains. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedCoverDate
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
variable {G:Gauge}{D D' e:ℕ}{E:Credit}

def age (R:Realm G (e+1) E)(m i:ℕ):ℝ:=
  R.y m+(R.draws.S.scale i-R.draws.S.scale m)+(i-m:ℕ)

def salary (C W:Credit)(R:Realm G (e+1) E)(l r k u b m i:ℕ)
    (φ:Rarity D)(ψ:Rarity D')(y t z α β A B C₁ D₁:ℝ):ℝ:=
  let x:=paceT R.draws.S m (i+1)
  let L:ℝ:=(ll R.draws i).L.val
  C.buy (age R m i)*R.cash (priceWG G e k u b E W) i*
    WilsonIndependentMatchedJoinFare.rent l r u b L t z (radiusH φ x y) (radiusH ψ x y) α β A B C₁ D₁

/-- At the named older date all thermal coefficients, including the unit, cost
the actual seats' salaries times the first-connection and stable gains. -/
theorem original (G:Gauge)(l r k e u b d₁ d₂:ℕ)(E W L:Credit):
    ∃ C:Credit,∀(R:Realm G (e+1) E)(_sale:SpringD R k u b W)
    (_older:Dormitory R (l+r) u L)(m i N:ℕ)(_hm:R.anchor  ≤  m)(_hi:m  ≤  i)(_hn:i < N)
    (_room:l+r ≤ k)(φ:Rarity D)(ψ:Rarity D')(P Q:Era G ℝ)(δ y t z α β A B C₁ D₁:ℝ)
    (o:CellR)(_top:0<δ)(_sep:ClearDay φ ψ t)(_s:0<t),
    let x:=paceT R.draws.S m (i+1)
    let rest:=paceT R.draws.S m i
    let front:=ll R.draws i
    radiusH φ rest y ≤ z  →  radiusH ψ rest y ≤ z  → 
    (VisitsT φ x y o).Nonempty  →  (VisitsT ψ x y o).Nonempty  → 
    Income P l e (u+b) (OrbP front φ x y o) (charge φ (u+b) d₁ x y (A*(δ/x)^α) B)  → 
    Income Q r e (u+b) (OrbP front ψ x y o) (charge ψ (u+b) d₂ x y (C₁*(δ/x)^β) D₁)  → 
    let reached:=cruises R.draws R.paid N (l+r) i m (JoinGap R.draws R.paid i N l r P Q)
    let fee:=salary C W R d₁ d₂ k u b m i φ ψ y t z α β A B C₁ D₁ *
      rest^((b:ℝ)-((d₁+d₂:ℕ):ℝ))*(δ/rest)^(α+β)
    Flush e u 1 reached fee ∧ ∀j ≤ e,∀q:Fin 0 → YForest G,‖reached.2 j 0 q‖ ≤ fee :=by
  obtain ⟨C,take⟩:=WilsonIndependentMatchedCoverJoined.original (D:=D) (D':=D') G l r k e u b E W L
  refine ⟨C,?_⟩
  intro R sale older m i N hm hi hn room φ ψ P Q δ y t z α β A B C₁ D₁ o top sep s
  dsimp only
  intro pfit qfit lp rp left right
  let x:=paceT R.draws.S m (i+1)
  let v:=paceT R.draws.S m i
  let len:ℝ:=(ll R.draws i).L.val
  have step:x*len=v:=pace_step R.draws.S m i
  have hx:0<x:=pace_pos R.draws.S m (i+1)
  have hlen:0<len:=by dsimp [len]; exact_mod_cast (ll R.draws i).L.pos
  have paid:=take R sale older m i (i+1) N (hm.trans hi) (Nat.lt_succ_self i) hn room
    (paceT R.draws.S m) (age R m i) (pace_escort hm hi) (PadRank.frugal R hm hi) φ ψ P Q x y t z o
    hx (step.le.trans (pace_le R.draws.S hi)) step.symm sep s (step.symm ▸ pfit) (step.symm ▸ qfit)
    lp rp _ _ left right
  dsimp only at paid
  have cost:=WilsonIndependentMatchedJoinFare.original φ ψ d₁ d₂ u b x y len δ t z α β A B C₁ D₁ hx hlen top
  rw [step] at cost
  rw [pace_self, cost] at paid
  simpa only [salary,x,v,len,mul_assoc] using paid.2

end YM.Integration.WilsonIndependentMatchedCoverDate
