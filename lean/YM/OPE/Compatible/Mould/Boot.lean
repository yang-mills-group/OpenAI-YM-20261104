import YM.OPE.Compatible.Mould.Thorn
/-! # rank.Z at opacity. Measured.B. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {u ν:M→ℝ}{hp:4 ≤ i}{V:(j:M)→Alps K T i (u j)}
namespace Topic
local notation "μ"=> lapPrice (Patch.L P)
lemma zInvest (A: Ω Z M ν)(he:e<l+1)(j:M): Surjective (A.read e he j):=by
      intro v; let f(_:Unit):= v; let p(_:Unit):=j; obtain ⟨x,H,y⟩:= Aeon.zark Z.r Z.t (A.branch p) Z.bill e he (zero_le_one:(0:Unit→ℝ) ≤1) f (show Wealth _ _ _ from wealthC v.val) 0 (Nat.zero_le _) (fun _=> trims.be _); exact ⟨x (), (y ()).2⟩
variable (V':Ω Z M ν)
variable {Z a V'} {hv:0≤u} (T':Z.Floss V V' hp hv k Hp a)
lemma smoke {A' B':ℕ→ℝ}{q:ℝ}(hp:Sky q k B')(ha:Thick q A')(h:Thick q (A'-B'))(j:ℕ):B' j=0:=by
     have hv:Thick q B':=by rw [show B'=A'-(A'-B') by abel]; exact Thick.sub ha h
     exact congr_fun (hp.blind hv) j
private lemma squaredPrice (he : e < l + 1) :
    lapPrice P.L l * lapPrice P.L l ≤ lapPrice P.L e * lapPrice P.L e := by
  have step : lapPrice P.L l ≤ lapPrice P.L e := by
    by_cases same : l = e
    · rw [same]
    · exact (stairPrice P.L _ _ (by omega) P.coarse).le
  exact mul_le_mul step step (EndFare P.L l).le (EndFare P.L e).le

private lemma opacitySky (i : Phase) (v : Even n.val) (x y : Site n) (p q : Mint Z e) :
    Sky (lapPrice P.L e * lapPrice P.L e) 6 (fun j => Por Hp Z e i v x y a j p q) :=
  sunV H hs X Z.station D₀ (spose a G d τ) (ContinuousLinearMap.id ℝ (solar G d τ))
    v x y Hp i p q

private lemma useAllReadings {A X : Type*} (read : A → X) (onto : Surjective read)
    (p : X) (B C : X → X → ℝ) (hc : ∀ s t, B s t = C s t)
    (h : ∀ q, B p (read q) = 0 ∧ B (read q) p = 0) :
    ∀ w, C p w = 0 ∧ C w p = 0 := by
  intro w
  obtain ⟨q, rfl⟩ := onto w
  exact ⟨(hc _ _).symm.trans (h q).1, (hc _ _).symm.trans (h q).2⟩

private abbrev rawProbe (H : LocalRatio R) (hs : G.Simple) (D : Stern K P τ l d w)
    (A : Alps K T i v) (hi : 4 ≤ i) (hu : 0 ≤ v) (a : Axis)
    (s : Phase) (hn : Even n.val) (x y : Site n) (t q : Tracts G d τ) (j : ℕ) :=
  let F := Fallix G D.aware K A.gear hi
  Variance.HillP A H hi hs hu P x y hn a s j (F t) (F q)

private lemma initialNullRows (A : Alps K T i v) (hi : 4 ≤ i) (hu : 0 ≤ v)
    (s : Phase) (hn : Even n.val) (x y : Site n) (hQ : Pins K P x y)
    (t q : Tracts G d τ) (ht : t ∈ OmegaPhi (H := H) (hs := hs) (D₀ := D₀) a A hi hu) :
    Thick (μ l * μ l) (rawProbe H hs D₀ A hi hu a s hn x y t q) ∧
    Thick (μ l * μ l) (rawProbe H hs D₀ A hi hu a s hn x y q t) := by
  let F := Fallix G D₀.aware K A.gear hi
  exact Variance.quakeX A H hi hs hu P x y hn (F t) a
    (show F t ∈ Variance.SailSap A H hi hs hu P a l from ht) hQ (F q) s

include T'

private lemma rowDifference (b : M) (he : e < l + 1) (s : Phase) (hn : Even n.val)
    (x y : Site n) (hx : barrier P ≤ n.val) (hQ : Pins K P x y) (t q : V'.flag e b) :
    Thick (μ e * μ e)
      (rawProbe H hs D₀ (V b) hp (hv b) a s hn x y t.val q.val -
        fun j => Por Hp Z e s hn x y a j (V'.read e he b t) (V'.read e he b q)) :=
  T'.corn e he s n hn x y hx hQ b t q

private lemma vanishRow (b : M) (he : e < l + 1) (s : Phase) (hn : Even n.val)
    (x y : Site n) (hx : barrier P ≤ n.val) (hQ : Pins K P x y) (t q : V'.flag e b)
    (bound : Thick (μ l * μ l) (rawProbe H hs D₀ (V b) hp (hv b) a s hn x y t.val q.val))
    (j : ℕ) : Por Hp Z e s hn x y a j (V'.read e he b t) (V'.read e he b q) = 0 :=
  smoke (A' := rawProbe H hs D₀ (V b) hp (hv b) a s hn x y t.val q.val)
    (B' := fun j => Por Hp Z e s hn x y a j (V'.read e he b t) (V'.read e he b q))
    (opacitySky (Z := Z) (a := a) (e := e) Hp s hn x y (V'.read e he b t) (V'.read e he b q))
    (bound.extend (squaredPrice (P := P) he))
    (rowDifference (Z := Z) (V := V) (V' := V') (a := a) Hp T' b he s hn x y hx hQ t q) j

lemma StockUnit {he:e<l+1}(b:M)(t:V'.flag e b)(h:t.val∈ OmegaPhi (H:=H) (hs:=hs) (D₀:=D₀) a (V b) hp (hv b)): -- specific probe
    ∀(n:Side)(hV:Even n.val)(x y:Site n),barrier P≤ n.val→ Pins K P x y→∀ j s (q:V'.flag e b),Por Hp Z e s hV x y a j (V'.read e he b t) (V'.read e he b q)=0∧ Por Hp Z e s hV x y a j (V'.read e he b q) (V'.read e he b t)=0 := by
  intro n hV x y hx hQ j s q
  have rows := initialNullRows (H := H) (hs := hs) (D₀ := D₀) (a := a) (V b) hp (hv b) s hV x y hQ t.val q.val h
  have kills := vanishRow (Z := Z) (V := V) (V' := V') (a := a) Hp T' b he s hV x y hx hQ
  exact ⟨kills t q rows.1 j, kills q t rows.2 j⟩

lemma stockMe {he:e<l+1}(b:M)(t:V'.flag e b)(h:t.val∈ OmegaPhi (H:=H) (hs:=hs) (D₀:=D₀) a (V b) hp (hv b)): V'.read e he b t∈ Dross Hp Z a e := by
  change Kneel Hp Z a (V'.read e he b t)
  intro n hn x y hx hq j s
  exact useAllReadings (V'.read e he b) (zInvest Z V' he b) (V'.read e he b t)
    (Por Hp Z e s hn x y a j) (fun v w => UnitBorn Hp Z a hn x y s j v w)
    (fun v w => flareP Hp Z a v w hn x y s j)
    (fun q => StockUnit Hp T' b t h n hn x y hx hq j s q (he := he))
end Topic
end YM.OPE.Stroke
