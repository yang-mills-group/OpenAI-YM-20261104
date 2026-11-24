import YM.Integration.WilsonOriginalNullOriginGridMatrix

/-! The physical child route and its whole paid matrix are issued from the
one given position on the fine grid. Neither the source nor the origin
inverse is elected anew at its descendants. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullOriginGridRoster
open Function Filter Lattice RG Wilson Source Labels MeasureTheory Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor
open WilsonOriginalNullPlacedGermMap WilsonOriginalNullPlacedFullMatrix WilsonOriginalNullOriginGridMatrix
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d

def ancestry (p s:ℕ) (y:Site ((C₀).side s p)) (j:ℕ):Site ((C₀).side j p):=
  if h:j ≤ s then ((C₀).S.toDepth h p).parent y else 0

theorem starts (p s:ℕ) (y:Site ((C₀).side s p)):ancestry R p s y s=y:=by
  rw [ancestry,dif_pos (le_refl s)]
  let v:=(C₀).S.toDepth (le_refl s) p
  have back:v.parent (v.embed y)=y:=v.embed_parent y
  rw [show v.embed y=y from like_embed y] at back
  exact back

theorem route (p s:ℕ) (y:Site ((C₀).side s p)) {j:ℕ} (live:j<s):
    ((C₀).path.levels.clock.op j p).ratio.parent (ancestry R p s y (j+1))=ancestry R p s y j:=by
  simp only [ancestry,dif_pos (show j+1 ≤ s from live),dif_pos live.le]
  exact (Next.Rank.Station.parent_nested ((C₀).path.levels.clock.op j p).ratio
    ((C₀).S.toDepth live p) ((C₀).S.toDepth live.le p) ((C₀).S.block_odd j) ((C₀).S.toDepth_odd live p) y).symm

structure Issued (η:ℝ) (N p m n:ℕ) (live:m+n ≤ N) (z:Site ((C₀).side (m+n) p))
    (home:Opened C₀ d m p) (high:Opened C₀ d (m+n) p) (A:(C₀).label d →ₗ[ℂ] (C₀).label d):Prop where
  paid:Heard R d η N p m n live home (ancestry R p (m+n) z) A
  reads (v:(C₀).label d) :
    let b:=((C₀).factory d N p).terminal.symm v
    let e:=fitting (C:=C₀) d N p m R.makes home (by omega) b
    let parent:=((C₀).S.toDepth (show m ≤ m+n by omega) p).parent z
    let a:=dyes C₀ (m+n) N p live (((C₀).S.a (m+n):ℂ)^d • (C₀).O N p v (((C₀).S.toDepth live p).embed z))
    let body:=flow C₀ d N p m n a
    let π:=fun q=>projection F₀ (C₀).params ((C₀).path.rep N p m).p.threshold parent q
    let coord:=measured R d N p m n live home high A ((centered R d N p m n live home high).symm e)
    ∃ q,Printed C₀ d N p m parent q body ∧ π q=coord ∧ ∀ q',Printed C₀ d N p m parent q' body → π q'=coord

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) {η:ℝ} (pos:0<η):
    ∀ᶠ m:ℕ in atTop,∀N p n (live:m+n ≤ N) (z:Site ((C₀).side (m+n) p)),
      ∃ (home:Opened C₀ d m p) (high:Opened C₀ d (m+n) p) (A:(C₀).label d →ₗ[ℂ] (C₀).label d),
        Issued R d η N p m n live z home high A := by
  obtain ⟨a,hi⟩:=WilsonOriginalNullPlacedFullMatrix.original R d simple shop pos
  obtain ⟨u,usable⟩:=eventually_atTop.mp (open_late (C:=C₀) simple d)
  filter_upwards [eventually_ge_atTop (max u a)] with m hm
  intro N p n live z
  let y:=ancestry R p (m+n) z
  have planted:∀j<n, ((C₀).path.levels.clock.op (m+j) p).ratio.parent (y (m+j+1))=y (m+j):=fun j hj=>
    route R p (m+n) z (by omega)
  obtain ⟨home,A,pay⟩:=hi m ((le_max_right ..).trans hm) N p n live y planted
  obtain high:=usable (m+n) (by omega) p
  refine ⟨home,high,A,pay,?_⟩
  intro v b e parent a body π coord
  have eq:=WilsonOriginalNullOriginGridMatrix.site R d N p m n η live home high y A pay e
  have lower:y m=parent:=dif_pos (show m ≤ m+n by omega)
  have upper:y (m+n)=z:=starts R p (m+n) z
  dsimp only at eq
  simp only [e,b,LinearEquiv.symm_apply_apply,LinearEquiv.apply_symm_apply] at eq
  rw [lower,upper] at eq
  exact eq

end YM.Integration.WilsonOriginalNullOriginGridRoster
