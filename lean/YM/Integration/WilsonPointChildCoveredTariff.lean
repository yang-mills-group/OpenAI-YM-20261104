import YM.Integration.WilsonPointChildInverseIncome
import YM.Integration.WilsonPointChildWinding

/-! The pinned normalized upper source on the true test space. A single
    anchored address has the filed MarkU diameter. Price the operator norm at
    each stencil using its true common test wallet, including field rank zero. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildCoveredTariff
open YM Lattice RG Wilson Filter Function Finset PowerSeries Next.Free Stationary PhysicalNext.Repeat.Legato Next.Foundations
open Laurent FormalBulk08 Reef Flat Lava Lotus Shore Mesa Gorge Rift Kemp Pose Aster Roof Dawn
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open WilsonPointChildFiledPress WilsonNeutralPointCourse
open scoped Topology ContDiff ENNReal Matrix BigOperators Classical
variable {G:Gauge}{α ι:Type}{d D r:ℕ}

local instance studio_group (D:ℕ):NormedAddCommGroup (Dawn.Studio D):=inferInstance
local instance studio_space (D:ℕ):NormedSpace ℝ (Dawn.Studio D):=inferInstance
local instance gallery_group (D:ℕ):NormedAddCommGroup (Dawn.Gallery D):=inferInstance

theorem diameter (p:ι → Cover)(s:ι)(o:α)(x:dock Cover α r):
    Syn terrain p {s} x≤wide (fame α) (Fin.cons (p s,o) x):=by
  let y:Fin (r+1) → Cover×α:=Fin.cons (p s,o) x
  have assign (i:({s}:Finset ι)⊕Fin r):∃k:Fin (r+1),(y k).1=foyer p {s} x i:=by
    rcases i with ⟨t,h⟩|t
    · have eq:t=s:=Finset.mem_singleton.mp h
      exact ⟨0,by subst t;rfl⟩
    · exact ⟨t.succ,rfl⟩
  apply league_le
  intro i j
  obtain ⟨u,hu⟩:=assign i
  obtain ⟨v,hv⟩:=assign j
  change size (foyer p {s} x j-foyer p {s} x i)≤_
  rw [←hv,←hu]
  exact reached (fame α) y v u

theorem tested (p:ι → Cover)(s:ι)(o:α){σ C:ℝ}(hs:0≤σ){K:Tile (Biglot α) r}
    (funded:Knoxville (fame α) σ (p s,o) K C):Wig terrain p σ C {s} K:=by
  refine ⟨funded.1,?_⟩
  intro x
  let y:Fin (r+1) → Cover×α:=Fin.cons (p s,o) x
  have cap:=
    (ENNReal.le_tsum (f:=fun v=>Gorge.shine σ (wide (fame α) (Fin.cons (p s,o) v))*‖K v‖ₑ) x).trans funded.2
  rw [Gorge.shine,←ofReal_norm,←ENNReal.ofReal_mul (Real.exp_pos _).le] at cap
  have tariff:Real.exp (σ*(Syn terrain p {s} x))*‖K x‖≤C:=
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (diameter p s o x)) hs)) (norm_nonneg _)).trans
      ((ENNReal.ofReal_le_ofReal_iff funded.1).mp cap)
  rw [neg_mul,Real.exp_neg]
  exact (le_mul_inv_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using tariff)

def linear (Y:Anthem D G)(law:IsLinearMap ℝ Y)(e r:ℕ)(x:chain (edgeL G) r):Studio D→ₗ[ℝ]ℝ where
  toFun q:=Y q e r x
  map_add' q f:=by rw [law.map_add];rfl
  map_smul' t q:=by rw [law.map_smul];rfl

theorem operator (p:ι → Cover)(s:ι)(o:Loc G 1){σ C:ℝ}(hs:0≤σ)(cn:0≤C)
    (Y:Anthem D G)(law:IsLinearMap ℝ Y)(e r:ℕ)
    (funded:∀q:Studio D,Knoxville (fame _) σ (p s,o) (Y q e r) (C*‖q‖)):
    ∃K:chain (edgeL G) r→Dawn.Gallery D,
      (∀x q,K x q=Y q e r x) ∧ Wig terrain p σ C {s} K:=by
  let cap (x:chain (edgeL G) r):=C*Real.exp (-σ*Syn terrain p {s} x)
  have credit (x:chain (edgeL G) r)(q:Studio D):‖linear Y law e r x q‖≤cap x*‖q‖:=by
    have cost:=(tested p s o hs (funded q)).2 x
    exact cost.trans_eq (by dsimp [cap];ring)
  let K (x:chain (edgeL G) r):Dawn.Gallery D:=(linear Y law e r x).mkContinuous (cap x) (credit x)
  exact ⟨K,fun _ _=>rfl,cn,fun x=>(K x).opNorm_le_bound (mul_nonneg cn (Real.exp_pos _).le) (credit x)⟩

/-- Every used physical tensor entry, priced on the actual normalized upper
    point graph before both regulators, in the independent diameter convention. -/
theorem original (R:Run G)(wood:Primer.Families R.family)(a:G.ColorIndex)(depth:d<D)(o:Loc G 1)(simple:G.Simple)
    {orders:ℕ→ℕ}(granted:WilsonWindowFormalPurchase.Canonical orders R.kit)
    (slow:∀j,((R.family.S.block j).val:ℝ)≤Real.log (RG16.Lambda R.family.path.levels j))
    {E:ℕ}(weak:WilsonPointChildInverseIncome.Weak R wood a depth o E)
    (fwd:WilsonPointChildInverseIncome.Forward R wood a depth E){η:ℝ}(hp:0<η):
    ∀ᶠi:ℕ in atTop,∀N,i≤N→∀digit:∀j,Site (R.family.S.block j),
      ∀v:Letter (R.family.labels.level d),∀e≤E,∀r,∃K:chain (edgeL G) r→Dawn.Gallery D,
      (∀x q,K x q=filed R wood a depth digit N i v q e r x) ∧
      Wig terrain (fun _:Unit=>0) (width R i) ((R.family.path.levels.clock.hatBeta i)^η) {()} K:=by
  have bill:=WilsonPointChildInverseIncome.income R wood a depth o simple granted weak fwd
  filter_upwards [R.family.path.levels.fits.deep.eventually_ge_atTop d,
    WilsonPointChildWidthHistory.original R wood a depth o simple granted slow E bill hp] with i awake fund
  intro N live digit v e cap r
  have court:=WilsonNeutralPointCourse.original R wood a depth digit N i simple o live
    (awake.trans (R.family.path.levels.fits.mono (Nat.le_succ i)))
  have h:=fund N live digit
  exact operator (fun _:Unit=>0) () o (WilsonPointChildWidthPurchase.prices R granted i).1.le h.1
    _ (court.officers v).toIsLinearMap e r (fun q=>h.every court v q e cap r)

end YM.Integration.WilsonPointChildCoveredTariff
