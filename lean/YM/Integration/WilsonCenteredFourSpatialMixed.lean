import YM.Integration.WilsonCenteredFourSpatialForms

/-! The fixed finite chart purchases its directions before either of the two
running near colors, or the reflected far color, are chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourSpatialMixed
open Function Filter Set Finset Spec Table OPE OPE.Orbits PhysMS Trace.Pilot Climb
open PhysicalNext.Repeat.Legato WilsonThermometerWeakPairClock WilsonCenteredFourSpatialNodes
open OPE.Levy XSpace.Normalize
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→PhysMS.tower S)
local notation "d₄" => (fun _:Fin 2=>4)

theorem original (V:Store G)(simple:G.Simple)(g:ℝ→ℝ)(hg:Coupling G g)
    (lead:Leading F J)(salary:WilsonThermometerWeakPairSector.Salary F Q J){M δ:ℝ}(m0:0≤M)(δ0:0<δ):
    ∃(D:ℕ)(C:ℝ),0≤C ∧ ∀(p:ℕ)(ε:ℝ),0<ε→∀ B:ℕ,D+p+1≤B→∀ᶠr in trail,
      let t:=scale g B r
      ∀(x:Points 2)(z:E4),‖x 0‖≤M→‖x 1‖≤M→‖z‖≤M→2*δ≤‖z‖→δ≤‖x 0-x 1‖→
      Injective (beside (fun i=>r • x i) (sole (t • z)))→Injective (beside (sole (0:E4)) (sole (t • z)))→
      ∀(v:Fin 2→RG17.Free R.family 4)(a:RG17.Free R.family 4),
      let u:=fun i=>J r 4 (v i)
      ‖defect (S:=S) 4 (fun i=>r • x i) u (Q.packet 4 (fun i=>r • x i) (d:=d₄) u 0)
          (t • z) (J t 4 a)‖≤C*(∏i,‖v i‖)* (‖a‖*(ε*g r^p*(r/t)^4)):=by
  let b:=Module.finBasis ℂ (RG17.Free R.family 4)
  let I:=Fin (Module.finrank ℂ (RG17.Free R.family 4))
  let axes (u:Fin 2→I):=fun i=>b (u i)
  choose D C c0 pay using fun j:Fin 2→I=>WilsonCenteredFourSpatialBasis.original F Q J V simple g hg lead salary (axes j) m0 δ0
  let K:=∑j,D j
  let W:=∑j:Fin 2→I,(∏i,‖(b.coord (j i)).toContinuousLinearMap‖)*C j
  refine ⟨K,W,Finset.sum_nonneg (fun j _=>mul_nonneg (Finset.prod_nonneg fun i _=>(b.coord (j i)).toContinuousLinearMap.opNorm_nonneg) (c0 j)),?_⟩
  intro p ε ep B window
  have dk(j):D j≤K:=Finset.single_le_sum (fun k (_:k∈Finset.univ)=>Nat.zero_le _) (Finset.mem_univ j)
  have all:=eventually_all.mpr (fun j=>pay j p ε ep B (by have:=dk j;omega))
  filter_upwards [all,hg.positive,self_mem_nhdsWithin] with r paid gp (rp:0<r)
  dsimp only;intro x z x0 x1 z0 nz xy near far v a
  let t:=scale g B r
  let L:=WilsonCenteredFourSpatialForms.forms F Q (fun i=>r • x i) (t • z) (J t 4 a)
  let T:=L.compLinearMap (fun _:Fin 2=>(J r 4).toLinearMap)
  have id(u:Fin 2→RG17.Free R.family 4): T u=defect (S:=S) 4 (fun i=>r • x i) (fun i=>J r 4 (u i))
      (Q.packet 4 (fun i=>r • x i) (d:=d₄) (fun i=>J r 4 (u i)) 0) (t • z) (J t 4 a):=
    WilsonCenteredFourSpatialForms.actual F Q _ _ _ _ near far
  rw [←id]
  apply WilsonCenteredFourSpatialForms.directions b T v C
  intro j; rw [id]
  exact (paid j x z x0 x1 z0 nz xy near far a).trans_eq (by ring)
end YM.Integration.WilsonCenteredFourSpatialMixed
