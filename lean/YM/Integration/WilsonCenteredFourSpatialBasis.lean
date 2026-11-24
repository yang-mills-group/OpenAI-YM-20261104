import YM.Integration.WilsonCenteredFourSpatialNodes

/-! Test the complete moving physical far functional on an actual normalized
basis. This admits a moving far vector at its original norm on the same frame. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourSpatialBasis
open Function Finset Filter Set Climb Spec Table OPE OPE.Orbits OPE.Arboreal OPE.Levy
open PhysMS PhysMS.Frame Trace.Pilot PhysicalNext.Repeat.Legato XSpace.Normalize
open WilsonCenteredFourSpatialNodes WilsonThermometerWeakPairClock
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→PhysMS.tower S)

private lemma bill {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E]
    {ι:Type}[Fintype ι](b:Module.Basis ι ℂ E)(T:E→ₗ[ℂ]ℂ)(v:E)(a:ℝ)
    (charged:∀i,‖T (b i)‖≤a):
    ‖T v‖≤(∑i,‖(b.coord i).toContinuousLinearMap‖)*‖v‖*a:=by
  have expn:T v=∑i,b.repr v i*T (b i):=by
    conv_lhs=>rw [←b.sum_repr v]
    rw [map_sum]; simp only [map_smul,smul_eq_mul]
  rw [expn,Finset.sum_mul,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum;intro i _
  rw [norm_mul]
  exact mul_le_mul ((b.coord i).toContinuousLinearMap.le_opNorm v) (charged i) (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem original (V:Store G)(simple:G.Simple)(g:ℝ→ℝ)(hg:Coupling G g)
    (lead:Leading F J)(salary:WilsonThermometerWeakPairSector.Salary F Q J)
    (v:Fin 2→RG17.Free R.family 4){M δ:ℝ}(m0:0≤M)(δ0:0<δ):
    ∃(K:ℕ)(C:ℝ),0≤C ∧ ∀(p:ℕ)(ε:ℝ),0<ε→∀ B:ℕ,K+p+1≤B→∀ᶠ r in trail,
      let t:=scale g B r
      let u:=fun i=>J r 4 (v i)
      ∀(x:Fin 2→E4)(z:E4),‖x 0‖≤M→‖x 1‖≤M→‖z‖≤M→2*δ≤‖z‖→δ≤‖x 0-x 1‖→
        Injective (beside (fun i=>r • x i) (sole (t • z)))→
        Injective (beside (sole (0:E4)) (sole (t • z)))→∀a:RG17.Free R.family 4,
          ‖defect (S:=S) 4 (fun i=>r • x i) u (Q.packet 4 (fun i=>r • x i) (d:=fun _:Fin 2=>4) u 0)
              (t • z) (J t 4 a)‖≤C*‖a‖*(ε*g r^p*(r/t)^4):=by
  let b:=Module.finBasis ℂ (RG17.Free R.family 4)
  let I:=Fin (Module.finrank ℂ (RG17.Free R.family 4))
  let pre:I→RG17.Free R.family 4:=fun i=>reflect 4 (b i)
  have undo(i:I):reflect 4 (pre i)=b i:= (Bel R.family.book).reflect_twice _ 4 timeAxis _
  obtain ⟨K,pay⟩:=salary V g hg I (fun _ _=>4) (fun _=>4) 4 (fun _=>lift v) pre (fun _=>none) M δ m0 δ0
  refine ⟨K,∑i,‖(b.coord i).toContinuousLinearMap‖,Finset.sum_nonneg (fun i _=>(b.coord i).toContinuousLinearMap.opNorm_nonneg),?_⟩
  intro p ε ep B bought
  filter_upwards [pay p ε ep B bought,(small simple g hg B).eventually (lead.equivariant 4)]
    with r actual eq
  dsimp only
  intro x z a0 a1 z0 nz xy clr ex a
  let t:=scale g B r
  let u:=fun i=>J r 4 (v i)
  let Y:=Q.packet 4 (fun i=>r • x i) (d:=fun _:Fin 2=>4) u 0
  let T:RG17.Free R.family 4→ₗ[ℂ]ℂ:=
    (defect (S:=S) 4 (fun i=>r • x i) u Y (t • z)).comp (J t 4).toLinearMap
  apply bill b T a
  intro i
  have h:=actual i (x 0) (x 1) z a0 a1 z0 nz xy
  have fareq:(WilsonThermometerWeakMovingCorner.far F J 4 t (pre i)).2 = J t 4 (b i):=by
    rw [←undo i];exact (Frame.flip_coupled F 4 J t eq (pre i)).symm
  rw [slots, fareq] at h
  change ‖formula F Q (lift (fun i=>r • x i)) 0 (d:=fun _:↥WilsonThermometerWeakPairRooms.near=>4)
            (lift u) (sole (t • z)) (sole (J t 4 (b i)):Labels S (fun _:Unit=>4)) 4 none‖≤_ at h
  rw [signed F Q _ _ _ _ clr ex] at h
  exact h

end YM.Integration.WilsonCenteredFourSpatialBasis
