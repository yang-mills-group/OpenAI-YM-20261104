import YM.Integration.WilsonSeparatedSharedRegulator
import YM.Integration.WilsonPhysicalRetainedCluster

/-! A common *whole physical* reference label at each separation cell,
for later measurement by the actual distant scalar probe. The original
complete source is evaluated on one basis, before any change of test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedRosterTerminal
open Function Set Filter Finset Real Extraction Lattice Wilson RG OPE OPE.Orbits OPE.Cards Spec
open PhysicalNext.Repeat.Legato Frontier6.Road Trace.Pilot SharedIntrinsicWilsonGrid RG16.Literal PhysMS
open Next.UVStress IntrinsicWilsonTensor MultilinearCellCapture FilteredIntrinsicGramReadout
open WilsonPhysicalRetainedCluster FilteredWilsonProduct IntrinsicProductCompactness
open scoped Classical BigOperators Topology
variable {G : Gauge} {R : Run G} {S : Table R.family.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ} {D : ℕ}

private def word (F : Final R.family f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → tower S) (t : ℝ) (g : Grades d) (a : Indices R.family (levels g)) :
    MultilinearMap ℂ (fun i => Input R.family (d i)) ℂ :=
  (MultilinearMap.mkPiAlgebra ℂ I ℂ).compLinearMap fun i =>
    (LinearMap.proj (a i)).comp ((S.representative _).comp ((Q.cutTest _ _).comp (J t (d i)).toLinearMap))

private def polynomial (Bank : Retained (d:=d) R D) (F : Final R.family f S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → tower S) (t : ℝ) (x : I → Cover) (w : ℕ×ℕ) :
    MultilinearMap ℂ (fun i => Input R.family (d i)) (R.family.label D) :=
  ∑ g : Grades d,∑ a : Indices R.family (levels g),(word F Q J t g a).smulRight (Bank g t x a w)

private theorem polynomial_at (Bank : Retained (d:=d) R D) (F : Final R.family f S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → tower S) (t : ℝ) (x : I → Cover) (w : ℕ×ℕ) (v : (i:I)→Input R.family (d i)) :
    polynomial Bank F Q J t x w v = basket R Bank F Q J v t x w := by
  simp only [polynomial,basket,_root_.sum_apply,MultilinearMap.smulRight_apply]
  rfl

private theorem expansion (M : Tensor R.family d D) (v : (i:I)→Input R.family (d i)) :
    M v=∑ u:Code (fun i=>Input R.family (d i)),coords (fun i=>Input R.family (d i)) u v • M (combination (fun i=>Input R.family (d i)) u) := by
  let b (i : I) := Module.finBasis ℂ (Input R.family (d i))
  have hv : v = fun i=>∑ j,(b i).repr (v i) j • b i j := funext fun i=>((b i).sum_repr _).symm
  conv_lhs => rw [hv]
  rw [M.map_sum]
  exact Finset.sum_congr rfl (fun u _=>M.map_smul_univ _ _)

theorem purchased (R : Run G) (hG : G.Simple) {V : Table R.family.book} (F : Final R.family f V)
    (fac : Facilities R.family f V) (anchor : I) (P : Plan R.family D (Fintype.card I) (∑ i,d i)) :
    ∃ Bank : Retained (d:=d) R D,
    ∀ (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J : ℝ → tower V), Leading F J → ∀ A:ℝ,
    ∀ᶠ t in trail,∀ U : Ultrafilter (ℕ×ℕ), U.toFilter≤f.fuse → ∃ Z : (I → Cover) → Tensor R.family d D,
      (∀ x,Plot R.family (P.b t) (P.middle t) (P.j t) x →
        WilsonSeparatedSharedRegulator.Along F Q J t (P.b t) (P.j t) x U (Z x)) ∧
      ∀ L : Set (I → Cover), L.Finite → (∀ x∈L,Plot R.family (P.b t) (P.middle t) (P.j t) x) →
      ∀ᶠ w in U.toFilter, ∀ x∈L,∀ v : (i:I)→Input R.family (d i),
        ‖basket R Bank F Q J v t x w-Z x v‖ ≤ exp (-A*LogV t)*(∏ i,‖v i‖) := by
  obtain ⟨Bank,bank⟩ := WilsonPhysicalRetainedCluster.all_inputs R hG F fac anchor P
  refine ⟨Bank,?_⟩
  intro Q J lead A
  let E := fun i=>Input R.family (d i)
  let C₀ (u:Code E) := ∏ i,‖((Module.finBasis ℂ (E i)).coord (u i)).toContinuousLinearMap‖
  let N (v:(i:I)→E i) := ∏ i,‖v i‖
  let B (u:Code E) := N (combination E u)+1
  let total := ∑ u:Code E,C₀ u*B u
  have grow := (Real.tendsto_exp_atTop.comp PhysMS.to_log_zoom).eventually_ge_atTop total
  filter_upwards [bank Q J lead (A+1),WilsonSeparatedSharedRegulator.refinements F fac anchor Q P J lead,grow]
    with t bought settled big U sub
  obtain ⟨Z,fixed⟩ := settled U sub
  refine ⟨Z,fixed,?_⟩
  intro L finite placed
  let fee := exp (-(A+1)*LogV t)
  have each (u:Code E) : ∀ᶠ w in U.toFilter,∀ x∈L,‖basket R Bank F Q J (combination E u) t x w-Z x (combination E u)‖≤B u*fee := by
    apply finite.eventually_all.mpr
    intro x hx
    let v:=combination E u
    let valueAt (w : ℕ×ℕ) := value (D:=D) F.room.cutoff (P.b t) w (field F Q J v t (P.j t) x w)
    have hg : Tendsto valueAt U.toFilter (𝓝 (Z x v)) := fixed x (placed x hx) v
    filter_upwards [((bought x (placed x hx)).1.filter_mono sub),hg.eventually (Metric.ball_mem_nhds _ (Real.exp_pos _))] with w raw seen
    have z : ‖valueAt w-Z x v‖≤fee := by simpa only [dist_eq_norm] using (Metric.mem_ball.mp seen).le
    have c : ‖basket R Bank F Q J v t x w-valueAt w‖≤fee*N v := by rw [norm_sub_rev];exact raw v
    exact ((norm_sub_le_norm_sub_add_norm_sub _ (valueAt w) _).trans (add_le_add c z)).trans_eq
      (by dsimp only [B,N,v];ring)
  filter_upwards [Filter.eventually_all.mpr each] with w used x hx v
  let M : Tensor R.family d D := polynomial Bank F Q J t x w-Z x
  have exactValue (v':(i:I)→E i) : M v'=basket R Bank F Q J v' t x w-Z x v' := by
    change polynomial Bank F Q J t x w v'-_=_
    rw [polynomial_at]
  have charged (u:Code E) : ‖M (combination E u)‖≤B u*fee := by rw [exactValue];exact used u x hx
  have invoice (u:Code E) : ‖coords E u v‖≤C₀ u*N v := by
    unfold coords C₀ N
    rw [norm_prod,←prod_mul_distrib]
    exact prod_le_prod (fun _ _=>norm_nonneg _) fun i _=>((Module.finBasis ℂ (E i)).coord (u i)).toContinuousLinearMap.le_opNorm _
  have nN : 0≤N v := prod_nonneg (fun i _=>norm_nonneg _)
  have cap (u:Code E) : 0≤C₀ u := prod_nonneg (fun i _=>((Module.finBasis ℂ (E i)).coord (u i)).toContinuousLinearMap.opNorm_nonneg)
  rw [←exactValue]
  calc
    ‖M v‖ = ‖∑ u:Code E,coords E u v • M (combination E u)‖ := by rw [expansion]
    _ ≤ ∑ u:Code E,‖coords E u v • M (combination E u)‖ := norm_sum_le ..
    _ ≤ ∑ u:Code E,(C₀ u*B u)*(fee*N v) := Finset.sum_le_sum fun u _=>by
      rw [norm_smul]
      exact (mul_le_mul (invoice u) (charged u) (norm_nonneg _) (mul_nonneg (cap u) nN)).trans_eq (by ring)
    _ = total*(fee*N v) := by rw [←Finset.sum_mul]
    _ ≤ exp (LogV t)*(fee*N v) := mul_le_mul_of_nonneg_right big (mul_nonneg (Real.exp_pos _).le nN)
    _ = _ := by dsimp only [fee,N];rw [←mul_assoc,←exp_add];congr 2;ring

end YM.Integration.WilsonSeparatedRosterTerminal
