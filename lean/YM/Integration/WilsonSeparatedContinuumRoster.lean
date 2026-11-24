import YM.Integration.WilsonSeparatedMovingSignedCorrelation

/-! Uniform signed separation on the original continuum field, before all
near input vectors, all continuum positions, and all the presold far arms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedContinuumRoster
open Filter Set Function Spec OPE OPE.Orbits PhysMS Trace.Pilot Pert Pert.Position RG17 Extraction Table Climb
open MS MS.Land MS.Menus MS.Local.Physical OPE.Nesting OPE.Levy Next.UVStress OPE.Cards
open Frontier6.Road PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonSeparatedMovingRichGeometry WilsonSeparatedMovingRichVacuum
open scoped BigOperators Classical Topology
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {V:Table R.family.book} {I:Type} [Fintype I] {d:I→ℕ}

private lemma amplify {I:Type} [Fintype I] (Y:I→Type) [∀i,NormedAddCommGroup (Y i)] [∀i,NormedSpace ℂ (Y i)]
    [∀i,FiniteDimensional ℂ (Y i)] {ε:ℝ} (ep:0<ε) :
    ∃ t:ℝ,0<t ∧ ∀ form:MultilinearMap ℂ Y ℂ,∀ ρ:ℝ,0≤ρ→(∀ u:Code Y,‖form (combination Y u)‖≤t*ρ)→
      ∀ v:(i:I)→Y i,‖form v‖≤ε*ρ*(∏ i,‖v i‖) := by
  let fee (u:Code Y):=∏ i,‖((Module.finBasis ℂ (Y i)).coord (u i)).toContinuousLinearMap‖
  have fpos (u):0≤fee u:=Finset.prod_nonneg fun _ _=>norm_nonneg _
  let A:=∑ u:Code Y,fee u
  have α:0≤A:=Finset.sum_nonneg fun u _=>fpos u
  let t:=ε/(A+1)
  have tp:0<t:=div_pos ep (by linarith only [α])
  have settle:A*t≤ε:=by
    calc
      _≤(A+1)*t := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) tp.le
      _=ε := by dsimp only [t];field_simp [show A+1≠0 by linarith only [α]]
  refine ⟨t,tp,?_⟩
  intro localMap ρ positive paid v
  let N:=∏ i,‖v i‖
  have np:0≤N := Finset.prod_nonneg fun _ _=>norm_nonneg _
  have curve (u:Code Y):‖coords Y u v‖≤fee u*N := by
    unfold coords
    rw [norm_prod,←Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun _ _=>norm_nonneg _) fun i _=>((Module.finBasis ℂ (Y i)).coord (u i)).toContinuousLinearMap.le_opNorm _
  rw [basis_tuple Y v localMap]
  calc
    _≤∑ u:Code Y,‖coords Y u v*localMap (combination Y u)‖ := norm_sum_le _ _
    _≤∑ u:Code Y,fee u*(t*ρ*N) := Finset.sum_le_sum fun u _=>by
      rw [norm_mul]
      exact (mul_le_mul (curve u) (paid u) (norm_nonneg _) (mul_nonneg (fpos u) np)).trans_eq (by ring)
    _=A*(t*ρ*N) := (Finset.sum_mul ..).symm
    _=(A*t)*(ρ*N) := by ring
    _≤ε*(ρ*N) := mul_le_mul_of_nonneg_right settle (mul_nonneg positive np)
    _=_ := by dsimp only [N];ring

private def difference {E:Type} [Fintype E] {e:E→ℕ} (J:ℝ→tower V) (x:I→E4) (y:E→E4) (w:Labels V e) (r:ℝ) :
    MultilinearMap ℂ (fun i=>Free R.family (d i)) ℂ :=
  (sectionLabels (d:=Sum.elim d e) w (Orbits.moment V (beside x y))).compLinearMap (fun i=>(J r (d i)).toLinearMap)-
  (upon V 0 0 y w (V.unit 0)) • (Orbits.moment V x).compLinearMap (fun i=>(J r (d i)).toLinearMap)

private lemma read {E:Type} [Fintype E] {e:E→ℕ} (J:ℝ→tower V) (x:I→E4) (y:E→E4) (w:Labels V e) (r:ℝ)
    (v:(i:I)→Free R.family (d i)):
    difference J x y w r v=whole V x (Frame.born J r v) y w-Orbits.moment V x (Frame.born J r v)*upon V 0 0 y w (V.unit 0) := by
  change sectionLabels (d:=Sum.elim d e) w (Orbits.moment V (beside x y)) (Frame.born J r v) -
    upon V 0 0 y w (V.unit 0)*Orbits.moment V x (Frame.born J r v)=_
  rw [sectionLabels_apply,mul_comm]
  rfl

theorem original (hG:G.Simple) (F:Final R.family f V) (fac:Facilities R.family f V)
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J:ℝ→tower V) (lead:Leading F J)
    {A:(Bel R.family.book).Hierarchy} (obey:∀ h:ℕ,∀ᶠ r in trail,Frame.obedient F A (J r) h)
    (B:Deck G) (D:ℕ) (φ:Test 2) (d:I→ℕ) {a M η γ:ℝ} (ap:0<a) (top:a<1) (mp:0≤M) (ηp:0<η)
    (gap:γ<1-a) {g:ℝ→ℝ} (hg:Coupling G g) (k:ℕ) {ε:ℝ} (ep:0<ε) :
    ∀ᶠ r in trail,∀ x:I→E4,WithinRoom r M η x 0→∀ u∈tsupport φ,∀ b:Glyph B D,∀ v:(i:I)→Free R.family (d i),
      let y:=far (r^a) u
      let w:=fields B D b J (r^a)
      let ins:=Frame.born J r v
      ‖whole V x ins y w-Orbits.moment V x ins*upon V 0 0 y w (V.unit 0)‖≤ε*g r^k*r^γ*∏ i,‖v i‖ := by
  let Y (i:I):=Free R.family (d i)
  obtain ⟨t,tp,issue⟩:=amplify Y ep
  have publish (z:Code Y):=WilsonSeparatedMovingSignedCorrelation.original hG F fac Q J lead obey B D φ
    (combination Y z) ap top mp ηp gap hg k tp
  filter_upwards [Filter.eventually_all.mpr publish,length_rate.pos,hg.positive] with r full rp gp x hx u hu b v
  let y:=far (r^a) u
  let w:=fields B D b J (r^a)
  let signed:=difference (d:=d) J x y w r
  let ρ:=g r^k*r^γ
  have p0:0≤ρ:=mul_nonneg (pow_nonneg gp.le _) (Real.rpow_nonneg rp.le _)
  have rows (z:Code Y):‖signed (combination Y z)‖≤t*ρ := by
    rw [show signed (combination Y z)=_ from read J x y w r (combination Y z)]
    simpa only [ρ,mul_assoc] using full z x hx u hu b
  have scaled:=issue signed ρ p0 rows v
  rw [show signed v=_ from read J x y w r v] at scaled
  simpa only [ρ,mul_assoc] using scaled

end YM.Integration.WilsonSeparatedContinuumRoster
