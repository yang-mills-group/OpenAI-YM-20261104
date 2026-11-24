import YM.Integration.WilsonSeparatedMovingCells
import YM.Integration.WilsonSeparatedDiagnosticGram

/-! The actual signed local correlation and its whole captured label
against a genuine separated external roster of any grades, with all
near input vectors chosen after the common length. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPlottedExterior
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Cells OPE OPE.Orbits OPE.Cards Spec
open PhysMS Trace.Pilot Frontier6.Road Next.UVStress SharedIntrinsicWilsonGrid ContinuumIntrinsicWilsonProduct IntrinsicWilsonTensor
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I E : Type} [Fintype I] [Fintype E] {d : I → ℕ} {D : ℕ}

private theorem columns (d:I→ℕ) :
    ∃ B : ℝ, 0≤B ∧ ∀ m : MultilinearMap ℂ (fun i=>Input C (d i)) ℂ, ∀ b : ℝ,
      (∀ a : Code (fun i=>Input C (d i)),‖m (combination _ a)‖≤b) →
      ∀ v,‖m v‖≤B*b*(∏ i,‖v i‖) := by
  classical
  let P (i:I) := Input C (d i)
  let coord (a : Code P) (i:I) := ((Module.finBasis ℂ (P i)).coord (a i)).toContinuousLinearMap
  let size (a : Code P) := ∏ i,‖coord a i‖
  have sn (a : Code P) : 0 ≤ size a := Finset.prod_nonneg fun _ _=>ContinuousLinearMap.opNorm_nonneg _
  have invoice (a:Code P) (v:(i:I)→P i) : ‖coords P a v‖ ≤ size a*∏ i,‖v i‖ := by
    unfold coords size
    rw [norm_prod,←Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>(coord a i).le_opNorm _)
  refine ⟨∑ a:Code P,size a,Finset.sum_nonneg (fun a _=>sn a),?_⟩
  intro m b raw v
  let p := ∏ i,‖v i‖
  have positive : 0≤p := Finset.prod_nonneg fun i _=>norm_nonneg _
  rw [basis_tuple P v m]
  calc
    _ ≤ ∑ a:Code P,‖coords P a v*m (combination P a)‖ := norm_sum_le ..
    _ ≤ ∑ a:Code P,size a*(b*p) := Finset.sum_le_sum fun a _=>by
      rw [norm_mul]
      exact (mul_le_mul (invoice a v) (raw a) (norm_nonneg _) (mul_nonneg (sn a) positive)).trans_eq (by ring)
    _ = (∑ a:Code P,size a)*(b*p) := (Finset.sum_mul ..).symm
    _ = _ := (mul_assoc ..).symm

private theorem allowance (P : Plan C D (Fintype.card I) (∑ i,d i)) (e : E→ℕ) (σ:ℝ) (cap : σ<1/32) :
    ∃ b:ℝ,0<b ∧ 3*b<P.h ∧ σ+(∑ i,((e i:ℝ)+1)*(4*b))<1/32 := by
  have lead : Tendsto (fun b:ℝ=>3*b) (𝓝[>] 0) (𝓝 0) := by
    have h:Tendsto (fun b:ℝ=>b) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [mul_zero] using (tendsto_const_nhds (x:=(3:ℝ))).mul h
  have tail : Tendsto (fun b:ℝ=>σ+∑ i,((e i:ℝ)+1)*(4*b)) (𝓝[>] 0) (𝓝 σ) := by
    have hc : Continuous (fun b:ℝ=>σ+∑ i,((e i:ℝ)+1)*(4*b)) := by fun_prop
    simpa only [mul_zero,Finset.sum_const_zero,add_zero] using (hc.continuousAt (x:=0)).tendsto.mono_left nhdsWithin_le_nhds
  have positive : ∀ᶠ b:ℝ in 𝓝[>] 0,0<b := self_mem_nhdsWithin
  exact (positive.and ((lead.eventually (gt_mem_nhds P.pos)).and (tail.eventually (gt_mem_nhds cap)))).exists

theorem original (F : Final C f S) (fac : Facilities C f S) (anchor : I)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C D (Fintype.card I) (∑ i,d i)) (J : ℝ→tower S) (lead : Leading F J)
    {g:ℝ→ℝ} (hg : Coupling G g) (e:E→ℕ) (budget:E→ℝ) (funded:∀ i,0<budget i)
    {η σ:ℝ} (ηp:0<η) (cap:σ<1/32) (k:ℕ) {ε:ℝ} (εp:0<ε) :
    ∀ᶠ r in trail,∀ x : I → Cover,Plot C (P.b r) (P.middle r) (P.j r) x →
      ∀ Z:Tensor C d D, Common F Q J r (P.b r) (P.j r) x Z →
      let near := C.S.gridPoint (P.j r) ∘ x
      ∀ y:E→E4,ClearOf 0 y η → Injective (beside near y) →
      ∀ w:Labels S e,(∀ i,‖S.representative _ (w i)‖≤budget i) →
      ∀ q:Viewers F,q=none ∨ Screen near → ∀ v:(i:I)→Input C (d i),
        ‖whole (spectator F q) near (Frame.born J r v) y w -
          upon (spectator F q) D 0 y w (S.project D (Z v))‖ ≤
            ε*g r^k*r^D*r^σ*∏ i,‖v i‖ := by
  let X := fun i=>Input C (d i)
  obtain ⟨B,nb,invoice⟩ := columns (C:=C) d
  let ε' := ε/(B+1)
  have ε'p : 0<ε' := div_pos εp (by linarith only [nb])
  have coupon : B*ε'≤ε := by
    dsimp only [ε'];rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith only [nb])).mpr
    nlinarith only [εp.le]
  obtain ⟨b,bp,inner,loss⟩ := allowance P e σ cap
  have stocks (u : Code X) := WilsonSeparatedMovingCells.original F fac anchor Q P J lead (combination X u)
    hg fac.simpleGate e budget funded bp inner σ loss k ε' ε'p
  have macroClear := ((PhysMS.length_rate.rpow b).tends (by linarith only [bp]) PhysMS.to_log_zoom).eventually_lt_const ηp
  filter_upwards [Filter.eventually_all.mpr stocks,macroClear,length_rate.pos,hg.positive] with r paid space rp gp x plot Z common near y clear placed w bounded q phase v
  change 0<r at rp
  have safe : ClearOf 0 y (r^b) := ⟨fun i=>space.le.trans (clear.openSpace i),fun i j ne=>space.le.trans (clear.spread i j ne)⟩
  let T:=spectator F q
  let nearMap := (sectionLabels (d:=Sum.elim d e) w (Orbits.moment T (beside near y))).compLinearMap
    (fun i=>(J r (d i)).toLinearMap)
  let gap := nearMap-(upon T D 0 y w).compMultilinearMap ((S.project D).compMultilinearMap Z)
  have value (a:(i:I)→X i) : gap a=whole T near (Frame.born J r a) y w-upon T D 0 y w (S.project D (Z a)) := by
    change sectionLabels (d:=Sum.elim d e) w (Orbits.moment T (beside near y)) (Frame.born J r a)-_=_
    rw [sectionLabels_apply]
    rfl
  have each (u:Code X) : ‖gap (combination X u)‖≤ε'*g r^k*r^D*r^σ := by
    let a:=combination X u
    have receipt:= (paid u x plot).2 (Z a) (common.cluster a) y safe placed w bounded
    rw [value]
    rcases phase with rfl|screen
    · exact receipt.1
    · exact receipt.2 screen q
  rw [←value v]
  have finish := invoice gap (ε'*g r^k*r^D*r^σ) each v
  apply finish.trans
  have positivePrice : 0≤g r^k*r^D*r^σ := mul_nonneg (mul_nonneg (pow_nonneg gp.le _) (pow_nonneg rp.le _)) (Real.rpow_nonneg rp.le _)
  have nN : 0≤∏ i,‖v i‖ := prod_nonneg (fun i _=>norm_nonneg _)
  have final := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right coupon positivePrice) nN
  simpa only [mul_assoc] using final

end YM.Integration.WilsonSeparatedPlottedExterior
