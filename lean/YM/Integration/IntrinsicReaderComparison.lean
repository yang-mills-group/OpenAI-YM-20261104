import YM.Integration.PhysicalWilsonTensorReadout

/-! Identification of the original regulated intrinsic tensor with the
physical continuum Reader packet at arbitrary coupling order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.IntrinsicReaderComparison
open Function Filter Lattice Wilson OPE OPE.Orbits OPE.Cards PhysMS
open Frontier6.Road EngineeringWeightedReadout MultilinearCellCapture
open Trace.Pilot SharedIntrinsicWilsonGrid IntrinsicWilsonTensor PhysicalWilsonTensorReadout
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ} {D : ℕ}

private def native (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (t : ℝ) (x : I → E4) : Tensor C d D :=
  (S.representative D).compMultilinearMap ((∑ k : Fin (D+1),
    (F.sector.derivatives.rise (Nat.le_of_lt_succ k.isLt)).compMultilinearMap (R.fresh k.val (d:=d) x 0)).compLinearMap
      (fun i => (J t (d i)).toLinearMap))

private theorem native_apply (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (t : ℝ) (x : I → E4) (v : (i : I) → Input C (d i)) :
    S.project D (native F R J t x v) = R.packet D x (Frame.born J t v) 0 := by
  simp only [native,LinearMap.compMultilinearMap_apply,S.rep,MultilinearMap.compLinearMap_apply,
    _root_.sum_apply,Reader.packet,LinearEquiv.coe_coe]
  rfl

/-- A finite physical basis pays the norm of the complete multilinear
map on all independently chosen inputs, including unequal input caps. -/
theorem basis_norm :
    ∃ K : ℝ, ∀ (M : MultilinearMap ℂ (fun i => Input C (d i)) (Input C D)) (A : ℝ),
      (∀ q : IntrinsicWilsonTensor.Columns C d, ‖M (Next.UVStress.combination (fun i => Input C (d i)) q)‖ ≤ A) →
      ∀ v : (i : I) → Input C (d i), ‖M v‖ ≤ (K*A) * ∏ i, ‖v i‖ := by
  let E := fun i => Input C (d i)
  let B := IntrinsicWilsonTensor.Columns C d
  let base (i : I) := Module.finBasis ℂ (E i)
  let coord (q : B) (i : I) := ((base i).coord (q i)).toContinuousLinearMap
  let K (q : B) := ∏ i, ‖coord q i‖
  refine ⟨∑ q : B, K q,?_⟩
  intro M A limit v
  let V := ∏ i, ‖v i‖
  have hM : M v = ∑ q : B, Next.UVStress.coords E q v • M (Next.UVStress.combination E q) := by
    have full : v = fun i => ∑ q, (base i).repr (v i) q • base i q := funext fun i => ((base i).sum_repr _).symm
    conv_lhs => rw [full]
    rw [M.map_sum]
    exact Finset.sum_congr rfl fun q _ => M.map_smul_univ _ _
  have hc (q : B) : ‖Next.UVStress.coords E q v‖ ≤ K q*V := by
    rw [Next.UVStress.coords,norm_prod,← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => (coord q i).le_opNorm (v i))
  change ‖M v‖ ≤ ((∑ q : B, K q)*A)*V
  rw [hM,Finset.sum_mul,Finset.sum_mul]
  apply (norm_sum_le ..).trans
  exact Finset.sum_le_sum fun q _ => by
    rw [norm_smul]
    exact (mul_le_mul (hc q) (limit q) (norm_nonneg _) (mul_nonneg (Finset.prod_nonneg (fun i _ => (coord q i).opNorm_nonneg))
      (Finset.prod_nonneg (fun i _ => norm_nonneg _)))).trans_eq (by ring)

theorem reader_price (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J) (hF : Foundation F R) (U : Detector S D)
    (M η : ℝ) (hM : 0≤M) (hη : 0<η) :
    ∃ A : ℝ, ∀ᶠ t in trail, ∀ x : I → E4, WithinRoom t M η x 0 →
      ∀ v : (i : I) → Input C (d i), ‖wholeReadout U J t (detectorOPEError F R J v U t x)‖ ≤
        A*t^(1/2:ℝ)*∏ i, ‖v i‖ := by
  obtain ⟨K,hK⟩ := basis_norm (C:=C) (d:=d) (D:=D)
  let c := ‖LinearMap.toContinuousLinearMap U.report‖
  let v₀ := Next.UVStress.combination (fun i => Input C (d i))
  refine ⟨K*c,?_⟩
  filter_upwards [eventually_all.mpr (fun q => detectorOPE_whole_readout_power F R U J H hF (v₀ q) M η hM hη
    (1/2) (by norm_num))] with t basis
  intro x room v
  let X := residual U J t x (native (d:=d) F R J t x)
  have eq (u : (i : I) → Input C (d i)) : X u = wholeReadout U J t (detectorOPEError F R J u U t x) := by
    rw [show X = _ from rfl,residual_apply,native_apply]
    rfl
  have bound (q : IntrinsicWilsonTensor.Columns C d) : ‖X (v₀ q)‖ ≤ c*t^(1/2:ℝ) := by
    rw [eq]
    convert basis q x room using 1
    norm_num [c]
  rw [← eq]
  exact (hK X _ bound v).trans_eq (by ring)

private theorem native_gap (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (U : Detector S D) (t : ℝ) (y : I → E4) (v : (i : I) → Input C (d i))
    (z : C.label D) : (J t D).symm (S.project D z - R.packet D y (Frame.born J t v) 0) =
      wholeReadout U J t (detectorOPEError F R J v U t y) -
        wholeReadout U J t (PhysicalMSOPEReadout.candidateResidual J U v t y (S.project D z)) := by
  let all (a : Fin U.size) := whole S y (Frame.born J t v) (OPE.positions S (U.listen a)).ofLp
    (fun j => (OPE.tags S (U.listen a) j).2)
  have scan (q : S.Field D) : wholeReadout U J t (PhysicalMSOPEReadout.candidateResidual J U v t y q) =
      wholeReadout U J t all - (J t D).symm q := by
    change wholeReadout U J t (all - fun a => witnessAt S D (U.listen a) q) = _
    rw [map_sub,wholeReadout_field]
  change _ = wholeReadout U J t (PhysicalMSOPEReadout.candidateResidual J U v t y
    (R.packet D y (Frame.born J t v) 0)) - _
  rw [scan,scan,map_sub]
  abel

/-- In the common separated room the intrinsic output is the continuum
Reader output up to an error with a positive engineering power in the
same physical frame, uniformly as a multilinear operator. -/
theorem engineering (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C D (Fintype.card I) (∑ i, d i)) (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J)
    (hF : Foundation F R) (M η : ℝ) (hM : 0≤M) (hη : 0<η) :
    ∃ e : ℝ → ℝ, RateLE trail LogV e (-(1:ℝ)/32) ∧
      ∀ᶠ t in trail, ∀ x : I → Cover, Plot C (P.b t) (P.middle t) (P.j t) x →
        let y := fun i => C.S.gridPoint (P.j t) (x i)
        WithinRoom t M η y 0 → ∀ Z : Tensor C d D, Common F R J t (P.b t) (P.j t) x Z →
          ∀ v : (i : I) → Input C (d i),
            ‖(J t D).symm (S.project D (Z v) - R.packet D y (Frame.born J t v) 0)‖ ≤ e t * ∏ i, ‖v i‖ := by
  let U := Classical.choice (has_detectors F.room.kernel D)
  obtain ⟨K,room⟩ := reader_price (d:=d) F R J H hF U M η hM hη
  obtain ⟨e,he,_,actual⟩ := PhysicalWilsonTensorReadout.estimate F facility anchor R P U J H
  let hT := PhysMS.to_log_zoom
  have rate : RateLE trail LogV (fun t => K*t^(1/2:ℝ)) (-(1:ℝ)/32) := by
    apply ((RateLE.const K hT).mul ((PhysMS.length_rate.rpow (1/2)).pays hT)).mono
    norm_num
  refine ⟨fun t => K*t^(1/2:ℝ)+e t,rate.add he hT,?_⟩
  filter_upwards [room,actual] with t source certified
  intro x plotted y separated Z founded v
  rw [native_gap F R J U]
  exact (norm_sub_le ..).trans ((add_le_add (source y separated v) (certified x plotted Z founded v)).trans_eq (by rw [add_mul]))

/-- The same actual tensor agrees with the Reader packet to every prescribed
power of the physical running coupling. -/
theorem coupling (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C D (Fintype.card I) (∑ i, d i)) (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J)
    (hF : Foundation F R) (M η : ℝ) (hM : 0≤M) (hη : 0<η)
    (g : ℝ → ℝ) (hg : Coupling G g) (k : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ t in trail, ∀ x : I → Cover, Plot C (P.b t) (P.middle t) (P.j t) x →
      let y := fun i => C.S.gridPoint (P.j t) (x i)
      WithinRoom t M η y 0 → ∀ Z : Tensor C d D, Common F R J t (P.b t) (P.j t) x Z →
        ∀ v : (i : I) → Input C (d i),
          ‖(J t D).symm (S.project D (Z v) - R.packet D y (Frame.born J t v) 0)‖ ≤
            ε*g t^k * ∏ i, ‖v i‖ := by
  obtain ⟨e,he,paid⟩ := engineering F facility anchor R P J H hF M η hM hη
  have fee := (RateIs.const PhysMS.to_log_zoom hε).mul ((PhysMS.coupling_rate hg facility.simpleGate).power k)
  rw [mul_zero,zero_add] at fee
  filter_upwards [paid,fee.outweigh he (by norm_num) PhysMS.to_log_zoom] with t bound accepted
  intro x hx y geom Z actual v
  exact (bound x hx geom Z actual v).trans (mul_le_mul_of_nonneg_right ((Real.le_norm_self _).trans accepted)
    (Finset.prod_nonneg fun i _ => norm_nonneg (v i)))

end YM.Integration.IntrinsicReaderComparison
