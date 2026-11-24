import YM.Integration.WilsonSeparatedOriginalSlabFourierArea
import YM.Integration.WilsonSeparatedOriginalSlabTestNorm

/-! The actual parent area, every relative ultraviolet child and the common Wilson center lie in one preassigned Fourier cube. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabFourierPositions
open Function Set Filter MeasureTheory Lattice Wilson RG RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Flatten RG05Readout.Pulse
open private location from YM.Integration.WilsonSeparatedOriginalReplicaRegularity
open scoped BigOperators Classical Topology ContDiff
abbrev I := Fin 3
abbrev Axes:=I×Axis

def axes (x:Cloud I):Axes→ℝ:=fun ij=>(x ij.1) ij.2

def form : (Axes→ℝ)→L[ℝ]Cloud I:=ContinuousLinearMap.pi (fun i:I=> (PiLp.continuousLinearEquiv 2 ℝ (fun _:Axis=>ℝ)).symm.toContinuousLinearMap.comp
  (ContinuousLinearMap.pi (fun d:Axis=>ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Axes=>ℝ) (i,d))))

theorem coordinate (y:Axes→ℝ)(i:I)(d:Axis):(form y i) d=y (i,d):=rfl

theorem read (x:Cloud I):form (axes x)=x:=by ext i d; rfl

def gross {G:Gauge}(C:Family G)(b J:ℕ)(r:ℝ):ℝ:=r⁻¹*(2*C.S.a b*(J:ℝ)+2*C.S.a b)

theorem held {G:Gauge}{C:Family G}{b N per:ℕ}(J:ℕ)(o:I→Site (C.side b per))
    (admit:o∈Pulse.area (C:=C) (b:=b) (p:=per) J)(top:b≤N){r:ℝ}(rp:0<r)
    (t:I→Site (C.S.toDepth top per).count){z:E4}(hz:z∈Native.box):
    ‖axes (location o top r t z)‖≤gross C b J r:=by
  have A:=C.S.a_pos b
  have ip:=inv_pos.mpr rp
  have zp:‖z‖≤1:=Pert.Cellular.cells_bd hz
  have colors:∀i,separation (o i) 0≤J:=by simpa only [Pulse.area,Finset.mem_filter,Finset.mem_univ,true_and] using admit
  apply (pi_norm_le_iff_of_nonneg (by unfold gross; positivity)).mpr
  rintro ⟨i,d⟩
  have orig:‖C.S.place (o i)‖≤2*C.S.a b*(J:ℝ):=(MergeProof.Ribbons.normC C b per (o i)).2.trans
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (colors i)) (by positivity))
  have fine:‖placeR (C.S.toDepth top per) (t i)‖≤1:=Pert.Cellular.cells_bd (by
    simpa only [smul_zero,add_zero] using mapsR (C.S.toDepth top per) (C.S.toDepth_odd top per) (t i) Native.box0)
  refine (PiLp.norm_apply_le ((location o top r t z) i) d).trans ?_
  change ‖r⁻¹ • (C.S.place (o i)-C.S.a b • z)+(r⁻¹*C.S.a b) • placeR _ (t i)‖≤_
  calc
    _≤r⁻¹*(‖C.S.place (o i)‖+C.S.a b*‖z‖)+(r⁻¹*C.S.a b)*‖placeR _ (t i)‖:=by
      refine (norm_add_le ..).trans ?_
      rw [norm_smul,norm_smul,Real.norm_of_nonneg ip.le,Real.norm_of_nonneg (mul_nonneg ip.le A.le)]
      exact add_le_add (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans_eq (by rw [norm_smul,Real.norm_of_nonneg A.le])) ip.le) le_rfl
    _≤r⁻¹*(2*C.S.a b*(J:ℝ)+C.S.a b*1)+(r⁻¹*C.S.a b)*1:=
      add_le_add (mul_le_mul_of_nonneg_left (add_le_add orig (mul_le_mul_of_nonneg_left zp A.le)) ip.le)
        (mul_le_mul_of_nonneg_left fine (mul_nonneg ip.le A.le))
    _=gross C b J r:=by unfold gross;ring

end YM.Integration.WilsonSeparatedOriginalSlabFourierPositions
