import YM.SignedWilsonExpansion.Belle.Buffet
/-! # First light $t$ on W through Rose test.Elected clocks. Sign.
-/
set_option autoImplicit false
set_option maxHeartbeats 660000
noncomputable section
namespace YM.SignedWilsonExpansion.Belle
open FVA2 FVA2.Dframe FVA2.Scale Dancer Dancer.Drawing Dancer.SeatsW
open Function Filter Asymptotics MeasureTheory Set XSpace XSpace.Structure1 Normalize
open MS MS.Menus MS.Puff MS.High MS.Land MS.Native MS.Fleet Maxwell Maxwell.Free Maxwell.Wick
open WilsonCoeffUV.Mer.Xa MarqueQ Crops PorchK PowerSeries Lesson Path Commission
open Buffet Rose Scale.Select
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge} {a b m n d:ℕ}{ι X:Type}{L:Filter ι}{t ν:ℝ}
namespace Lark
variable (W:Initialize G){V: Normalize.Store G}(K: Rose.Pick V){Y:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {S:Prescription (Press.portDeck G)}(M:Speed.Quoted W K Y S)(s:G.Simple)
variable {τ ε:ι→ℝ}
local notation "T"=> FVA2.Scale.Measure.start W K 6
local notation "c"=> Rose.c_T K
local notation "f"=> Rose.test K
abbrev Vials (G:Gauge)(p:Badge): Tags G 6 3:= Rose.missing (Rose.tag G) p
include s M
lemma frozen (p:Points 3)(hk:p∈conf 3): coeff 0 (Single T p)=0:=by
    let U:= (fun j=> Rose.batchT (Jury.fxt T p) j); have he(j:Badge)(b:j.Nonempty): coeff 0 (U j)=0:=by
       unfold U batchT; rw [coeff_mk, Jury.fxt,dif_pos hk,Method.orderd0 s Y S W K M.toContract 3]; exact Rose.silent W s hk j b
    unfold Single b3; change coeff 0 ( U Finset.univ - _+ _ ) = _; simp_rw [ ← show U=Rose.batchT _ from rfl, two_smul] -- expressions fully
    rw [coeff_zero_eq_constantCoeff_apply]; have hh(j: Badge)(b:j.Nonempty): constantCoeff ( U j )=0:=by rw [← coeff_zero_eq_constantCoeff_apply]; exact he j b
    simp [ hh Finset.univ (by decide), hh {0,1} (by decide), hh {0,2} (by decide), hh {1,2} (by decide), hh {0} (by decide) ]
lemma frozen_field : coeff 0 ( Scale.Select.output K T ) =0:=by
    rw [Scale.Select.output,coeff_mk,Test.apply_eq f (P:=fun _=> (0:ℂ)) (fun y h=> frozen W K M s y h)]; simp [ Test.applyTo ]
lemma straight : Scale.Select.output K T=(↑( c ):ℂ) • PowerSeries.X :=by
    have he:= M.toContract.meant; rw [ Scale.Select.meter,Reg.Choice.tune,frozen_field W K M s,map_zero,sub_zero] at he; conv=>rhs; rw [←he]; rw [smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr K.fresh.ne)] -- ok
lemma stamina (d:ℕ): ContinuousOn (fun y:Points 3=>calcT (t:ℂ) d (Single T y)) (conf 3):=by simp_rw [timed]; exact continuousOn_finsetSum _ (fun i _=> (Scale.Select.steady _ ( Method.official s Y S 0 W K M.toContract ).light).mul_const _)
lemma meterPays (t:ℝ)(hp:0<b): Test.applyTo f (fun y=>calcT (t:ℂ) b (Single T y))= ↑( c )*( t:ℂ ):=by
    rw [show Test.applyTo _ _ = calcT ( t:ℂ ) b (Scale.Select.output K T) from ?_ , straight W K M s, map_smul]; change _= _; rw [timed, Finset.sum_eq_single 1]; · simp
    · intro i _ h; rw [coeff_X, if_neg h,zero_mul] -- eq direction?
    · simp [hp]
    -- integrand finite. unify powers.
    unfold Test.applyTo; simp_rw[timed,Finset.mul_sum, ← mul_assoc]; rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun i _=> by rw [integral_mul_const, Scale.Select.output,coeff_mk]; rfl
    intro i _; exact ((f).smearing ( Scale.Select.steady _ ((Method.official s Y S 0 W K M.toContract).light) )).mul_const _
variable (X:ι→Badge→ Points 3→ ℂ)
omit M s
def thermometer (i:ι): ℂ:= (f).applyTo fun y=> cumul fun u=> X i u y
-- name reading numerical $φ$ exactly manuscript
noncomputable abbrev clockW (i:ι):ℝ:=(thermometer K X i).re/c
variable (r:Tendsto τ L (𝓝 0))(s0:ε=O[L](1:ι→ℝ))(tip:(fun i=> τ i^(b+1))=o[L] ε)
variable (H:∀ p:Badge,Serves L (fun i y=> X i p y) (fun i y=> Path.mote (FVA2.Scale.Measure.start W K 6) b y (τ i) ( Vials G p )) (tsupport (Rose.test K)) ε)
variable (h:∀ᶠ i in L,∀ p:Badge,ContinuousOn ( X i p ) (conf 3))(u:0<b)
lemma actual {X:Badge→ Points 3→ ℂ}(h:∀ p,ContinuousOn (X p) (conf 3)): ContinuousOn (fun i=> cumul fun p=> X p i) (conf 3) := by
    unfold cumul; exact ( (h _).sub ((((h _).mul (h _)).add ((h _).mul (h _))).add ((h _).mul (h _)))) |>.add ((((h _).mul (h _)).mul (h _)).const_mul _)
include M s r s0 tip H h u
lemma foreground : (fun i=> thermometer K X i - ↑( c )*(τ i:ℂ))=o[L] ε:=by
     have hv := Buffet.paysB W K M s X (Vials G) _ ( Path.Testi f ) s0 H r tip; let ρ(i):=τ i; let φ:= f
     have ht := paidProfile φ (y:=fun i u=> calcT (ρ i) b (Single T u)) hv ( h.mono fun i p=> actual p) (Eventually.of_forall fun _=> stamina W K M s b); exact ht.congr_left fun i=> by rw [show φ=f from rfl, meterPays W K M s _ u]; rfl
lemma fortune : ( clockW K X - τ)=o[L] ε:= by
     let ρ(i):= τ i; let C':= Complex.reCLM; have hp:= ( (C'.isBigO_id _).comp_tendsto Filter.tendsto_map ).trans_isLittleO (foreground W K M s X r s0 tip H h u); refine ( hp.const_mul_left (c)⁻¹ ).congr_left (?_)
     intro i; change ( c )⁻¹ * ( _ - _ :ℂ ).re= clockW K X i - _; rw [Complex.sub_re,←Complex.ofReal_mul,Complex.ofReal_re]; unfold clockW; field_simp [K.fresh.ne] -- field_simp identifies c via rfl?
end Lark
end YM.SignedWilsonExpansion.Belle
