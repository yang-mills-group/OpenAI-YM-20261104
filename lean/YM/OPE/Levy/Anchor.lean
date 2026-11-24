import YM.OPE.Levy.Procure

/-! # Engineering rate ticket of every finite row, along an actual weak curve

Simultaneous demands `E+1` and cutoff sublimits from `Levy.ranging_supply`.
No comparison of coefficients between different choices of Final. Adapted
from YM/Next/UV_STRESS/Rates.lean (`Stations.build_curve`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Levy
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Climb RG Next.UVStress
open Bid Dash Next.Extract Push.RelayDifference Spec
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{F:Order}{B R}{A S:Table C.book} {V W:DiffPlan S}
   (L:Base C F A B R S V) (hu: W.Inclusions S) (hg:G.Simple) (hQ:RoughFactory C) (h:Stocked C F)
   (hO:F.Ordered C S)(hPt:F.PointLimits C S)
def zstamp (R:Zoom)(i:ℕ):= -Real.log (R.r i)
lemma zlarge (Z:Zoom): Tendsto (zstamp Z) atTop atTop:=by
  exact Filter.tendsto_neg_atTop_iff.mpr (Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨Z.limits,Eventually.of_forall Z.positive⟩))

/-- `< e`-plane pricing, applicable to every complementary splitting. -/
def Anchored (Ω:DiffPlan S)(X:Zoom)(U:ℕ→Panel S):Prop :=
   ∀ (d e:ℕ) (he:e≤d) (x:(Bel C.book).Field d)(φ:S.Field d→ₗ[ℂ] ℂ), (∀ y∈planeAt (U:=Ω) (d:=d) e he, φ y = 0) →
          RateLE atTop (zstamp X) (fun i=> φ (U i d x)) (-(e:ℝ))

variable {H:S.Hierarchy}
def Uses (Ω:DiffPlan S)(Z:Zoom)(U:ℕ→Panel S):Prop :=
    ∀ (d:ℕ) (e:Fin (d+1)), ∀ (k:ℕ), d ≤k → ∀x, ∃ y∈plane (U:=Ω) e, ‖U k d x - y‖ ≤ Real.exp ((costHint k - (e:ℝ))*zstamp Z k) * ‖x‖
lemma uses_anchor {Z:Zoom}{U:ℕ → Panel S}(hs:Uses W Z U):Anchored W Z U:=by
   intro d e he x φ hz
   let t:=zstamp Z
   have hu: RateIs atTop t (fun k=>Real.exp ((costHint k -(e:ℝ))*t k)) (-(e:ℝ)):=by
     apply RateIs.exp'
     have he:= cost_clears.sub_const (e:ℝ); rw [zero_sub] at he
     refine he.congr' ?_
     filter_upwards [(zlarge Z).eventually_gt_atTop 0] with i hi using (Eq.symm (mul_div_cancel_right₀ (costHint i - (e:ℝ)) hi.ne'))
   let T':=φ.toContinuousLinearMap
   let q:= ‖T'‖*‖x‖
   suffices hf: RateLE atTop t (fun i=>q*Real.exp ((costHint i-(e:ℝ))*t i) ) (-(e:ℝ)) by
      refine hf.of_norm_le (?_ :∀ᶠ i in atTop, ‖φ (U i d x)‖ ≤ _)
      filter_upwards [eventually_ge_atTop d] with i hi
      obtain ⟨v,hv,hv'⟩:=hs d ⟨e,Nat.lt_succ_of_le he⟩ i hi x
      calc _ = ‖φ (U i d x-v)‖:=by rw [map_sub,hz v hv,sub_zero]
           _ ≤ ‖T'‖ * ‖U i d x-v‖ :=T'.le_opNorm _
           _ ≤ ‖T'‖ * (Real.exp ((costHint i - ↑e)*t i)*‖x‖):= mul_le_mul_of_nonneg_left hv' (norm_nonneg T')
           _ = q * Real.exp _:=by unfold q; rw [mul_comm _ ‖x‖,←mul_assoc]
   simpa only [zero_add] using (RateLE.const q (zlarge Z)).mul (hu.pays (zlarge Z))

include L hu hQ h hO hg hPt
lemma anchored_supply (hB:(Bel C.book).Hierarchy):
    ∃ (X:Zoom) (U:ℕ→Panel S),
      (∀ d, ∀ᶠ k in atTop, StraightAt H.spin hB.spin (U k) d) ∧ (∀ k, U k 0 ((Bel C.book).unit 0)=S.unit 0) ∧ Approaches X U ∧ Anchored W X U :=by
  obtain ⟨R,X,hX⟩:=ranging_supply L hu hg hQ h hO hPt hB.smooth hB.spin
  choose U hU hu1 hu' hz using fun k => harvested H hO hB.spin (X k) (hX k).2.1
  refine ⟨R,U,fun d => (eventually_ge_atTop d).mono fun k hk => hU k d hk, hu1,
           ⟨fun n v => ⟨fun k => (smoothZoom H.smooth (panels (U k) ∘ v) (R.positive k)).sub (smoothDisc hB.smooth _),?_⟩⟩, uses_anchor ?_⟩
  · intro s hK hC M hp ε he
    have hh : Tendsto (fun k => costHint k * Next.UVStress.Station.charge v * M) atTop (𝓝 0) := by
      simpa using (cost_clears.mul_const (Next.UVStress.Station.charge v)).mul_const M
    filter_upwards [eventually_ge_atTop n, eventually_all.mpr (fun i => eventually_ge_atTop (v i).1),
      size_ascends.eventually (Work.A05.compact_fits hK hC), hh.eventually (ge_mem_nhds he)] with k hk hs ht hx t hw hb
    rw [test_sub]
    · rw [← (hX k).1]; exact (hz k n hk v hs t (hw.trans ht) M hp hb).trans hx
    · exact (smoothZoom H.smooth (panels (U k) ∘ v) (R.positive k)).continuousOn
    exact (smoothDisc hB.smooth v).continuousOn
  intro d e k hk x
  obtain ⟨b,hb,hp,hM⟩:=hu' k
  let j:Fin (k+1):=⟨d,Nat.lt_succ_of_le hk⟩
  obtain ⟨z,hz,hU'⟩:= hM j x
  rw [show U k d x = S.project d z from hU']; exact (hX k).2.2 j e b hp x z hz
end YM.OPE.Levy
