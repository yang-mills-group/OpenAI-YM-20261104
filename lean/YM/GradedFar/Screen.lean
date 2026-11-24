import YM.GradedFar.Test

import YM.GradedFar.Progress
import YM.OPE.Orbits.Continuity
/-!
# Paired (M.3) tests with finite vector/signed variation: cost at the original scale
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
open Filter Function Set Spec Table Extraction
open OPE OPE.Orbits
open Trace.Pilot PhysMS XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.O.Enh FVA2.GradedFar
open FVA2.Scale FVA2.O.Score FVA2.Dframe
open MS MS.Book MS.Fleet MS.Land FVA2.Register MeasureTheory
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{fo:Extraction.Order}{S:Table C.book}(F:Final C fo S)
    (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J:ℝ→tower S)
    {n m l h p p':ℕ} {d:Fin n→ℕ}{e:Fin m→ℕ}
lemma radius_conf {r T:ℝ} (hr:0<r)(o:E4){x:Points n}{y:Points m}(h:forest x (T • y)∈ conf (n+m)) :
    Injective (beside (sites o r x) (sites o (r*T) y)) := by
  let e : Fin n ⊕ Fin m ≃ Fin (n+m) := finSumFinEquiv
  let z := forest x (T • y)
  have hj : Injective (z.ofLp ∘ e):= (show Function.Injective z.ofLp from h).comp e.injective
  rw [show beside (sites o r x) (sites o (r*T) y) = fun i=>o+r • z (e i) from ?_]
  · exact fun _ _ h=>hj (smul_right_injective E4 hr.ne' (add_left_cancel h))
  funext i; rcases i with i|i <;> simp [e,z,sites,mul_smul]
lemma center_conf {r T:ℝ}(hr:0<r) (o:E4) {y:Points m}(hy:outgoing (T•y)∈conf (1+m)) :
    Injective (beside (sole o) (sites o (r*T) y)):= by
  have hh:= beside_distinct.mp (radius_conf hr o hy)
  apply beside_distinct.mpr; refine ⟨injective_of_subsingleton _, hh.2.1,?_⟩
  intro _ i h; exact hh.2.2 0 i (by simpa [sites] using (show o= _ from (h:o= sites o (r*T) y i)))

lemma near_collar (n m:ℕ) {K:Set (Points n)}(hK:IsCompact K)(hx:K⊆ conf n) :
    ∀ᶠ r in trail,∀ x∈ K,∀ o,∀ i ≤ m, orbitMargin R.port i (sites o r x) o:=by
  obtain ⟨M,hM,δ,hδ,Hc⟩:=compact_within K hK hx
  filter_upwards [self_mem_nhdsWithin, (eventually_all_finset (Finset.Iic m)).2 (fun i _=>Fork.occupied
    (I:=Fin n) F R.port hM hδ i)] with r (hr:0<r) hj x he o i hi
  apply hj i (Finset.mem_Iic.mpr hi) (⟨sites o r x,o⟩:Fork.Launch (Fin n)); specialize Hc x he; constructor
  · intro j; have he:=Hc.span j; change ‖(o+r • x j)-o‖ ≤ M*r
    rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hr.le, mul_comm]; exact mul_le_mul_of_nonneg_right (by simpa using he) hr.le
  intro i j ne; have he:=Hc.spaced i j ne; change _ ≤ ‖o+r • x i-(o+r • x j)‖; rw [add_sub_add_left_eq_sub,
    ← smul_sub,norm_smul,Real.norm_of_nonneg hr.le,mul_comm]; exact mul_le_mul_of_nonneg_left (by simpa using he) hr.le

section
variable {X:Type*} [TopologicalSpace X] (x:X→Points n)(y:X→ Points m)(o:X→E4)(ν:Viewers F)
    (u:Inputs G d)(v:Inputs G e)(hx:Continuous x)(hy:Continuous y)(ho:Continuous o)
@[fun_prop]
lemma continuous_sites (ho:Continuous o)(hr:Continuous x)(r:ℝ) : Continuous (fun i=> sites (o i) r (x i)):=by
  apply continuous_pi; intro j; unfold sites; fun_prop
include hx hy ho
lemma continuousY {r T:ℝ}(H:0<r) (hz:∀ i, forest (x i) (T • y i)∈ conf (n+m)) :
    Continuous (fun i=>atLength F J ν (o i) r T (x i) (y i) u v):= by
  simp_rw [atLength, today_apply]; apply continuous_iff_continuousAt.mpr; let z (i:X) : Loc (Fin n) (Fin m) :=
    (sites (o i) r (x i),o i,sites (o i) (r*T) (y i)); intro i
  exact (whole_cont_at (labels J r u) (labels J (r*T) v) _ (spectate F ν) (x:=z i) (radius_conf H _ (hz i))).comp
    ((continuous_sites x o ho hx r).prodMk (ho.prodMk (continuous_sites y o ho hy _))).continuousAt
omit hx
lemma continuousD {r T:ℝ}(a:Sec G h)(H:0<r) (hz:∀ i, outgoing (T•y i)∈ conf (1+m)) :
    Continuous (fun i=> atCenter F J h ν (o i) r T (y i) v a):= by
  simp_rw [center_length]; exact continuousY F J (fun _=>0) y o ν (d:=Output h) (fun _=>a) v continuous_const hy ho H hz
include hx
lemma continuousPack {r T:ℝ}(H:0<r) (he:∀ i, forest (x i) (T • y i) ∈ conf (n+m))(hz:∀ i, outgoing (T•y i)∈ conf (1+m))
    (hq:∀ i,∀ j≤h, orbitMargin R.port j (sites (o i) r (x i)) (o i)):
    Continuous (fun i=> atCenter F J h ν (o i) r T (y i) v (packet F J R h (o i) r (x i) u)):=by
  let z (i:X): Loc (Fin n) (Fin m):= (sites (o i) r (x i),o i,sites (o i) (r*T) (y i)); let v' := labels J (r*T) v; let u':=labels J r u
  have hf(i:X): atCenter F J h ν (o i) r T (y i) v (packet F J R h (o i) r (x i) u)=
    Orbits.trunc (spectator F ν) F R h (z i).1 (o i) u' (z i).2.2 v' := by
      rw [sameCenter F J e h ν _ _ _ _ _ (center_conf H (o i) (hz i))];
      change upon (spectator F ν) h _ _ v' (assign J r h (_)) = _; rw [packet,LinearEquiv.apply_symm_apply];
      exact packet_read F R _ _ _ _ _ _ _ (center_conf H _ (hz i))
  simp_rw [hf]
  apply continuous_iff_continuousAt.mpr; intro i
  exact (trunc_cont_at F R u' v' h ν (z:=z i) ⟨hq i,radius_conf H _ (he i),center_conf H _ (hz i)⟩).comp
    ((continuous_sites x o ho hx r).prodMk (ho.prodMk (continuous_sites y o ho hy _))).continuousAt
variable (N:WilsonPrescription G) {hG:G.Simple}(Z:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:MS.Land.Prescription (Press.portDeck G)}(H:Main.Match N hG Z σ true)(ρ:ℝ)
local notation "A" => Scale.Measure.outlook N.scheme N.criterion
local notation "W" => GroupS.gaugeN N.scheme N.criterion Z ρ
include H ρ
lemma continuousVectorResponse {r T:ℝ}(H':0<r) (hz:∀ i, outgoing (T•y i)∈conf (1+m))(hK:∀ i, x i∈ conf n)
    (p:ℕ) (t:ℝ)(h:ℕ): Continuous (fun i=> atCenter F J h ν (o i) r T (y i) v
      (croppedVector A h p u (x i) t)):= by
  have hw:= (H.separatedOPE ρ).wilson
  have hv : ∀ a : Toon G h, Continuous (fun i => crop p t (ope A u (x i) (Dframe.flash a))) := by
    intro a
    have hf (j : ℕ) (q : Scan G n) : Continuous (fun i => PowerSeries.coeff j (FVA2.O.Canon.FarCoefficients A q (x i) (Dframe.flash a))) := by
      apply continuous_iff_continuousAt.mpr; intro i; exact (((hw.far q).2.1 _ j).continuousAt ((conf_open n).mem_nhds (hK i))).comp hx.continuousAt
    simp_rw [crop_eq, ope, map_sum, PowerSeries.coeff_C_mul]; fun_prop
  simp_rw [croppedVector,map_sum,_root_.map_smul]
  exact continuous_finsetSum _ fun i _=> (hv i).smul (continuousD F J y o ν v hy ho _ H' hz)
end
end YM.Integration.GradedFar
