import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Receive
/-!
# Income on `fresh` physical stratum after H Near vector inputs
and conversion back to Sec. No lower-weight residual discarded.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Original
open Function Filter Set MeasureTheory Asymptotics Lattice Wilson RG Source Extraction Table Spec
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Climb Maxwell XSpace XSpace.Normalize XSpace.Structure1 OPE OPE.Orbits PhysMS
open FVA2.Scale Comparing O.Score O.Enh Dframe ScaleCost Flash259HorizonFork
open scoped Topology BigOperators Classical Matrix
local notation "late" => 𝓝[>] (0:ℝ)
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Z : ℝ→PhysMS.tower S) (Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {N : WilsonPrescription G} {ν : ℝ}
    {O : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {sim : G.Simple}
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim O σ dial)
    {t : ℝ→ℝ} (hZ : Leading F Z) (hq : ∀ d, FieldQuote G (GroupS.gaugeN N.scheme N.criterion O ν) t (via Z) d 1)
    (hQ:SingleLog F Q.port)

variable {I J : Type}[Fintype I]{l : Filter J} {r:J→ℝ} (hr:Tendsto r l late)
    {d:I→ℕ} {h:ℕ} {M δ:ℝ}
    (u:J→(i:I)→Sec G (d i)) (x:J→ I→E4) (o:J→E4)
    (mn:0≤M) (dp:0<δ)
    (hu:∀ i b,Allowance l r (fun _=>1) (fun j=>FVA2.O.Score.coord b (u j i)))
    (hx:∀ᶠ i in l, WithinRoom (r i) M δ (x i) (o i))

local notation "P" => F.sector.derivatives
local notation "U" => fun j:J=> enter Z (r j) (u j)
include H hZ hq hr
lemma whole_income (v:J→ S.Field h) (paid:Allowance l r (fun i=> r i^h) v) (b:Toon G h) :
    Allowance l r (fun _=>1) (fun i=> coord b ((frame Z (r i) h).symm (v i))) := by
  let A := Module.finBasis ℂ (S.Field h)
  have e (i:J) : coord b ((frame Z (r i) h).symm (v i))=∑ j, LinearMap.toContinuousLinearMap (A.coord j) (v i) * coord b ((frame Z (r i) h).symm (A j)) := by
    nth_rw 1 [← A.sum_repr (v i)]; simp only [map_sum,_root_.map_smul]; rfl
  simp_rw [e]
  refine Allowance.sum hr _ _ fun j _=>?_ ; refine (Allowance.mul (Allowance.linear (LinearMap.toContinuousLinearMap (A.coord j)) paid) (free_label F Z H hZ hq hr (A j) b)).extend ?_
  filter_upwards [hr.eventually self_mem_nhdsWithin] with i hi; rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ (ne_of_gt (show 0< r i from hi)))]
include hQ hx hu mn dp
private lemma significance (b:Toon G h) {k:ℕ} (e:k ≤ h) :
    Allowance l r (fun _=>1) (fun i=> coord b ((frame Z (r i) h).symm (F.sector.derivatives.rise e (Q.fresh k (x i) (o i) (U i))))) := by
  let v:= fun i:J=> Q.fresh k (x i) (o i) (U i)
  have hf: Allowance l r (fun i=> r i^k) v := by
    refine receiving F Z H hZ hq hr hr (Eventually.of_forall (fun i=>le_rfl)) d (fun i=> Q.fresh k (x i) (o i)) _ ?_ hu
    intro d he v; exact (basis_amount F Q mn dp hQ v k hr hx).congr (Eventually.of_forall fun i => (Q.fresh_inclusions he (x i) (o i) k v).symm)
  have z j:= whole_income F Z H hZ hq hr v hf j
  let w (i:J):= (frame Z (r i) k).symm (v i)
  refine (Allowance.sum hr Finset.univ (fun j: Toon G k=> fun i:J=> coord j (w i) * coord b (up e (theory j)))
    (fun j _=> (Allowance.mul (z j) (Allowance.fixed _)).extend (Eventually.of_forall (fun _=>one_mul _)))).congr ?_
  filter_upwards [hr.eventually (height hZ h)] with i hi; rw [ ← show frame Z _ _ _=(P).rise e (v i) from (hi _ e (w i)).trans (congr_arg _ ((frame Z (r i) _).apply_symm_apply (v i))), LinearEquiv.symm_apply_apply ]; symm
  nth_rw 1 [ ← all_sig (w i) ]; rw [map_sum,map_sum]; simp_rw [ _root_.map_smul ]; rfl

lemma packet_size (b:Toon G h) : Allowance l r (fun _=>1) (fun i=> coord b ((frame Z (r i) h).symm (Q.packet h (x i) (U i) (o i)))) := by
  simp_rw [Reader.packet,map_sum]; exact Allowance.sum hr _ _ (fun j _=> significance F Z Q H hZ hq hQ hr u x o mn dp hu hx b (Nat.le_of_lt_succ j.isLt))
end YM.FVA2.GradedFar259.Original
