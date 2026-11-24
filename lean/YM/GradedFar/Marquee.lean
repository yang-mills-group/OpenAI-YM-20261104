import YM.GradedFar.Reel
import YM.GradedFar.Pan
/-!
# M4 post-selection price. Fixed input extension
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
namespace Window
open Function Filter Set MeasureTheory Metric PowerSeries
open Extraction Table Spec OPE OPE.Orbits PhysMS Trace.Pilot
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh MS MS.Native MS.Land MS.Fleet
open FVA2.GradedFar.Cart Tariff
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} (F : Final C f S) (J P: ℝ→tower S) (R: Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable (Z:WilsonPrescription G)(M: MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true) (ν:ℝ) {t:ℝ→ℝ}
variable {n h d:ℕ} {e:Fin n→ℕ} (l:Toon G d)
local notation "X"=> Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
abbrev Cargo (A:Arenas G) (x:Points n)(u:AppointedH140Inputs G e)(l:Toon G d):= ope A u x (Dframe.flash l)
lemma cargo_crop (p:ℕ)(t:ℝ)(u:AppointedH140Inputs G e)(x:Points n): coord l (croppedVector X d p u x t)=appointedH140Crop p t (Cargo X x u l):=by
 unfold croppedVector; rw [map_sum,Finset.sum_eq_single l]
 · rw [map_smul,pivotδ,if_pos rfl,smul_eq_mul,mul_one]
 · intro i _ he; rw [map_smul,pivotδ,if_neg (by aesop),smul_zero]
 simp
lemma cargo_basis {A:Arenas G}(x:Points n)(u: AppointedH140Inputs G e): Cargo A x u l=∑ a:Picks G e, PowerSeries.C (multipliers u a) * Cargo A x (basisWord a) l:=by
 simp_rw [Cargo, ope_basis]; rfl
-- receives property from estimates in comparisonOPE on all basis labels and independent center uniforms
abbrev Regained (V:Arenas G)(t:ℝ→ℝ) (n h d:ℕ) : Prop := ∀ {e: Fin n→ℕ}, AppointedH140Through h e → ∀ K:Set (Points n), IsCompact K→K ⊆ conf n→∀ l:Toon G d,∀ u:AppointedH140Inputs G e,
    Receives t trail (fun r (i:E4 × ↥K)=> messenger F P R i.1 r l i.2.val u) (fun i=> Cargo V i.2.val u l)
include H
lemma cargo_cont (u:AppointedH140Inputs G e)(i:ℕ) : ContinuousOn (fun x=> coeff i (Cargo X x u l)) (conf n):=by
  simp_rw [Cargo,ope,map_sum,coeff_C_mul]; exact continuousOn_finsetSum _ fun k _=> (((H.separatedOPE 0).wilson.far _).2.1 _ i).const_mul _
include ν H
variable (Ht:Batch.Pose F J Z t)(HP:Batch.Prepared F J P Z t) (Hq:LogTrace F R.port)
include Ht HP Hq
lemma unit_price (he:AppointedH140Through h e) {K:Set (Points n)}(hK:IsCompact K)(hx:K⊆conf n) (u:AppointedH140Inputs G e)(hu:Box u 1) :
 Receives t trail (fun r (i:E4 × ↥K)=> messenger F P R i.1 r l i.2.val u) (fun i=> Cargo X i.2.val u l):=by
 obtain hv:= Ht.running; obtain ho:= hv.positive
 refine ⟨fun i=>?_,fun i=>?_⟩
 · obtain ⟨D,hd⟩:= hK.exists_bound_of_continuousOn ((cargo_cont Z M H _ u i).mono hx); exact Charge.cap ⟨D, fun x=> hd x.2.val x.2.property⟩
 obtain ⟨D,hD,Hx⟩:=Batch.comparisonOPE F R J P Z M H ν Ht HP Hq (d:= max h d) (h:=d) (e:=e) (fun i=> (he i).trans (le_max_left ..)) (le_max_right ..) hK hx i
 refine ⟨D,hD,?_⟩; filter_upwards [Hx,ho] with r hr hp x; obtain ht:=hr x.1 x.2.val x.2.property u hu; rw [abs_of_pos hp,alarm,← cargo_crop,← map_sub]; rw [bookVector Z M H ν] at ht; exact (coord_le ..).trans ht
lemma regain : Regained F P R X t n h d:=by
 intro e he K hK hx l u; rw [-- simp_rw cargo loses recursive!
  show (fun i:E4 × ↥K=>Cargo X i.2.val u l)=fun i=>∑ a:Picks G e,PowerSeries.C (multipliers u a)*Cargo X i.2.val (basisWord a) l from funext (fun i=>cargo_basis _ i.2.val u),
  show (fun r (i:E4 × ↥K)=> messenger F P R i.1 r l i.2.val u)= fun r i=> ∑ a: Picks G e, multipliers u a * messenger F P R i.1 r l i.2.val (basisWord a) from funext (fun r=> funext (fun i=> basis_sum _ _ ))]
 refine Receives.sum _ (fun i _=> Receives.mul (Receives.fix _) (unit_price F J P R Z M H ν l Ht HP Hq he hK hx _ (fun i q=>?_)) (Coupling.conforms hG Ht.running))
 rw [basis_letter, pivotδ]; split_ifs <;> simp
omit H ν Ht Hq HP
section
variable {V:Arenas G}(ht:Coupling G t)(hμ:∀ i, ∀ j, ∀ (hj:j ≤ i), Neighbor.Included F P j i hj) (hq: Regained F P R V t n h d)
include ht hμ hq hG
lemma cargo_inclusions {x:Points n}(hx:x∈conf n)(he:AppointedH140Through h e)(u: AppointedH140Inputs G e): Cargo V x (GradedFar.raised he u) l=Cargo V x u l:=by
 obtain hv:=Receives.along (hq (fun i=>le_rfl) {x} isCompact_singleton (singleton_subset_iff.mpr hx) l (GradedFar.raised he u)) (fun _:Unit=> (0,⟨x,Set.mem_singleton _⟩)) -- supply Through
 obtain hf:= Receives.along (hq he _ isCompact_singleton (singleton_subset_iff.mpr hx) l u) (fun _:Unit=>(0,⟨x, Set.mem_singleton _⟩))
 refine Receives.same (Coupling.conforms hG ht) (ht.positive.mono fun _ h=> h.ne') ?_ hf (F:=fun (_:Unit)=>Cargo V x (GradedFar.raised he u) l) ()
 refine hv.congr ?_ (fun _=> rfl); exact (eventually_all.mpr (fun i=> hμ _ _ (he i))).mono (fun r hr=> funext fun _=> resurface F P R 0 r l he hr x u)
end
end Window
end YM.Integration.GradedFar
