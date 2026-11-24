import YM.MS.ScaleForest.Orchards
/-!
# The harvested recurrence in the official IR scheme

Compute operational cumulant glade coefficients from the normalized graph
symbol on all orders. This observer argument will work for position labels
or later actual sum applications. Keep the condition for the physical read
`Trip` (and `Fields`) precisely, including bulk history at each order k.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.Planted
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect High Latch Job Rake Geo Tone Momentum Osc Snap Fiddle Metric
open scoped Topology ContDiff
variable {G : Gauge} {I W J: Type} [LinearOrder W] [TopologicalSpace I] [FirstCountableTopology I] (V:Palette G)(K:W→Script G)(x:Rake.Position W I) {b:Bool}
variable (μ:ℝ)
local notation "Λ"=>constantP G I (PlanetD G)

def bulkStation (V:Palette G)(μ:ℝ) : Site G I:= fun n=> grove μ (bulks V n)
def pinStation (V:Palette G)(μ:ℝ) (A:Script G) : Site G I:= fun n=> projectV 0 (nominal μ ((marked V A.2 n).map bed))

lemma counted_terrain (X:Planted G I b)(h:X.Stand): collect (projectV 0 (resolve μ X)) := by
   obtain ⟨R,hR,hT,hP⟩:= (X.offers μ h).2.1 (1/2) (by norm_num) (by norm_num)
   refine ⟨ X.slots.toNat,fun i t l hl=>?_⟩; exact ranks_off (n:=0) (show Goods X.slots (backing 0 (resolve μ X) 0 t i) from need_rank.walk _ t (hT.funds 0 hR.top t i)) l (by omega)

lemma cloud_training (X:Planted G I true)(h:X.Stand): Job.train false (projectV 0 (push μ X)) := by
   obtain ⟨R,hR,hT,hP⟩:= X.pushing μ h (1/2) (by norm_num) (by norm_num); exact fun i s w _=> funded s i hT (hP 1) zero_lt_one (by norm_num) hR.top 0 w

lemma engaged (S:Plan G I true)(hp:Hired S):
    collect (projectV 0 (nominal μ S))∧ Job.train false (projectV 0 (interests μ S))∧ projectV 0 (nominal μ S)=Job.river (projectV 0 (interests μ S)):= by
   induction S with
   | nil=> simp only [nominal,interests,List.map_nil, List.sum_nil,map_zero,river0]; exact ⟨ collect_z,fun _ _ _ _=> integrable_zero ..,trivial⟩
   | cons i s ih=> obtain ⟨h,H⟩:= (hire_cons i s).mp hp; obtain ⟨ht,hT,hL⟩:= ih H; obtain he:= cloud_training μ i h; rw [show nominal μ _=_ + nominal μ s from (show nominal μ (i::s)=resolve μ i+nominal μ s from rfl), show interests μ _ = push μ i+interests μ s from rfl,map_add,map_add]; exact ⟨collect_p (counted_terrain μ i h) ht, fun v x w hu=> (he v x w hu).add (hT v x w hu), (by rw [flow_add he hT, rooting, VertRiver,hL])⟩

lemma on_trip (S:Plan G I true)(h:Hired S) : Trip (sailP (fun _=>planeF) Λ) (projectV 0 (nominal μ S)) (profit μ S) := by
   unfold Trip profit; rw [← sensingUfull μ (co_visible μ S h), add_sub_cancel ]; exact engaged μ S h

variable (h:MapGap x)
include h
lemma profit_loss {S: Finset W}(hs:2≤S.card)(n:ℕ) : profit μ (rising V K x S n)= multi (fun _=>planeF) x Λ Λ (bulkStation V μ) (mesur V K x μ S) (mesur V K x μ) n S:= by
   let Y:=rising V K x; let f:= fun i:ℕ=> bulkMix V (Y S i) (bulks V (n-i)); let g:=fun p=> MixSeg V K x Y S p n;
   let T:=Domain.paths n 0; let L:=picks S; have hf i : Hired (f i):= hire_b V _ _ (hired_all V K x h S i); have hg i (hi:i∈L): Hired (g i):= supply_mix V K x h S i n (fun p k _=> hired_all V K x h p k) hi;
   rw [show rising V K x S n=T.toList.flatMap f ++ L.toList.flatMap g from (by rw [planting,stepSchedule,if_pos hs]), profit_sum μ (hire_over f (fun i _=>hf i)) (hire_over g (fun i hi=>hg i (Finset.mem_toList.mp hi))),profitFlat μ f (fun i _=>hf i), profitFlat μ g (fun i hi=>hg i (Finset.mem_toList.mp hi)), Finset.sum_map_toList, Finset.sum_map_toList ];
   unfold multi; refine congr_arg₂ (·+·) ?_ (Finset.sum_congr rfl (fun i hi=>?_))
   · unfold lonely f Y; simp_rw [plane_chart V K x μ hs,bMixing μ V _ _ (hired_all V K x h S _)]; rfl
   unfold g MixSeg; let Q(z:Finset W)(n):=tray V K Y z n;
   rw [profitFlat μ _ ?tile, Finset.sum_map_toList]; refine Finset.sum_congr rfl (fun j hj=>?_); rotate_left
   · exact fun j _=> hire_pin (Q i j.1).2 (Q (S\i) j.2).2 V (atlas_hired V K x h i j.1) (atlas_hired V K x h _ _) (roadGap x h hi)
   exact Mixing (Q i j.1).2 (Q (S\i) j.2).2 μ V (roadGap x h hi) (atlas_hired V K x h _ _) (atlas_hired V K x h _ _)

theorem recurrence : Fields x (fun _=>planeF) Λ Λ (bulkStation V μ) (fun i=> pinStation V μ (K i)) (mesur V K x μ) := by
   refine ⟨ funext (fun n=>?_), fun i=> funext (fun n=>plane_single V K x μ i n), fun S hs n=>?_⟩
   · unfold mesur atlas tray; rw [if_neg (by simp), dif_neg (by simp)]; simp [nominal]
   rw [ ← profit_loss V K x μ h hs n, plane_chart V K x μ hs n ]; exact on_trip μ _ (hired_all V K x h S n)
end YM.MS.ScaleForest.Planted
