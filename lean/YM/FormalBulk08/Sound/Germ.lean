import YM.FormalBulk08.North.Nest
import YM.FormalBulk08.Avenue.Plaza
import YM.UVExtension.Free.Rows
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Sound
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster Dove Dove.Lab PowerSeries UVExtension UVExtension.Free Matrix Exterior Tree
open scoped Topology ENNReal BigOperators Classical Matrix
variable {G:Gauge}{I J:Type}{A:Levels G}
open North
lemma capital {σ C:ℝ}{U:ℕ→ℝ}{R:ℕ→Row I J}{V:Row I J}{m:ℕ}(hs:0<σ)(h:Pace σ C U R V m)(n: Side): Ends (fun i=>(R i).acts n) (V.acts n) := by
   have he: Tendsto R atTop (𝓝 V):= tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=>tendsto_pi_nhds.mpr fun v=> h.moves i j v
   have hv := (eventually_gt_atTop m).mono (show ∀ i,m < i→ (R i).strip σ C from fun i=>h.stays i)
   exact tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=>acts_entry he hv n i j hs
variable {K:KernelChoices}{d j t:ℕ}{W:Lab G K I}{ρ:ChartRatio G}
-- precision before choosing any fields. No coefficients above admission used here.
def rose (A: Levels G)(k:ℝ)(i:ℕ):= terminalR fun N=> pink k (location A N i)
lemma rose_live (A:Levels G)(k:ℝ)(hk:0<k)(i:ℕ): ∃ C σ:ℝ,0<C∧ 0<σ∧ Pace σ C (fun N=>C*ratioR A.S N i targetPower) (fun N=>pink k (location A N i)) (rose A k i) i := by
   obtain ⟨s,C,hs,hC,H,T⟩:= colors G k hk (A.clock.adm i); refine ⟨C,s,hC,hs, pacer _ _ hs.le ?_ i (fun _ _=> (H _).1) (fun N M n m=> (T A _ _ _ n.le m rfl).1)⟩
   simpa using (repeat_foot A.S i targetPower targetPower_pos).const_mul C

def sun (A:Levels G)(k:ℝ)(i:ℕ)(n:Side):= patron G (Precision.K ((rose A k i).acts n))
lemma matrixPaid {I J K:Type*}[Fintype J]{f:ℕ→Matrix I J ℝ}{p:ℕ→Matrix J K ℝ}{U:Matrix I J ℝ}{V:Matrix J K ℝ} (h:Ends f U)(he:Ends p V): Ends (fun i=>f i*p i) (U*V):= by
    apply tendsto_pi_nhds.mpr; intro x; apply tendsto_pi_nhds.mpr; intro y; simp_rw [mul_apply]; exact tendsto_finsetSum _ fun i _=>(tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h x) i).mul (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp he i) y)
lemma plusKin {n:Side}{p:ℕ→Row (TypeFace 2) (TypeFace 2)}{q:Row (TypeFace 2) (TypeFace 2)}
    (h:Ends (fun i=>(p i).acts n) (q.acts n)): Ends (fun i=> patron G (Precision.K ((p i).acts n))) (patron G (Precision.K (q.acts n))):= by
   let Q i:= Precision.K ((p i).acts n); have he: Ends Q (Precision.K (q.acts n)):= by
       unfold Q Precision.K; exact (matrixPaid (matrixPaid tendsto_const_nhds h) tendsto_const_nhds)
   apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro j; simp_rw [Avenue.blue_cost]; by_cases hv:i.2.2=j.2.2
   · simp_rw [if_pos hv]; exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp he _) _
   simp_rw [if_neg hv]; exact tendsto_const_nhds
lemma cosmic (A:Levels G)(k:ℝ)(hk:0<k)(i:ℕ)(n:Side): Ends (fun N=> kernelP G k (location A N i) n) (sun A k i n):= by
   obtain ⟨C,s,hC,hs,T⟩:= rose_live A k hk i; exact plusKin (p:=fun N=>pink k (location A N i)) (q:=rose A k i) (capital hs T n)
-- explicit accounting of inherited g0 not outsourcing this to positive repeated components
variable (a:hue G)(i:Leaf W.scrolls)(hp:Use W ρ d)(h:LocalRatio ρ)(hs:G.Simple)
include hp h hs
lemma virgin_ink : heir a ρ W i.a i.b 0 2=setkin G (rose (W.V i.a) K.penalty i.b):= by
    let V:= W.V i.a;let U:=rose V K.penalty i.b; let Z N:= pink K.penalty (location V N i.b)
    obtain ⟨C,s,hC,hv,T⟩:=rose_live V _ K.penalty_pos i.b; have hh:= North.crown a hp h hs (Nat.zero_le _) 2 i
    funext w; refine tendsto_nhds_unique (hh.shares w) (?_); have he: Ends (fun n=> setkin G (Z n) w) (setkin G U w):= by
       obtain ⟨B,hB,E⟩:= setkin_pay G hv.le; apply Metric.tendsto_nhds.mpr; intro ε hp; let f n:=B*(C*ratioR V.S n i.b targetPower); have ht: Tendsto f atTop (𝓝 0):= by simpa only [f,mul_zero] using! (((fare_fin i).const_mul C).const_mul B)
       filter_upwards [eventually_gt_atTop i.b,ht.eventually (gt_mem_nhds hp)] with n h he; rw [Real.dist_eq];refine lt_of_le_of_lt (?le : _ ≤ f n) he
       have hX := E _ _ (mul_nonneg hC.le (ratioR_pos ..).le) (T.price n h);exact Bail.value (Dove.seat_minus G hv.le hC.le (T.stays n h) T.value ▸ hX) hv.le w 0
    exact he.congr' ((eventually_ge_atTop i.b).mono (fun N H=> congr_fun ((genu (W.V i.a) (W.wood i.a) (W.toEmpire.bill i.a) ρ a h hs H).ink.symm) w))
end YM.FormalBulk08.Sound
