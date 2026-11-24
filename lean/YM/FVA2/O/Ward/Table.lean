import YM.FVA2.O.Ward.Inputs
import YM.FVA2.O.Ward.Power
import YM.MS.Breeze.North
/-!
# Course-unrestricted four dimensional space of momentum kernels at finite scale and polynomial growth
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Ward
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect
local notation "S"=> Job.single Unit
variable {G:Gauge} {μ:Measure QP} {s:ℝ}
abbrev Rolled (K:Edge G): Prop := Sheet S 1 (fun _=> K)
variable {L K:Edge G} {F H:Law G}
lemma unit_at {X:Arts.Rip G} (hp:rPrice X): Rolled (X 0):= by
    intro i j; simp only [ Job.cw,Pi.one_apply,one_zpow,one_mul ]; rw [spaceArc]; exact hp 0 i j
lemma rA : Rolled (A0 G s 0):= unit_at (A_caps G s).1
lemma rB : Rolled (B0 G s 0):= unit_at (B_caps G s).1
lemma rL : Rolled ((Q G 0).change (A0 G s 0)):= by rw [cue]; exact unit_at (C_caps G s).1
lemma lineOf (h:Rolled K)(i j:BH G): total S (fun _=> K i j) 1:= by obtain hx := h i j; simp only [ Job.cw,one_zpow,Pi.one_apply,one_mul] at hx; exact hx
lemma Rolled.pays (h:Rolled K)(hp:Job.Cohere μ)(he:F∈Wallet G): Pass K F μ := by
    change Lease false false S (fun _=>F) 1 at he; obtain ⟨d,hD,hW⟩:= Job.funds Unit hp; exact fun l=> herec hW h he.highp (fun _=>zero_le_one) (fun _=>zero_le_one) () l (fun i=>Bool.noConfusion i)
lemma Rolled.orb (h:Rolled K)(hp:Job.Cohere μ)(he:F∈ Wallet G): orbit K μ F ∈ Wallet G:= by
    rw [finite_cc μ (h.pays hp he)]; obtain ⟨d,hD,hW⟩:= Job.funds Unit hp; obtain hu:= planC (Lease.highp (show Lease false false S (fun _=>F) 1 from he)) h hW hD (fun _=>zero_le_one) (fun _=>zero_le_one); rw [one_mul] at hu; exact hu
lemma Rolled.on_tree (h:Rolled L)(hf:F∈ Wallet G)(hg:H∈ Wallet G): tree Landau.parity L F H ∈ Wallet G:= by
    change Lease false false S (fun _=>F) 1 at hf; change Lease false false S (fun _=>H) 1 at hg
    obtain hu:= trunks (fun i j=> polar (h i j)) hf.snow.highp hg.highp (fun _=>zero_le_one) (fun _=>zero_le_one) (fun _=>zero_le_one); rw [ show Latch.positive S 4 1 (1*1)=1 from funext fun (_:Unit)=>by simp [ Job.cw,Latch.positive]] at hu; exact hu
lemma Rolled.up (h:F∈ Wallet G): (Q G 0).raise F∈ Wallet G:= by
    apply permits.mpr; intro E _ _ w; let X:=Q G 0; unfold fieldVal; simp_rw [visit_Z,visit_sail]; refine visit_bound (fun i=>zero_le_one) (fun l i k h'=>?_); refine Costs.sum _ (fun c hc=>?_) (fun i p _=> zero_le_one)
    obtain he:= (count_caps G).solid 0 i.1 c; obtain hh:= permits.mp h E (l++(c,i.2)::k); unfold Arc.veg at he; rw [← spaceArc] at he; convert (Bound.linear i.2 he).mul hh using 1; ext x; simp only [fieldVal, Wire.sail_join, Wire.sail_cons]; ext x; simp
end YM.FVA2.O.Ward
