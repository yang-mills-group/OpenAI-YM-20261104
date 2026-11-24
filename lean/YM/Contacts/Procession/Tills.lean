import YM.Contacts.Procession.Stamp
/-! # One bill before all these petroleum lamps. Torus arithmetic still arbitrary.
Momenta on full cover. -/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Procession.Xenon
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff
variable {α β ι:Type}{G:Gauge}{σ:ℝ≥0}{b c d:ℝ}{u B i k j r e:ℕ} {m:ℕ→ Side}
-- tomography perfectly fixed period choices
lemma portraying {f:Field (Fin i) (Node α)} (x:Fin i→Node α)(hf:Summable f)(hm:Tendsto (fun j=>(m j).val) atTop atTop):
    Tendsto (fun i=> packing (lower (m i)) f (lower (m i) ∘ x)) atTop (𝓝 (f x)):= by
   let φ (n:ℕ)(q:Fin i→Node α):= if lower (m n) ∘ q=lower (m n) ∘ x then f q else 0; have he n: packing (lower (m n)) f (lower (m n) ∘ x)=∑' q,φ n q:=by unfold packing; rw [expand_eq]; rfl
   let g (q:Fin i→Node α):= if q=x then f x else 0; have hl (w): Tendsto (fun j=>φ j w) atTop (𝓝 (g w)):= by
     apply Filter.EventuallyEq.tendsto; filter_upwards [eventually_all.mpr (fun k:Fin i=> lower_separates hm (w k) (x k))] with i hi; unfold φ g; by_cases h:w=x; · rw [h]; simp
     rw [if_neg ?_,if_neg h]; intro he; exact h (funext fun j=> hi j (congr_fun he j))
   have hx:=tendsto_tsum_of_dominated_convergence hf.norm hl (Eventually.of_forall fun i w=> show ‖φ i w‖ ≤ ‖f w‖ from by unfold φ; split_ifs <;> simp); simp_rw [he]; simpa only [g,tsum_ite_eq] using hx
lemma alive_approach {F:Field (Fin i) (Node α)}{g:∀ i',Field (Fin i) (Co (m i') α)} {c:ℕ→ℝ} {x:α} (h:∀ i,Alive σ b (c i) x F (m i) (g i))(ht:Tendsto c atTop (𝓝 0))(y:Fin i→Node α)(hm:Tendsto (fun i=>(m i).val) atTop atTop): Tendsto (fun i=>g i (lower (m i)∘y)) atTop (𝓝 (F y)):= by
   let v(i:ℕ):=lower (m i)∘y; have he:= squeeze_zero_norm (f:=fun i=>g i (v i)-packing (lower (m i)) F (v i)) (fun n=> budget_single ((h n).far.raw) (v n)) ht; have hh:=he.add (portraying y (h 0).room.summ hm); rw [zero_add] at hh; apply hh.congr; intro i; exact sub_add_cancel .. -- sum defeq?
variable [Fintype α][Fintype β]
variable (R: Row α α)(H: Row α β)(A: House (Node α))(V:∀ m:Side, House (Co m α))(x:α)(y:β) {g:TableFee}
abbrev ray (B e:ℕ)(F: Field (Fin i) (Node α)):=porch A (plane R) (Matrix.of (plane H)) F B e
abbrev peer (e:ℕ)(F: Field (Fin i) (Node α))(m:Side):= rose (V m) (R.acts m) (H.acts m) (packing (lower m) F) e
lemma mooring {X Y:Type}[Fintype X][Fintype Y](R:Matrix X Y ℝ)(f g:Field (Fin i) X)(a:ℝ): hoist R (a • f+g) = a • hoist R f + hoist R g:= by ext1 v; simp [hoist,allAt,printRun,reorder, Pi.smul_apply, smul_eq_mul, add_mul,tsum_fintype, sum_add_distrib,mul_add, mul_assoc,mul_left_comm _ a,mul_sum]
lemma weightless (e:ℕ)(m:Side)(f p:Field (Fin i) (Node α))(h:Summable f)(hp: Summable p)(a:ℝ): peer R H V e (a • f+p) m=a • peer R H V e f m+peer R H V e p m:= by
   have ht : packing (lower m) (a • f+p)= a • packing (lower m) f+ packing (lower m) p:= funext ( (Scroll.scale (p:= hinge (ι:=Fin i) (lower m)) (f:=f) (fun _=> rfl) a).add (fun _=>rfl) (h.const_smul a) hp|>fun t i =>(t i).symm) -- syntax test
   unfold peer rose leafS; rw [ht, Pi.single_add,Pi.single_add,Pi.single_smul,Pi.single_smul, canal_linear]; funext i; exact mooring ..
structure Dome (g:TableFee)(σ:ℝ≥0)(c d:ℝ) : Prop where
   paidA m i j: Two (voyageW m σ α) (A i j) (V m i j) (g i j) 0
   warmed m : Snug (V m)
   flag : 0<σ
   Rfee : R.strip σ c
   beam : 0≤c
   hFee : H.strip σ d
   cbase : 1≤ d
variable {R H A V x y}{t:ℝ}{F P:Field (Fin i) (Node α)}
namespace Dome
variable (h:Dome R H A V g σ c d) (ψ : Rest (terrain σ α) (0,x) F b)(hp:Poem F)(he:e < B)(hi:i≤ B)
include h ψ hp he hi
theorem river (y:β)(hm:Tendsto (fun i=>(m i).val) atTop atTop) (v : Fin j → Node β) : Tendsto (fun i=> peer R H V e F (m i) j (lower (m i) ∘ v)) atTop (𝓝 (ray R H A B e F j v)) := by
   refine alive_approach (x:=y) (fun i=> reading_block (h.paidA _) ψ h.Rfee h.beam h.hFee h.cbase y (h.warmed _) he hp hi) (?_) v hm; let p i:=hush σ (m i); have ht : Tendsto p atTop (𝓝 0) := tendsto_inv_atTop_zero.comp (Real.tendsto_exp_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)|>.comp hm).const_mul_atTop (NNReal.coe_pos.mpr h.flag))); simpa only [zero_mul,mul_zero] using ((ht.mul_const _).const_mul ((j+1:ℕ):ℝ))
-- physical linearity full horizonp; fix all periods before shifting; no unbiased action reexpression across.
private def eery (i:ℕ):Side:= ⟨i+1,by positivity⟩
omit h ψ hp he hi in
private lemma eiga : Tendsto (fun j=>(eery j).val) atTop atTop := tendsto_atTop_mono (f:=id) Nat.le_succ tendsto_id
theorem ray_tilt (y:β)(hw:Rest (terrain σ α) (0,x) P t)(hq:Poem P) (a:ℝ): ray R H A B e (a • F+P)=a • ray R H A B e F+ ray R H A B e P:= by
   funext v w; apply tendsto_nhds_unique (h.river ((ψ.smul _).add hw) ((hp.scale a).add hq) he hi y eiga w); refine Tendsto.congr' ?_ ( ((h.river ψ hp he hi y eiga w).const_mul a).add (h.river hw hq he hi y eiga w)); apply Eventually.of_forall; intro i; dsimp only; rw [weightless R H V e _ F P ψ.summ hw.summ a]; rfl -- congr'
-- pole price linear when application normalized. Lipschitz 
end Dome
end YM.Contacts.Procession.Xenon
