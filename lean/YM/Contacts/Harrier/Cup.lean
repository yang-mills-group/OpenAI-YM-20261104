import YM.Contacts.Prairie.Torch
import YM.Contacts.Procession.North
namespace YM.Contacts.Harrier
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k h i r l j M D:ℕ}{ζ σ:ℝ≥0}
-- linear ray prototypes without marker rank weighing inside geometric test.Deposits before all locations.
section basis
variable {P F:House X}[Fintype ι]
lemma shift_none (n:ℕ): shiftA n (0:House X)=0:=by ext1 p; unfold shiftA; split <;> rfl
lemma shift_add (P F:House X) : shiftA n (P+F)=shiftA n P+shiftA n F:= by ext1 p; simp only [shiftA,Pi.add_apply]; split<;> simp_all
lemma shift_scale (P:House X)(c:ℝ): shiftA n (c • P)= c • shiftA n P:= by ext1 p; simp only [shiftA,Pi.smul_apply]; split<;>simp_all
lemma proper_zero (X:Type)(r:ℕ):Proper r (0:House X):= ⟨fun _ _=> Poem.empty,fun _ _ _=>rfl⟩
lemma proper_add (h:Proper M F)(he:Proper M P):Proper M (F+P):= ⟨fun i j=>(h.sym i j).add (he.sym i j), fun i j hv=> by simp only [Pi.add_apply,h.thin i j hv,he.thin i j hv,add_zero]⟩
lemma proper_scale (h:Proper M F)(a:ℝ):Proper M (a • F):= ⟨fun i j=>(h.sym i j).scale a, fun i j hi=>by simp [h.thin i j hi]⟩
lemma proper_shift (h:Proper M F):Proper M (shiftA n F):= by
   constructor; intro i j; unfold shiftA; split; exact h.sym _ j; exact Poem.empty; intro i j hi; unfold shiftA; split; exact h.thin _ _ (by omega); rfl
lemma wind_none [Fintype X](n r:ℕ): House.wind (0:House X) n r=0:= by
   have h: (0:House X)=0+(0:House X):=(add_zero _).symm; let w:= House.wind (0:House X) n r; exact (show w=0 from add_left_cancel (a:=w) ((wind_add 0 0 n r).symm.trans ((congr_arg (fun (x:House X)=>House.wind x n r) h.symm).trans (add_zero _).symm)))
lemma wind_scale [Fintype X] (n i)(P:House X)(a:ℝ): House.wind (a • P) n i=a • House.wind P n i:= by
   funext x; simp only [House.wind,Pi.smul_apply, Finset.smul_sum]; apply sum_congr rfl; intro z hz; simp only [← glitter]; unfold dazzle; split; apply Convoy.design_scale; simp
lemma coil_nil (h:Proper M F)(hx:i<4) : coil F M i r=0:= by unfold coil dazzle shiftA Catch.cap; split; split; apply h.thin; omega; rfl; rfl
lemma seal_scale {F:House (Lines G m 1)} (h:sealedL F i)(a:ℝ): sealedL (a • F) i:= fun k hk=> wind_scale i k F a|>.symm ▸ shiningMark (h k hk) a
lemma birth_shift {F:House (Lines G m 1)}(n:ℕ)(h:Nation G m M F): Nation G m M (shiftA n F):= by
   refine ⟨proper_shift h.proper, fun k=>?_ ⟩; rw [shift_again]; let K:=shiftA (Catch.cap M) F; have hp:Snug K:= tagged h.proper (by unfold Catch.cap; omega) (by unfold Catch.cap; omega); rw [show shiftA (M+2+n) F=shiftA n K from (by unfold K Catch.cap; rw [shift_again]; congr 1; omega)]; by_cases ht:n≤ k
   · convert sealedL_shift hp n (h.birth (k-n)) using 1; omega
   intro i hi; by_cases hx:n ≤ i; swap; · rw [wind_gloom hp (by omega)]; exact calm_zero
   have he: i-n<4:=(by omega); rw [show k+3=k+3-n+n from (by omega), show i=i-n+n from (by omega)]; rw [wind_turn]; suffices hh: House.wind K (k+3-n) (i-n)=0 by rw [hh]; exact calm_zero; -- maybe rewrites in k if independent nat terms
   funext x; unfold House.wind; simp_rw [← glitter]; apply sum_eq_zero; intro r hr; rw [show dazzle _ _ _=_ from coil_nil (r:=r) h.proper he]; apply parcel_nil
lemma nation_zero (A:Gauge)(m:Side)(j):Nation A m j 0:= by refine ⟨proper_zero _ _,fun k=>?_⟩; intro i hi; rw [shift_none,wind_none]; exact calm_zero
lemma nation_add {F U:House (Lines G m 1)}(hp:Nation G m M F)(he:Nation G m M U): Nation G m M (F+U):=⟨proper_add hp.proper he.proper,fun i=> shift_add F U|>.symm ▸ seal_add (hp.birth i) (he.birth i)⟩
lemma nation_scale {F:House (Lines G m 1)}(hp:Nation G m M F)(a:ℝ): Nation G m M (a • F):=⟨proper_scale hp.proper a,fun i=> shift_scale F a|>.symm ▸ seal_scale (hp.birth i) a⟩
end basis
variable {v:Dye G}{P Q:bore G}
abbrev Based (ζ:ℝ≥0)(x:Dye G)(M:ℕ)(F:bore G):Prop:= Mount F M ∧ ∃ Z:TableFee,Price F x ζ Z
lemma universal (h:Based ζ v M P): Mount P M:= h.1
namespace Based
lemma zero : Based ζ v M 0:= by
   have h:∀ (n:Side), plead (0:bore G) (lower n)= (0:House (Lines G n 1)):=by intro n; funext i j; unfold plead packing cram; ext x; simp
   exact ⟨⟨proper_zero _ _,fun m=>by rw [h]; apply nation_zero⟩,0,⟨fun i j=> Rest.zero⟩⟩
lemma add (h:Based ζ v M P) (he:Based ζ v M Q) : Based ζ v M (P+Q) := by
   obtain ⟨⟨ha,hA⟩,Y,hY⟩:=h; obtain ⟨⟨hb,hB⟩,V,hV⟩:=he; refine ⟨⟨proper_add ha hb,fun m=>?_⟩,Y+V,⟨fun i j=> (hY.lands ..).add (hV.lands i j)⟩⟩; let L:=lower m (α:=Dye G); have hh: plead (P+Q) L=plead P L+plead Q L:=by funext i j; simpa only [plead,Pi.add_apply,one_smul] using Theater.float_pack (P i j) (Q i j) 1 L (hY.lands ..).summ (hV.lands ..).summ
   rw [hh]; exact nation_add (hA m) (hB m)
lemma smul (h:Based ζ v M P)(a:ℝ): Based ζ v M (a • P):= by
   obtain ⟨⟨ha,hA⟩,V,H⟩:=h; refine ⟨⟨proper_scale ha a,fun m=>?_ ⟩, ‖a‖ • V,⟨fun i j=>(H.lands ..).smul a⟩⟩; rw [show plead (a • P) (lower m)=a • plead P _ from funext fun i=>funext fun j=> smul_pack ..]; exact nation_scale (hA _) a -- `rewrite _` ambiguity
lemma shift (h:Based ζ v M P) (k:ℕ):Based ζ v M (shiftA k P):= by obtain ⟨⟨hp,hP⟩,Y,H⟩:=h; exact ⟨⟨proper_shift hp,fun m=> by rw [pledgeShift]; exact birth_shift k (hP m)⟩,_, Catch.xin k 0 H⟩
lemma capacity (h:∀ k:ℕ,∃ X:bore G,Based ζ v M X ∧ ∀ i≤k,P i=X i) : Based ζ v M P:= by
   choose Qq hQ H using h; choose p hp using fun i=>(hQ i).2; have he:Proper M P:= ⟨fun i j=>(by rw [H i i le_rfl]; apply (universal (hQ i)).incarnate.sym),fun i j hi=>by rw [H i i le_rfl]; exact (universal (hQ _)).incarnate.thin i j hi⟩; refine ⟨⟨he,fun m=> ⟨properB M P _ he,fun k=>?_⟩⟩,(fun i j=>p i i j),⟨fun i j=> by rw [H i i le_rfl]; exact ((hp i).lands i j)⟩⟩
   let F:=Qq (k+3); apply seal_prefix (((universal (hQ (k+3))).attends m).birth k); intro i hi; unfold shiftA; split; · ext1 j; exact congr_arg (fun X=> packing (lower m (α:=Dye G)) (X j)) (H (k+3) (i-(M+2)) (by omega)).symm
   rfl
end Based
end
end YM.Contacts.Harrier
