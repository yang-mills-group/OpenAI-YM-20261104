import YM.Contacts.Procession.Glide
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Procession.Welcome
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon Kale Garf PertExtension.Series Radial Larch
open scoped Classical Topology BigOperators NNReal Matrix ContDiff
variable {α β γ ι:Type}{G:Gauge}{σ η:ℝ≥0}{b c:ℝ}{L q f:Side}{u B i k j r n d p t:ℕ}[Fintype ι]
lemma pack_io {f:Field ι α}(J:α→β)(x:ι→α)(hf:Injective J): packing J f (J∘x)=f x:= by
   unfold packing; rw [expand_eq,tsum_eq_single x]; · exact if_pos rfl
   intro b h; exact if_neg (fun he=> h (funext fun i=>hf (congr_fun he i)))
lemma pack_fell (f:Field ι α)(J:α→β)(x:ι→β)(hs:x∉ Set.range (hinge (ι:=ι) J)): packing J f x=0 := by unfold packing; rw [expand_eq]; refine (tsum_congr ?_).trans tsum_zero; intro y; exact if_neg (fun h'=>hs ⟨_,h'⟩)
lemma pack_cost {f:Field ι α}{l:Pulse.Range α}{k:Pulse.Range β}(J:α→β){a:α}{x:β}(hq:Injective J)(h:Rest l a f b) (ht:0 ≤ c)(he:∀ u:ι→α, fee k x (hinge J u) ≤ c* fee l a u) : Rest k x (packing J f) (c*b):= by
   let f' := packing J f; let w(t:ι→β):= ‖f' t‖*fee k x t; let j := hinge (ι:=ι) J; have hj:Injective j:= fun a b h=>funext fun i=>hq (congr_fun h i); have hf: SumBudget (w ∘ j) (c*b):= budget_mono (budget_scale ht h) (fun i=> mul_nonneg (norm_nonneg _) (fee_plus _)) (fun i=>?_ )
   · refine ⟨fun i=>mul_nonneg (norm_nonneg _) (fee_plus _),?_⟩; have hw: HasSum w (tsum (w∘ j)):= (hj.hasSum_iff (fun i hi=>by unfold w f'; rw [pack_fell f J i hi,norm_zero,zero_mul])).1 hf.2.1.hasSum; exact ⟨hw.summable,hw.tsum_eq.le.trans hf.2.2⟩
   change w (J∘i) ≤ c * _; unfold w f'; rw [pack_io J i hq,mul_left_comm c]; exact mul_le_mul_of_nonneg_left (he i) (norm_nonneg _)
-- geometric characters. Each Deck relative to root 0.
def lane (α:Type) (L:Side) (x:Node α) : Node (α ⊕ Co L α) := (rent L x.1,.inr (wrap L x.1,x.2))
lemma lane_inj (α:Type)(L:Side): Injective (lane α L) := by rintro ⟨p,a⟩ ⟨q,b⟩ h; replace h : (rent L p = rent L q) ∧ ((wrap L p,a)=(wrap L q,b)):= ⟨congr_arg Prod.fst h,Sum.inr.inj (congr_arg Prod.snd h)⟩; refine Prod.ext (?_:p=q) (show a=b from congr_arg Prod.snd h.2); rw [rent_balance L p, h.1,show wrap L p=wrap L q from congr_arg Prod.fst h.2]; exact (rent_balance ..).symm -- edit
variable {S:StepData q f}
lemma online (x:Node (Dye G)): offspring S (lower f x)= lower q (lane (Dye G) S.patch.L x):= by
   rcases x with ⟨a,r⟩; unfold offspring lower lane; rw [split_co]; change (S.ratio.parent (wrap f a),(Sum.inr (S.ratio.residue (wrap f a),r): Mixed G S.patch))=(wrap q _, Sum.inr _); rw [cell_stamp,S.ratio.residue_wrap]; rfl -- Sum.inr domain
private lemma lane_start (L:Side)(x:α): (lane α L (0,x)).1=0:= by
    change rent L 0=0; symm; apply rent_unique; simp [Lattice.lift]
lemma lane_strip (u:ι→Node α)(x:α)(y:α ⊕ Co L α)(h : (σ:ℝ)/(L.val:ℝ)≤η): fee (terrain σ _) (0,y) (hinge (lane α L) u)≤ Real.exp (4*σ:ℝ)* fee (terrain η _) (0,x) u:= by
   let l:=terrain η α; let k:= terrain σ (α ⊕ Co L α); let W(i:Option ι):= i.elim (0,x) u; let Y (i:Option ι):= i.elim (0,y) (lane α L ∘ u); have he i: (Y i).1=rent L (W i).1:= by cases i; exact (lane_start L x).symm; rfl
   apply k.wide Y (one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity)) (l.one_bill W)) ; intro i j
   change Real.exp (σ*(size _ :ℝ)) ≤ _*_; rw [he i,he j]; refine le_trans (?_:_≤ Real.exp (4*σ:ℝ)*l.step (W i) (W j)) (mul_le_mul_of_nonneg_left (l.width W i j) (Real.exp_pos _).le)
   have hr:=mul_le_mul_of_nonneg_left (stride L (W j).1 (W i).1) (NNReal.coe_nonneg σ); rw [terrain_step,← Real.exp_add]; apply Real.exp_monotone; have hp:= mul_le_mul_of_nonneg_right h (show (0:ℝ) ≤ size ((W j).1-(W i).1) by positivity); field_simp at *; apply (mul_le_mul_iff_of_pos_right (side_pos L)).1; nlinarith only [hp,hr]
lemma design_at {X:Type}[Fintype X](F:Field ι X)(x:X→ℝ): House.design F x=say F (fun _=>x):= by rw [House.design_spec,say,tsum_fintype]
lemma pack_twice {J: α→ β}{K:β→γ}(F:Field ι α)(h:Summable F): packing K (packing J F) = packing (K ∘ J) F:= by -- missing γ
   exact funext (Scroll.comp (p:=hinge (ι:=ι) J) (f:=F) (fun i=>rfl) (q:=hinge (ι:=ι) K) (fun i=> rfl) h)
-- bill projection exactly all positions
lemma advance (F:Field (Fin i) (Node (Dye G)))(hF:Poem F)(h:Summable F): packing (lower q) (packing (lane _ S.patch.L) F)= hoist (shave S G) (packing (lower f) F):= by
   refine design_eq (poetic _ (poetic _ hF _) _) hoist_shape (funext fun x=>?_); rw [hoist_read,pack_twice _ h,shaved,design_at,design_at,say_fold h,say_fold h]; apply congr_arg _; ext i j; change x _=x _; exact congr_arg x (online (S:=S) j).symm
end YM.Contacts.Procession.Welcome
