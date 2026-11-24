import YM.Contacts.Procession.Hollow
/-!
# Finite step all-order Mark. Genuine block Hess, uses unmarked PPE connection.

Formula and representation at any admissible given period.Finite.End
 -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Procession.Welcome
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon Kale Garf Spark PertExtension.Series Radial
open scoped Classical Topology BigOperators NNReal Matrix ContDiff
variable {α β ι:Type}{G:Gauge}{σ:ℝ≥0}{b:ℝ}{c f:Side}{u B i k r n p t:ℕ}{g:TableFee}
lemma paint_proper (M:Matrix α β ℝ){F:House α}(hf:Proper p F): Proper p (planeC M F):= ⟨fun i j=> hoist_shape, fun i j he=> by unfold planeC; rw [hf.thin _ _ he, hoist_erase]⟩
lemma cameo_proper {F:House α}(hf:Proper p F): Proper p (-F):=⟨fun i j=>(hf.sym i j).minus, fun i j he=>by simp [hf.thin i j he]⟩
section
variable [Fintype α][Fintype β]
lemma hoist_neg (M:Matrix α β ℝ)(F:Pulse.Field (Fin k) α): hoist M (-F)=-hoist M F:= by simpa only [add_zero, neg_one_smul,hoist_erase] using (mooring M F 0 (-1))
lemma hoist_add (M: Matrix α β ℝ)(F P:Pulse.Field (Fin k) α): hoist M (F+P)=hoist M F+hoist M P:= by simpa only [one_smul] using mooring M F P 1
lemma shuffle (A:House α)(g:α→α→ℝ): canal g t A 0=0:= by
   have he:= canal_linear (p:=t) g (A:=A) 0 0 1; simp only [one_smul,add_zero] at he; exact (add_left_cancel (show _=canal g t A 0+canal g t A 0 from (by rwa [add_zero] : canal g t A 0+0= canal g t A 0+canal g t A 0))).symm
lemma vault_neg (F A:House α) (g:α→α→ℝ)(v:ℕ): canal g v A (-F)= -canal g v A F:=by simpa only [neg_one_smul,shuffle,add_zero] using canal_linear (A:=A) (p:=v) g F 0 (-1)
end
variable {S:StepData c f}
local notation "χ"=> Lines G f 1
local notation "Υ"=> Lines G c 1
variable {A Y : House (Lines G f 1)}{H P: FreeResolvent.FaceRow}{R: Astro G S} {Q:ChartRatio G}
-- hold-W fixed horizon response at one period
abbrev entrance (S:StepData c f) (F:House χ) := planeC (shave S G) F -- beware shadow S vs S✝ glyph with f
abbrev streamG (Q:ChartRatio G) (S:StepData c f)(A:House χ)(F:House χ) (W:FreeResolvent.FaceRow) (L: Matrix χ Υ ℝ)(h:ℕ):= planeC (Forge.sky S G L) (canal (veer S G W) h (banners G S Q A) (entrance S F))
-- relation of adding a single shift Account; B≥p, ok. sign + in action (− in log).
section
private lemma painted (n:ℕ)(ht:0<t) : banners G S Q (A+shiftA t Y) n=banners G S Q A n+ shiftA t (-entrance S Y) n := by
   ext1 r; simp only [banners,Pi.add_apply]; by_cases hn:n=0
   · subst n; unfold compote shiftA; rw [if_pos rfl,if_pos rfl,if_neg (by omega)]; simp
   unfold shiftA compote; rw [if_neg hn,if_neg hn]; split_ifs with h h' h''<;> (simp only [Pi.zero_apply, Pi.neg_apply, hoist_add, hoist_erase, entrance,planeC] <;> abel) -- split redund
lemma continuity {H:House α}(p:ℕ) : True:= trivial -- omit
lemma meets (h:Chest A P)(hf:Proper p Y)(ht:p≤t)(hq:0 < t) (n:ℕ)(he:n<t+t): Forge.vault S Q (A+shiftA t Y) R P H n=Forge.vault S Q A R P H n + shiftA t (streamG Q S A Y P (atr G S R) p) n:= by
   let V:= -entrance S Y; let U:= banners G S Q A; have ht' := bracket (veer S G P) (banner_snug (Q:=Q) h.toShaped) (banners G S Q (A+shiftA t Y)) (show Proper p V from cameo_proper (paint_proper _ hf)) (by omega: n<2*t) (by omega) (fun j _=> painted j hq)
   let K:= Forge.sky S G (atr G S R); unfold Forge.vault mintage; ext1 r; rw [ht']; unfold shiftA at *; by_cases hn:n=0; · subst n; simp [show ¬t≤0 by omega]
   simp only [if_neg hn,Pi.add_apply]; split_ifs <;> (simp only [Pi.zero_apply, Pi.neg_apply, neg_add, hoist_add, hoist_erase,add_zero] <;> try rfl)
   unfold V; rw [vault_neg]; simp [hoist_neg,streamG,planeC] -- V unfolded at ht?
lemma preserved (h:Chest A P)(hf:Proper p Y)(ht:p≤t)(hq:0<t): Chest (A+shiftA t Y) P:= by
   let F:= shiftA t Y; have H:Snug F:= tagged hf (by omega) hq; refine ⟨⟨fun i j=>(h.poem i j).add (H.poems _ _), fun i j he=>?_⟩,fun x=>?_⟩; · change A i j+F i j=_; rw [h.thin i j he,H.thin i j (by omega),zero_add]
   simp_rw [Pi.add_apply,show shiftA t Y 0 2=0 from H.thin 0 2 (.inl rfl),add_zero]; exact h.glow _ -- rw F
lemma renames (h:Chest A P)(hf:Nation G f p Y)(hr:∀ k:ℕ, sealedL A (k+3))(hH:Beam S G R P H b)(hQ:LocalRatio Q): Nation G c p (streamG Q S A Y P (atr G S R) p) := by
   let Γ:=streamG Q S A Y P (atr G S R) p; have hp:= paint_proper (shave S G) hf.proper; have hx:= marsh (veer S G P) (banner_snug (Q:=Q) h.toShaped) hp; refine ⟨paint_proper (Forge.sky S G (atr G S R)) hx,fun k=>?_⟩
   let t:=k+p+4; let v:= p+2+t; let n:=k+3+t; have hK :∀ X:House χ,Chest X P→sealedL X n→sealedL (Forge.vault S Q X R P H) n:= by intro X hX hx; unfold n; rw [show k+3+t=k+t+3 by omega]; apply passportL hQ (show sealedL _ _ from (?_:_)) hX hH; exact (show n=k+t+3 by unfold n; omega) ▸ hx
   have ha:sealedL A n:= by rw [show n=k+t+3 by unfold n; omega]; exact hr _
   let X:= A+shiftA v Y; have hP':p ≤ v:=by unfold v; omega
   have hv:0<v:= lt_of_lt_of_le (show 0<p+2 by omega) (Nat.le_add_right ..); have hZ: sealedL (Forge.vault S Q A R P H + shiftA v Γ) n:= seal_prefix (hK X (preserved h hf.proper hP' hv) (seal_add ha (Frost hf (by omega:k+3≥3) t))) (fun i hi=> meets h hf.proper hP' hv i (by unfold v t; unfold n t at hi; omega))
   have hw:= seal_cancel (hK _ h ha) hZ; refine sealedL_prev t (?_); rw [shift_again,add_comm t]; exact hw
end
end YM.Contacts.Procession.Welcome
