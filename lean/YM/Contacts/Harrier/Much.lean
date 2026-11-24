import YM.Contacts.Harrier.Gift
namespace YM.Contacts.Harrier
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k i r l j M D:ℕ}{ζ σ:ℝ≥0}
namespace Transfer
open Parcel Prairie Planned.PrimaryIntegral295
variable {e:Parcel G} {p:Word}{s:Parcel.Step}{S:Boom} (T:e.License S ζ)(hp:OK S p)(hs:s∈S)
section
variable {v:Site s.L}{F:Sketch G}{x:Dye G}
lemma zero_bring (Z:Theater G) (M:ℕ)(o:Cover){Q}{δ:ℝ≥0}(H:Z.Rich σ ζ b c Q)(A:(ζ:ℝ)/Z.L.val≤δ)(x:Dye G): bring Z M o 0=0:= by apply add_left_cancel (a:=bring Z M o 0); simpa only [add_zero,one_smul] using (combine Z M o H A (Based.zero (v:=x)) (Based.zero (v:=x)) 1).symm
private lemma honors (P:Sketch G)(H:IsLinearMap ℝ P)(g:TableFee)(hx:∀ a:Cards,Costs D a 1→Price (P a) x ζ g)(hp:∀ a:Cards,Costs D a 0→P a=0) : ∀ i j,∃ b≥(0:ℝ), Weight (sail P i j) D (terrain ζ _) x b:= by
   have hl : Costs D 0 1:= fun i hi x hx=>by simp
   intro i j; refine ⟨_,((hx _ hl).lands i j).cash,fun p b hb H₁=>?_⟩; rcases hb.eq_or_lt with hb|hb; · subst b; change Rest _ _ (P p i j) _; rw [hp p H₁,mul_zero]; exact Rest.zero
   let Y:=b⁻¹ • p; have hh: Costs D Y 1 := by
       intro t ht v hv; change ‖iteratedFDeriv ℝ t (b⁻¹ • p.val) v‖ ≤ _; rw [iteratedFDeriv_const_smul_apply ((Cards.able p t).contDiffAt),norm_smul,Real.norm_of_nonneg (by positivity)]; exact (mul_le_mul_of_nonneg_left (H₁ _ ht _ hv) (by positivity)).trans_eq (inv_mul_cancel₀ hb.ne')
   have he : P p i j=b • P Y i j:= by simp_rw [Y,H.map_smul,Pi.smul_apply,smul_inv_smul₀ hb.ne']
   change Rest _ _ (P p i j) _; rw [he]; exact ((hx Y hh).lands i j|>.smul b).ist (by rw [Real.norm_of_nonneg hb.le,mul_comm]) -- maybe semicolon scopes
variable (h:Living x M D F ζ)
include T hp hs h
theorem collected : Living x M D (weigh e p s M v F) (2*ζ):= by
   obtain ⟨b,c,V,H⟩:= permits e p s T hp hs; let Z:=crafts e p s T hp; choose d hd hG using h.budget; let P:= (fun y:Cards=> F (desk s v y)); let L:= curb s v; let W:=weigh e p s M v F; have hf p (hp:Costs D p 1): Price (P p) x ζ d:= ⟨fun i j=>(mul_one (d i j)) ▸ (hG i j (desk s v p) _ zero_le_one (desk_cost s v p hp zero_le_one))⟩
   refine ⟨weighed T hp hs h, fun _=>measure T hp hs h _, honors W (weighed T hp hs h) (Z.transit M (2*ζ) b c (fun i j=> parcelY ζ L*d i j) V) ?_ ?_⟩; · intro p hp; let U:= P p; have hh:= hf p hp; exact (Theater.ecstasy H (migrant L (h.lineage _).1 hh) (revised L hh) (step_reserved ..) x).up
   intro p hN; have hu:P p=0:= by funext i j w; have hp:= hG i j _ _ le_rfl (desk_cost s v p hN le_rfl); rw [mul_zero] at hp; exact norm_le_zero_iff.mp (budget_single hp.raw w)
   change bring Z M L (P p)=0; rw [hu]; exact zero_bring Z M L H (step_reserved s ζ) x
lemma received : Living x M D (pass e p s M v F) (2*ζ):= by
   let P:=weigh e p s M v F; let w:=sink e.x (e.kickoff p s); let H(T:House (Node (Dye G))):= recoil w M T; choose d hd hD using (collected T hp hs (v:=v) h).budget; refine ⟨passing T hp hs h,fun _=> know T hp hs h _, honors (pass e p s M v F) (passing T hp hs h) (stool w M d) ?_ ?_⟩; intro v h'; exact moving w M (show Price (P v) x (2*ζ) d from ⟨fun i j=> (mul_one (d i j)) ▸ (hD i j v 1 zero_le_one h')⟩)
   intro v hv; change H (P v)=0; rw [show P v=0 from funext (fun i=> funext fun j=> funext fun w=> by have hz:= hD i j v 0 le_rfl hv; rw [mul_zero] at hz; exact norm_le_zero_iff.mp (budget_single hz.raw w))]; exact empty_recoil w
lemma cenacle (n:ℕ): Living x M D (Transfer.mean e p s M n F) (2*ζ):= (Living.sum univ fun i _=> (received T hp hs (v:=i) h)).scale _
end
end Transfer
end
end YM.Contacts.Harrier
