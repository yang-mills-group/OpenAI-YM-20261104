import YM.XSpace.Hair

/-!
# Physical motif reads on gauge-invariant stencils and the triangular inverse
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Bracket
open Function Set Filter Lows Scale Mu Uptown Normalize Maxwell Maxwell.Free MvPolynomial Next.Rank.Normal Contraction Finsupp
open scoped Topology BigOperators ContDiff
variable {G:Gauge}{d n m:ℕ}

lemma scenic_seat (g:G.El)(X:TaylorTower G):scenic d (seat d (shade g X))= Show.paint g (scenic d (seat d X)):=by
  unfold scenic castBlaze; rw [LinearMap.comp_apply,LinearMap.comp_apply, LinearMap.sum_apply,LinearMap.sum_apply,map_sum]; apply Finset.sum_congr rfl; intro i _; change release (seat d (shade g X) i).val = Show.paint g (release (seat d X i).val); rcases i with ⟨i,h⟩; cases i with
  | zero => change release (0: Vase 0 G.Color) = Show.paint g (release (0: Vase 0 G.Color)); rw [map_zero,map_zero]
  | succ i=> let a:=gaugeJet (X i); change release (fit (gaugeJet ((shade g X) i))) = Show.paint g (release (fit a)); rw [show gaugeJet ((shade g X) i)=Labels.Taylor.paint g a from equiv_curl ..]; funext x; change Litter.board _ ((Labels.Taylor.paint g a).val x.2)=G.adjoint g (Litter.board _ (a.val x.2)); unfold Litter.board; simp only [LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_smul];rfl -- edit
lemma import_knob (v:Stamp G)(h:Show.Color G v)(d:ℕ)(g:G.El): pigment g (archive d (overture d v))=archive d (overture d v):=by
  apply equalPol; intro A; rw [pigment_action,dicto,dicto,music_at,music_at,scenic_seat,←Show.greener,h]
lemma preserve (v:Stamp G)(h:Show.Color G v)(d k:ℕ): archive d (trunc coin k (overture d v)) ∈ shellSector G k:= by
  apply sector.mpr; refine ⟨amber_bound (transported coin _ _),fun g=>?_⟩; rw [← cutback]; unfold trunc; rw [LinearMap.sum_apply,map_sum]; refine Finset.sum_congr rfl fun i _=>?_ ;
  rw [← Maxwell.Free.commuting scaleW scaleW _ (fun i=> ?_), import_knob v h d g]; rw [pigment,aeval_X]; exact symbol_hom _ (fun i=>i+2)
lemma guarded (v:Sec G d)(k:ℕ): trunc scaleW k v.val ∈ shellSector G k := by apply sector.mpr; refine ⟨transported scaleW _ _,fun g=>?_⟩; unfold trunc; rw [LinearMap.sum_apply,map_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [← Maxwell.Free.commuting scaleW scaleW _ (fun i=> ?_), (sector.mp v.property).2 g]; rw [pigment,aeval_X]; exact symbol_hom _ (fun i=>i+2)

variable (W:Initialize G)
def unmeasured (n :ℕ) : (On.Grade G n) →ₗ[ℂ] Stamp G:= (Encore.reel (W.surveys n) 0).toLinearMap ∘ₗ On.lifting.toLinearMap ∘ₗ (On.Grade G n).subtype
lemma premiere (u:On.Grade G n):unmeasured W n u= Prelude.enter0 (W.surveys n) u:=by unfold Prelude.enter0; rw [Price.preparedV];rfl
def screenplay (d:ℕ): Sec G d →ₗ[ℂ] Stamp G:= ∑ i: Fin (d+1), unmeasured W i ∘ₗ Normalize.part d i
lemma screen (p: Sec G d): screenplay W d p=∑ i:Fin (d+1), Prelude.enter0 (W.surveys i) (Normalize.part d i p):=by unfold screenplay; simp_rw [LinearMap.sum_apply,LinearMap.comp_apply,premiere W]
lemma color_form (p:Sec G d):Show.Color G (screenplay W d p):=by
  intro g; rw [screen,map_sum]; apply Finset.sum_congr rfl; intro i _; unfold Prelude.enter0; rw [← Encore.tuned]; exact Show.program _ _ g
lemma radialPoly (p: Sec G d): cross (radial G d) (overture d (screenplay W d p))= overture d (screenplay W d p):=by apply sameCap; intro B; rw [crossing, music_at,music_at,screen,map_sum,map_sum]; apply Finset.sum_congr rfl; intro i _; exact steps_back B (status _ _)

def portal (d:ℕ): Sec G d →ₗ[ℂ] Sec G d:= LinearMap.codRestrict _ ((archive d).toLinearMap ∘ₗ trunc coin d ∘ₗ (overture d).toLinearMap ∘ₗ screenplay W d) fun p : Sec G d=> preserve _ (color_form W p) _ _
lemma analysis_portal (p: Sec G d):(portal W d p).val=archive d (trunc coin d (overture d (screenplay W d p))):=rfl
lemma solo (h:n≤d)(p:On.Grade G n): screenplay W d (en h p)=unmeasured W n p:=by unfold screenplay; rw [LinearMap.sum_apply]; let i :Fin (d+1):= ⟨n,by omega⟩; rw [Finset.sum_eq_single i]; change unmeasured W n (Normalize.part d n (en h p))=_; rw [part_same]; intro z _ hz; rw [LinearMap.comp_apply,part_other p (by contrapose! hz; exact Fin.ext hz),map_zero]; simp
lemma into (h:n≤d)(p:On.Grade G n): (portal W d (en h p)).val=stageCost (W.surveys n) h p:=by rw [analysis_portal,solo,premiere];rfl
lemma partial_job (h:n≤d)(hl:m≤n)(p:On.Grade G n):Normalize.part d m (portal W d (en h p))=Normalize.part d m (en h p):=by
  apply Subtype.ext; simp_rw [val_part,into]; change Lows.Cut scaleW m _ = Lows.Cut scaleW m p.val; rw [← show trunc scaleW n (stageCost (W.surveys n) h p)= p.val from pure_stage ..];
  have ht(v:WickPol G): Lows.Cut scaleW m (trunc scaleW n v) = Lows.Cut scaleW m v:=by ext i; simp only [Lows.Cut,coeff_weightedHomogeneousComponent,trunc_ap]; split_ifs <;> first | omega|rfl
  rw [ht]
private lemma independent (p:Sec G d)(h:portal W d p=0): p=0:=by
  have he(k:Fin (d+1)):Normalize.part d k p=0:=by
    induction k using WellFoundedLT.induction with
    | _ k ih =>
      have H := congr_arg (Normalize.part d k) h; conv at H => lhs; arg 2; arg 2; rw [← enfits p]; skip
      simp_rw [map_zero, map_sum] at H; rw [Finset.sum_eq_single k] at H; rw [partial_job W (m:=k.val) _ le_rfl,part_same] at H; exact H
      intro i _ hi; cases lt_or_gt_of_ne hi with | inl h=> rw [ih i h,map_zero,map_zero,map_zero] | inr h=> rw [partial_job W _ (h.le : k.val≤ i.val),part_other _ (fun h=> hi (Fin.ext h.symm))]
      simp
  rw [← enfits p]; simp_rw [he, map_zero, Finset.sum_const_zero]
lemma exchangeable (d:ℕ): Bijective (portal W d):= by
  suffices h:Injective (portal W d) from ⟨h,LinearMap.injective_iff_surjective.mp h⟩; exact LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (independent W))

def migrate (d:ℕ): Sec G d ≃ₗ[ℂ] Sec G d:= LinearEquiv.ofBijective (portal W d) (exchangeable W d)
end YM.XSpace.Bracket
