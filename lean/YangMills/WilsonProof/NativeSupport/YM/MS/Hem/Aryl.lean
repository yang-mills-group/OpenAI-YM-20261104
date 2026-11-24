import YM.MS.Hem.Aryl
import YM.MS.Hem.Lore
/-!
# Engineering Taylor degrees suffice independent of field leaves count
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Hem
open Set Filter Function Finset MeasureTheory Metric Arc
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine
open scoped Topology ContDiff
variable {I:Type}{G:Gauge}{j m n k:ℕ}{x:ℂ}{R:ℝ}{F H:Mob G}
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
lemma dm {A:Type}(w:Legs (Mode (Cfield G m) A)) :0≤mass w := by induction w with| nil=> exact le_rfl| cons i l ih=> rw [Price_cons]; exact add_nonneg (by unfold wfield; omega) ih
-- total degree projector. Not requiring F sturdy, only kPrice for operations. Using .skin correct.
lemma t_bud (f:Mob G){l:Legs (Shore G m)}(h:mass l+j=n): Tad f n m l=torch j (f m) l:= skin_eq _ _ _ h -- placeholders
lemma t_exc {l:Legs (Shore G m)}(h:(n:ℤ)<mass l): Tad F n m l=0:= if_neg h.not_ge
lemma film {w:Touch G m E}(h:ContDiff ℝ ∞ (fieldVal ( F m) w))(hx:mass w+j=n): fieldVal (Tad F n m) w=stage j ( fieldVal (F m) w):= by funext p; unfold fieldVal; rw [t_bud F (l:=sail w p) (show mass (sail w p)+j=n from (by rwa [mass_sail]))]; exact lit _ _ h p -- Infer j
lemma plane {w:Touch G m E}(h:(n:ℤ)<mass w): fieldVal (Tad F n m) w=0:= funext fun p=>t_exc (l:=sail w p) (by rwa [mass_sail])
variable {f:I→Mob G}
lemma tad_fall (h:fell 0 1 f)(k:ℕ): fell 0 1 (fun i=> Tad (f i) k):= by
   intro m E _ _ _ w; by_cases hp:(k:ℤ)<mass w; · simp_rw [plane hp]; exact Costs.zero fun _ _ _=> zero_le_one
   have he : mass w+(((k:ℤ)- mass w).toNat:ℤ)=k:= by omega
   simp_rw [film ( (h m E w).smooth _) he]; exact merch (h m E w) _
lemma tad_price (h:kPrice F)(k:ℕ): kPrice (Tad F k):= tad_fall h k
lemma tad_hol (f:ℂ→ Mob G)(h:Hol (disc R) f)(n:ℕ): Hol (disc R) (fun i=> Tad (f i) n) where
   price c T ht hp:= tad_fall (h.price c T ht hp) n
   top:= by
       intro m l; rcases lt_or_ge (n:ℤ) (mass l) with h1|h1; · simp_rw [t_exc h1]; exact fun _ _=>differentiableAt_const _
       let j:= ((n:ℤ)-mass l).toNat; have hx:mass l+j=n:= by unfold j; omega
       have ht := jet (key_fall h (ray l)) j; simp_rw [t_bud _ hx]; exact ht.root (1:ℝ)
lemma tad0 (k:ℕ): Tad (0:Mob G) k=0:= by ext; unfold Tad skin; split <;> simp [torch_at,reading]
lemma stage_add {f g:E→ℂ}(h:ContDiff ℝ ∞ f)(H:ContDiff ℝ ∞ g)(n:ℕ): stage n (f+g)=stage n f+stage n g := by
    unfold stage; rw [Tensor.coeff_add]; rfl; exact (h.of_le (by exact_mod_cast le_top)).contDiffAt; exact (H.of_le (by exact_mod_cast le_top)).contDiffAt
lemma t_plus (h:kPrice F)(hp:kPrice H)(n:ℕ): Tad (F+H) n=Tad F n+Tad H n:= by
    funext m l; rcases lt_or_ge (n:ℤ) (mass l) with h1|h1; · rw [Pi.add_apply,Pi.add_apply,t_exc h1,t_exc h1,t_exc h1,add_zero]
    have he : mass l+(((n:ℤ)-mass l).toNat:ℤ)=n:= by omega
    simp_rw [Pi.add_apply,t_bud _ he]; exact congr_fun (stage_add ((h m ℝ (ray l)).smooth ()) ((hp m ℝ ( ray l)).smooth ()) _) (1:ℝ)
lemma t_pose (c:ℂ)(n:ℕ): Tad (c • F) n=c • Tad F n:= by
    funext m l; unfold Tad skin; split <;> rename_i h
    · simp_rw [Pi.smul_apply,if_pos h,torch_at]; exact Plane.read_const c _
    rw [Pi.smul_apply,Pi.smul_apply, if_neg h,smul_zero]
lemma t_neg (n:ℕ): Tad (-F) n= -Tad F n:=by simpa using t_pose (F:=F) (-1) n
lemma t_minus (h:kPrice F)(hp:kPrice H)(n:ℕ): Tad (F-H) n=Tad F n-Tad H n:= by
   simp_rw [sub_eq_add_neg]; rw [t_plus h (show kPrice (-H) from ?_), t_neg]; convert fall_sub (fall_zero (fun _:Unit=>zero_le_one)) hp using 1; ext; simp -- possible weird Unit type
lemma t_already (n:ℕ)(hp:kPrice F)(m:ℕ): Tad (Tad F n) m=if n=m then Tad F n else 0:= by
   funext s l; let w:=ray l; have he:mass w=mass l:= ray_dim _
   rcases lt_or_ge (n:ℤ) (mass l) with h1|h1
   · rcases lt_or_ge (m:ℤ) (mass l) with h2|h2; rw [t_exc h2]; split; rw [t_exc h1]; rfl; have hm: mass l+((m-mass l).toNat:ℤ)=m:= by omega
     rw [t_bud _ hm, if_neg (by omega: n≠m)]; unfold torch; rw [plane (by rw [← he] at h1; exact h1)]; simp [stage,Tensor.diagonal,Tensor.coeff]
   have ht: mass w+(((n:ℤ)-mass l).toNat:ℤ)=n:= by omega
   rcases lt_or_ge (m:ℤ) (mass l) with h2|h2; · rw [t_exc h2,if_neg (by omega : n≠m)]; rfl
   have hL: mass l+(((m:ℤ)-mass l).toNat:ℤ)=m:=by omega
   rw [t_bud _ hL]; unfold torch; rw [film ((hp s ℝ w).smooth ()) ht, (Plane.Shape.stage' (show Shape (stage ((n:ℤ)-mass l).toNat (fieldVal (F s) w)) _ from form_diag _ _ rfl))]; split <;> rename_i h <;> (split <;> first| omega | rfl| (rw [t_bud F (by rw [← he]; exact ht)]; rfl) ) -- verify
end YM.MS.Hem
