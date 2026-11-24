import YM.MS.Wilson.Eras

/-!
# Orders, rank stencils at tip

Polynomial growth in y with all orders of evaluated sums. Forms full parameters. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Native.Wilsonian
open Function Filter Set Finset Plane Koszul Cylinder Lab Book Convolve Program
open Paint Landau Bare Focus Taylor Draft Sew Chart Color Lattice Logarithm Orient
open PowerSeries (coeff)
variable {G:Gauge} {A P I:Type}{F H:T (Dot G Cover)}{M: ℝ→ T (Dot G Cover)}{q:ℤ}(p:Team)(x:ℝ) {r s : ℕ}
lemma stood (h:∀ i,Tuned (F i) q)(i:ℕ): Tuned (wobble G p x F i) q:= by
    rw [wobble,LinearMap.comp_apply,rolls]; apply Tune.sum; intro j _; rw [rules]; exact wob_trained _ _ _ (Tune.sum _ fun l _=> (h l).cash _ (((shiftR p).pow l j.2).starv _)) _
lemma induced (h:∀ i,Colorless (F i))(i:ℕ): Colorless (wobble G p x F i):= by
    rw [wobble,LinearMap.comp_apply,rolls]; apply Colorless.csum; intro j _ f; rw [rules]; rw [dye_train]; congr 1; exact Colorless.csum _ (fun l hl=> Colorless.smul _ (h l)) f
lemma honored (h:∀ i,stance (F i))(i:ℕ): stance (wobble G p x F i):= by
    rw [wobble,LinearMap.comp_apply,rolls]; refine scene_sum _ (fun j hj=>?_); rw [rules]; exact stanceTrain _ _ _ _ (scene_sum _ (fun l _=> scene_scale (h _) _))
variable {p x}
lemma sought (h:∀ i,i≤r→Limit (F i).val q) (hp:s≤r): Limit (substitute (shift p x) F s).val q:= by rw [rules,sum_stack]; exact Limit.sum _ fun j hj=>(h _ (le_trans (Finset.mem_Iic.mp hj) hp)).smul _
lemma inducedLimit (h:∀ i,i≤r→ Limit (F i).val q)(hp:s≤r): Limit (wobble G p x F s).val q:= by
    rw [wobble,LinearMap.comp_apply,rolls,sum_stack]; exact Limit.sum _ fun i hi=> merited (_ ∘ _) _ (sought h (by obtain h:=mem_antidiagonal.mp hi; omega))
variable (p x)
lemma brief (hs:∀ x i,i≤r→ Limit (M x i).val q)(hp:∀ i,Ready (fun x=>M x i)) : Ready (fun x=> wobble G p x (M x) r):= by
    unfold wobble; simp_rw [LinearMap.comp_apply,rolls]; refine value_sum _ (fun j hj=>?_);
    let D (x:ℝ) := substitute (shift p x) (M x) j.2; have hh x: Limit (D x).val q.toNat:= (sought (p:=p) (x:=x) (hs x) (show j.2≤r by obtain h:=mem_antidiagonal.mp hj; omega)).up (by omega)
    exact trained (fun i:LightMode G Cover=> i.1.1) (adap p) (adapR p) D (substituted (shiftR p) hp _) q.toNat j.1 hh
structure Circle (G:Gauge)(F:ℝ→ T (Dot G Cover))(b:Bool)(q:ℤ): Prop where
    actual (i:ℕ)(x:ℝ): Tuned (F x i) q
    room (i:ℕ): ∃ v:ℕ, ∀ s:ℝ, Limit (F s i).val v
    settled (i:ℕ)(x:ℝ): Colorless (F x i)
    tag (i:ℕ): Ready (fun x=>F x i)
    stance0 (x:ℝ)(i:ℕ): b=true → stance (F x i)
lemma style_limit (G:Gauge)(i:ℕ): Limit (style G p x i).val (i+2):= inducedLimit (F:=core G) (fun j hj=> Limit.up (participates G j) (by omega)) (le_refl i)
lemma core_circle (G:Gauge)(p:Team): Circle G (style G p) true 0 where
    actual i x:= stood p x (crisp G) i
    room i:= ⟨i+2,fun x=> by exact_mod_cast style_limit p x G i⟩
    settled i x:= induced p x (realm G) i
    tag i:= brief (M:=fun _=>core G) (r:=i) (q:= i+2) p (fun _ j hj=> Limit.up (participates G j) (by omega)) (fun i=> Ready.const _)
    stance0 x i _:= honored p x (observes G) i
end YM.MS.Native.Wilsonian
