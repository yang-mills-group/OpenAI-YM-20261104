import YM.MS.Wind.Bon
/-!
# Paying all pointwise operations

Moment cut and lengths. L0 rank cost exactly shifted. Extend by chosen orbit on all
 raw; disk always uses Pass.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Wind
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open Landau Native Lattice Tone Momentum Heat Real Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{F H:Flow G}{P Q:Pack G}{b:Bool}{u v r r':ℤ}{I:Type}{t:ℝ}
-- rank-shift helpers for Heat

namespace Modeled
variable {K: Flux (BH G) QP ℂ}{F H:Law G}
lemma lapQuote (h: Pass K F μzone)(hk:Limit F r): Limit (orbit K μzone F) (r-2):= by
   rw [finite_cc μzone h]; intro l he; unfold Ccy; have he' (q:QP): trc K q F l=0:= by rw [at_trc]; apply Finset.sum_eq_zero; intro i _; exact Finset.sum_eq_zero (fun j _=> by rw [hk ((i,q)::(j,-q)::l) (by simp; omega),mul_zero])
   simp_rw [he']; simp
-- empty outputs fine
lemma guard (hp:Limit F r)(hv: Limit H r') (K:Flux (BH G) QP ℂ): Limit (boulevard parity K F H) (r+r'-2):= by
   intro l hh; rw [blvd,tree, scatter_congr _ l _ (fun _ _=>(0:ℂ)) ?_]; exact map_zero (allocate ..)
   intro a b he; unfold attaches; dsimp only; apply Finset.sum_eq_zero; intro i _; refine Finset.sum_eq_zero fun j _=>?_; have hd:= split_length he; by_cases H':r<a.length+1; · rw [hp ((i,-net a)::a) (by simp [H']),hp ((j,- net a)::a) (by simp [H'])]; ring
   rw [hv ((i,- -net a)::b) (by simp; omega),hv ((j,- -net a)::b) (by simp; omega)]; ring
lemma Qmax (Q:Charge (Landau.parity (A:=Axis) (C:=CI G)) QP ℂ) (hp: Limit F r): Limit (Q.raise F) r:= by intro l hl; rw [visit_Z, ← visit_zero (R:=ℂ) (b:=true) (p:=parity) l]; apply visit_agree; intro i a b hv; apply Finset.sum_eq_zero; intro j _; rw [hp (i++(j,a.2)::b) (by rw [← hv] at hl; simpa using hl),mul_zero]
lemma lap_symm (μ:Measure QP) (H:Symm (field parity) F): Symm (field parity) (Ccy K F μ):= by
    intro l i j r; unfold Ccy; rw [← integral_const_mul]; refine integral_congr_ae (Eventually.of_forall (fun x=>?_)); have he : Symm (field parity) (trc K x F):= by simp only [trc, LinearMap.sum_apply, LinearMap.smul_apply]; exact Symm.sum _ fun i _=> Symm.sum _ fun j _=> Symm.smul _ ((H.drop _).drop _)
    exact he l i j r
end Modeled
open Modeled Signal

def lapidus (K:ℝ→Flux (BH G) QP ℂ): Flow G→ₗ[ℂ] Flow G:= LinearMap.pi fun i=> (orbit (K i) μzone).comp (LinearMap.proj i)
lemma lapid_touch {K:ℝ→Flux (BH G) QP ℂ}(h: TouchF F)(he:flex K): TouchF (lapidus K F):= loop_on μzone cour0 he h
lemma lapid_s (h: Bon b u F): Bon b u (lapidus (Cpu G) F) := by
    let V:=Cpu G; have hp (t:ℝ): Pass (V t) (F t) μzone:= period0 μzone cour0 (main_f _) h.joint;
    have he t : lapidus V F t=Ccy (V t) (F t) μzone:= finite_cc μzone (hp t)
    refine ⟨lapid_touch h.joint (main_f _),?_,?_,?_,?_,?_,?_⟩ <;> intro t <;> rw [show lapidus (Cpu G) F t=_ from he t];
    · exact lap_symm μzone (h.sym t)
    · exact (h.perk t).loop _
    · exact inv_trace (h.real t) truthP
    · exact winsL (h.pulse t) fun _ _ _=> City.l_zero
    · intro i; rw [show repeatC i (Ccy (V t) (F t) μzone)= _ from cycle_dye (City.L0 t) wave i μzone (hp t),h.t_color]
    exact fun p=> cycle_t (h.stand t p)
lemma lapid_max {K:ℝ→Flux (BH G) QP ℂ}(h:TouchF F)(he:flex K)(hr:Rank F r): Rank (lapidus K F) (r-2):= fun x=> lapQuote (period0 μzone cour0 he h) (hr x)

def busy (K:ℝ→Flux (BH G) QP ℂ) : Flow G→ₗ[ℂ] Flow G→ₗ[ℂ] Flow G where
    toFun F:= LinearMap.pi fun i=> (boulevard parity (K i) (F i)).comp (LinearMap.proj i)
    map_add' F H:= LinearMap.ext (fun G'=> by ext; simp)
    map_smul' x F:= LinearMap.ext (fun G'=> by ext; simp)
lemma busy_s {K:ℝ→ Flux (BH G) QP ℂ}(h:TouchF F)(hx: TouchF H)(he: flex K)(hk: ∀ x:ℝ,Reverse (K x) parity): TouchF (busy K F H):= tree_touch hk he h hx
-- rotation when first enabled even for second at net guard. use b for both from mapping below.
lemma grow_s (h:Bon true u F)(he: Bon b v H): Bon b (u+v) (busy (Cpu G) F H) where
   joint:= busy_s h.joint he.joint (main_f _) (Vrev G)
   sym t:= tree_sym (City.X_even G t) (h.sym t) (he.sym t)
   perk t:= (h.perk t).keeper (he.perk t) (h.sym t) (he.sym t) (City.L_stamp _) (Vrev G t) (City.X_even G t) -- fix
   real t:= globe (h.real t) (he.real t) truthP (Vrev G t)
   pulse t:= win_tree (h.pulse t) (he.pulse t) (Vrev G t) (fun _ _ _=> l_zero)
   t_color t i:= by change repeatC i (tree parity (Landau.choir (City.L0 t) wave) (F t) (H t))=_; rw [show repeatC _ (tree _ _ _ _)= _ from tree_dye _ _ i (h:=X_even G t) (F:=F t) (H:=H t), h.t_color,he.t_color]; rfl
   stand t hx:= alight_t (h.stand t rfl) (he.stand t hx)
lemma busy_max (K:ℝ→Flux (BH G) QP ℂ)(h:Rank F r)(ht:Rank H r'): Rank (busy K F H) (r+r'-2) := fun i=> Modeled.guard (h i) (ht i) (K i)

-- polyn payments
lemma lapidPack (h:Fees b u P): Fees b u (fun x=> lapidus (Cpu G) (P x)) where
   stay x:= lapid_s (h.stay x)
   pay:=by obtain ⟨v,hv⟩:= h.pay; exact ⟨v,fun i=> Rank.pay (lapid_max (h.stay i).joint (main_f _) (hv i)) (by omega)⟩
   currency:= h.currency.linear ((lapidus (Cpu G)).restrictScalars ℝ)
private def pairR (M:Flow G→ₗ[ℂ] Flow G→ₗ[ℂ] Flow G): Flow G→ₗ[ℝ] Flow G→ₗ[ℝ] Flow G where
   toFun F:= (M F).restrictScalars ℝ
   map_add' F H:= by apply LinearMap.ext; intro; simp
   map_smul' c F:=by apply LinearMap.ext; intro t; rw [show c • F=(c:ℂ) • F from rfl, map_smul]; rfl
lemma busyPack (h: Fees true u P) (hp: Fees b v Q): Fees b (u+v) (fun x=> busy (Cpu G) (P x) (Q x)) where
   stay x:= grow_s (h.stay x) (hp.stay x)
   pay:= by obtain ⟨A,hA⟩:=h.pay; obtain ⟨B,hB⟩:=hp.pay; exact ⟨A+B,fun i=> Rank.pay (busy_max _ (hA i) (hB i)) (by omega)⟩
   currency:= Ready.pair (pairR (busy (Cpu G))) h.currency hp.currency
end YM.MS.Wind
