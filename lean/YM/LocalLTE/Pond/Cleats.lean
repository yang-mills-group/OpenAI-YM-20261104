import YM.LocalLTE.Pond.Pips
/-! Budget handoff, oxidizing pre+post affines. No receptive assumptions on stencil prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
-- uniform over all low rows. weights only station 
open Residual Geo Animals
-- inverse temp ≤ sqrt(t), shift
lemma curveT (L:Side) : Rate G L 1 (fun t=> (Pressure.temp t ^(2:ℕ))⁻¹) := by
   apply Rate.compare (Rate.hat (G:=G) (L:=L)); filter_upwards [eventually_gt_atTop (0:ℝ),Delay.shift_pos G L] with t ht hx
   rw [abs_of_nonneg (by positivity),abs_of_pos hx]; have h: 1 ≤ Real.exp ((Real.log (Real.log t))^2):= Real.one_le_exp (by positivity)
   refine le_trans (b:=t) ?_ (le_add_of_nonneg_right (Work.E04.shift_nonneg ..)); unfold Pressure.temp; rw [mul_pow, inv_pow, Real.sq_sqrt ht.le, mul_inv_rev,inv_inv]; exact mul_le_of_le_one_left ht.le (inv_le_one_of_one_le₀ (one_le_pow₀ h))
-- shorthand native. Cost.E.radius.
structure Art (i:RegularAddress n) (z:ℕ) where
   grove : Grove i.site
   radius : ℕ
   crisp : i.support=neighbors z i.site
   bonus : radius<z
   hearth: 2 ≤ radius
variable {G}
def Replicated {o:Site n}(X:Grove o)(m:ℕ)(κ:ℝ)(p:ℕ)(f:Config G n→ℝ): Prop:= ∃ P: LocalLTE.Cabana.Pkt (Directions G n) p, f= LocalLTE.FrameBox.realise X m κ P
variable {κ q:ℝ} {Z: BudgetPoint}{o:Site n}{N j i z:ℕ} {a:RegularAddress n} (A:Art a z)(f:Config G n→ℝ)
-- Local syntax
section pack
variable (X:Grove o){f g:Config G n→ℝ}
lemma rp_add (h:Replicated X i κ j f)(ht:Replicated X i κ j g): Replicated X i κ j (f+g):= by
   obtain ⟨P,rfl⟩:= h; obtain ⟨Q,rfl⟩:= ht; exact ⟨P+Q,funext fun x=>by unfold realise; rw [LocalLTE.Cabana.actual_add]; rfl⟩
lemma rp_scale (c:ℝ) (h:Replicated X i κ j f): Replicated X i κ j (c• f):=by
   obtain ⟨P,rfl⟩:= h; exact ⟨c•P,funext fun x=>by unfold realise; rw [LocalLTE.Cabana.actual_smul]; rfl⟩
lemma rp_sub (h:Replicated X i κ j f)(ht:Replicated X i κ j g): Replicated X i κ j (f-g):=by
   simpa only [sub_eq_add_neg,neg_one_smul] using rp_add X h (rp_scale X (-1) ht)
open Tensor in
lemma rp_flat (p:ℝ): Replicated (G:=G) X i κ (j+1) (Function.const _ p):=by
   let f: Directions G n→ℝ:=fun _=>p
   refine ⟨fun z=> Tensor.coeff f z 0,?_⟩; funext x; change p= (LocalLTE.Cabana.actual (E:=Directions G n) (n:=j+1) (fun z=>Tensor.coeff f z 0) _)
   unfold LocalLTE.Cabana.actual; rw [Finset.sum_apply,Finset.sum_eq_single ⟨0,Nat.zero_lt_succ j⟩]
   · unfold Tensor.diagonal; rw [Tensor.coeff_apply_zero]
   · intro v _ hv; have hz:v.val≠0:=fun he=> hv (Fin.ext he)
     unfold Tensor.coeff diagonal; dsimp only; rw [show iteratedFDeriv ℝ v.val f 0=0 from congr_fun (iteratedFDeriv_const_of_ne hz p) 0]; simp
   simp
lemma rp_raise (h:Replicated X i κ j f)(hp:j≤z): Replicated X i κ z f:=by
   induction hp with
   | refl=> exact h
   | @step y hh ih=>
      obtain ⟨P,h⟩:= ih
      let Q: LocalLTE.Cabana.Pkt (Directions G n) (y+1) := fun i=> if hi:i.val<y then P ⟨i.val,hi⟩ else 0
      refine ⟨Q,h.trans (funext fun v=>?_)⟩
      unfold LocalLTE.FrameBox.realise LocalLTE.Cabana.actual; rw [Fin.sum_univ_castSucc]; simp only [Finset.sum_apply,Pi.add_apply]; rw [show Tensor.diagonal (Q (Fin.last y)) (X.crook i Chi.canonical κ v)=0 from (by rw [show Q (Fin.last y)=0 from dif_neg (by simp)]; rfl),add_zero]; apply Finset.sum_congr rfl; intro i h; unfold Q; rw [dif_pos (by simp)]; rfl
lemma rp_zero : Replicated X i κ (j+1) (0:Config G n→ℝ) := rp_flat X 0
end pack
local notation "y"=> neighbors A.radius a.site
local notation "u"=> payout a f
variable (h: Z.Regular a.support f)
lemma color_ext : halo 2 {a.site}⊆ y:= by
    intro i hi; obtain ⟨x,h,hk⟩:= halo_spec.mp hi; apply (neighbors_mem ..).mpr; rw [Finset.mem_singleton.mp h] at hk; exact hk.trans A.hearth
lemma color_site : y⊆ a.support:= by rw [A.crisp]; intro j hj; exact (neighbors_mem ..).2 (((neighbors_mem ..).1 hj).trans A.bonus.le)
include A
lemma extents : expand a=neighbors z a.site:=by unfold expand; rw [Finset.union_eq_left.mpr ((color_ext A).trans (color_site A)),A.crisp]

def myth (κ:ℝ)(j:ℕ) := (f - Function.const _ (f 1)) - Hall.shave A.grove A.radius κ (pie j+1) (Residual.payout a f)
lemma quake (k:ℕ)(h:Replicated A.grove A.radius κ (pie k+1) f): Replicated A.grove A.radius κ (pie k+1) (myth A f κ k):=
    rp_sub A.grove (rp_sub A.grove h (rp_flat A.grove (f 1))) ⟨_,rfl⟩
include h
lemma forge (j:ℕ) (ht: Reliable G κ q) : Z.Regular (expand a) (myth A f κ j):= by
    apply VerifiedReset.reg_sub (reg_sub (reg_larger h Finset.subset_union_left) (reg_const _)); exact reg_larger (LocalLTE.FrameBox.legal A.grove A.radius ht _ _) ((color_site A).trans Finset.subset_union_left)
-- Price: preserve all ambient jets θ, shown independently.Use differential equality.
omit h
local notation "R₀" => payout a f
lemma taylor (ht:Reliable G κ q)(P: BudgetPoint)(n:ℕ)(k:ℕ)(hk:i ≤ n) (hj : n < k) : iteratedFDeriv ℝ i (shave A.grove A.radius κ k u ∘ increment 1) 0 = iteratedFDeriv ℝ i (u ∘ increment 1) 0:=by
   obtain ⟨C,hp,hC⟩:= Price.vial G k; let t:=∑ i:PlaqAxes,∑ j:PlaqAxes,|projection a f i j|
   have hv: ContDiffAt ℝ k (u ∘ soloV) 0 := (hC _ _ _ t ?_ _ (by simp)).smooth; swap
   · intro i j; apply le_trans (b:=∑ j:PlaqAxes,|projection a f i j|) (Finset.single_le_sum (f:=fun j=>|projection a f i j|) (fun i _=>abs_nonneg _) (Finset.mem_univ j)) (Finset.single_le_sum (f:=fun i=>∑ j:PlaqAxes,|projection a f i j|) ?_ (Finset.mem_univ i)); exact fun _ _=> Finset.sum_nonneg fun _ _=> abs_nonneg _
   exact Hall.roots A.radius A.grove ht k P (Residual.payout a f) (reg_larger (counter_regular ..) (color_ext A)) hv i (lt_of_le_of_lt hk hj)
lemma crisp (ht:Reliable G κ q) (P:BudgetPoint)(j:ℕ): myth A f κ j 1=0:= by
    have h:= taylor A f ht P 0 (pie j+1) (le_refl _) (by unfold pie; omega); let g:= shave A.grove A.radius κ (pie j+1) u; have ht: g 1=u 1:=by
       have ht: (g ∘ increment (1:Config G n)) 0=(u ∘ increment 1) 0 := by
         change iteratedFDeriv ℝ 0 (g ∘ increment 1) _=_ at h; simpa only [iteratedFDeriv_zero_apply] using DFunLike.congr_fun h (fun _:Fin 0=>(0:Directions G n))
       simpa only [Function.comp_apply, Work.G07.at_zero_increment] using ht
    unfold myth; rw [Pi.sub_apply,show shave A.grove A.radius κ (pie j+1) (payout a f) 1=u 1 from ht]; simp only [payout,counter,quad,petals_one]; simp
include h
lemma kineticZero (hG:G.Simple)(hp: Nonwrapping (expand a) a.site)(hx:20<n.val)(ht: Reliable G κ q)(j:ℕ) (v w: Directions G n) (hV:IsAffineDirection a.site v)(hw:IsAffineDirection a.site w): logHessian (myth A f κ j) v w=0:=by
    let u':=u; let g:= shave A.grove A.radius κ (pie j+1) u'
    have he: Z.Regular (expand a) g:= reg_larger (LocalLTE.FrameBox.legal A.grove A.radius ht _ _) ((color_site A).trans Finset.subset_union_left)
    have hh: logHessian g v w= logHessian u' v w := DFunLike.congr_fun (taylor A f ht Z 2 (pie j+1) (le_refl _) (by unfold pie; omega)) _
    have hv:Z.Regular (expand a) (f-Function.const _ (f 1)):= reg_sub (reg_larger h Finset.subset_union_left) (reg_const _)
    change logHessian (_-g) _ _=_; rw [hessian_sub hv he,hh,← hessian_sub hv (payout_regular a h)]; exact Residual.rebate_vanish a hG h hp hx _ _ hV hw
end YM.AnalyticBridge.VerifiedReset.Collection.Price
