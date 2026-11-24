import YM.MS.Hem.Gait
/-!
# Seats for subspaces
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Hem.Mell
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine
open scoped Topology ContDiff Interval
variable {I E:Type} {G:Gauge}{W S:Mob G}{b:Bool} {i:ℤ}
abbrev Need (Q:LeanC G):= Will (Q.restrictScalars ℝ)
lemma need_true : Need (sturdy b G) where
    touch:= Wind.time
    walk x s h := Stays h 0 s
    runner:= by
       intro u t hi h; change Sturdy b (mend u t); replace h : ∀ i,Sturdy b (u i):= h; constructor
       · intro m K hk; funext l; obtain he := cent_arguments (volume.restrict (Iic t)) ((flagS K G).sense|>.reaches l) (f:=fun i=> u i m) (hi m); simp_rw [(h _).turn m K hk] at he; exact he.2.symm -- trace maybe pattern
       intro m n hu l; unfold mend; simp_rw [(h _).grows hu]
       -- hole
lemma need_tail : Need (grade i G) where
   touch := Wind.peerU
   walk x s h := by replace h:Issue i x:=h; intro m l ht; simp only [plow, h m (sr s l) (by simpa [sr] using ht), mul_zero]
   runner := by intro F r ht h; replace h: ∀ s,Issue i (F s):= h; intro n l hu; unfold mend; simp_rw [h _ n l hu]; simp
lemma need_rank : Need (good i G) where
    touch:= Wind.peerG
    walk x s h:= by replace h:Goods i x:=h; intro m l ht; rw [Book.mod_int] at ht; unfold plow; rw [ranks_off h _ (by simpa [sr] using ht), mul_zero]
    runner u t hi hp:= by
       replace hp: ∀ i':ℝ, Goods i (u i'):= hp; intro m l ht; unfold mend; simp_rw [hp _ m l ht]; simp
lemma need_col : Need (collar i G) where
    touch:= Wind.tuned
    walk x s h:= by replace h:Collar i x:=h; exact ⟨plow_sym h.sym 0 s,hue_scale h.color s 0, plow_ghost h.ghost 0 s⟩
    runner u t h hp:= by
       replace hp: ∀ j, Collar i (u j):= hp; change Collar i _; constructor
       · intro m a i j b; unfold mend; simp_rw [(hp _).sym m a i j b]; rw [integral_const_mul]
       · intro m K; funext l; obtain H:= cent_arguments (volume.restrict (Iic t)) (sense (dye (D:=Arts.L m) K)|>.reaches l) (f:=fun i=> u i m) (h m); rw [brush] at H; simp_rw [(hp _).color m K] at H; exact H.2.symm
       intro m l h; unfold mend; simp_rw [(hp _).ghost m l h]; simp
lemma need_eye : Will (sight G) where
    touch:= Wind.still
    walk x s h:= glance h 0 s (star_zero ..)
    runner u t hi h:= by replace h:∀ i,Sight (u i):=h; intro m l; unfold mend; simp_rw [h _ m l]; exact integral_conj
end YM.MS.Hem.Mell
