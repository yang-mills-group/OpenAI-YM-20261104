import YM.SignedWilsonExpansion.MassShift
namespace YM.SignedWilsonExpansion.MarkShift
/-! Two-leg high propagation at order two. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Outlook MS.Emit MS.Heat MS.Rake
open HighScale HighRank TreeLine TreeView LocalForm MarkRows MassShift
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}
variable {B : Deck G}{M:Booked B}(S:MS_Data G M)(x:I B→ℝ)(simple:G.Simple)
local notation "R" => packet S x
local notation "N" => ground x
local notation "U" => Archive 4 S.bulk
local notation "κ" => PlanetD G
lemma blank (t:Clock ℝ)(w:Legs (Lane4 G))(h:0<w.length) (v:ℝ) : leap v (R 0) t w=0:= sub_eq_zero.mpr ((starts S x (t.1+v,t.2) w h).trans (starts S x t w h).symm)
lemma mark_single (e:ℕ)(t:Clock ℝ)(w:Lane4 G)(simple:G.Simple): R e t [w]=0:= single_off _ false (MarkRows.solid S x e t) simple w (fun x=>Bool.noConfusion x)
include simple
lemma pair_static : Static (R 1) 2 4 false:= by
  refine static_of ?_ (sheared S x 1 2) (fun E _ _ w hw ht t=> polish S x 1 t E w) (renew S x 1)
  intro y t w hw hr
  obtain he:=time_derivative w (speed S x 1 (ray w)) hw y t
  unfold recu at he
  let s:=(y,t)
  rw [tree_first, Pi.add_apply, cycle_height _ _ _ _ false hw (fun i hi hx=> level1 S x (y,t) i hi (by omega)), tree_height _ _ _ _ false hw ?_, add_zero] at he; exact he
  intro i j hh; by_cases ht:i=2
  · right; intro w' h hw
    rw [starts S x (y,t) w' (by omega)]; exact (born x).2.2 w' h (by omega)
  left; intro w' h h'; rw [BulkTop.paid1 S simple _ _ (by omega) h]; exact BulkTop.bulk1_r (G:=G) 0 w' (by rw [mod_int]; omega)
lemma first_quiet (t:Clock ℝ)(w:Legs (Lane4 G))(h:0<w.length)(v:ℝ): leap v (R 1) t w=0 := by
  apply sub_eq_zero.mpr; let b:=(t.1+v,t.2); change R 1 b w=R 1 t w
  by_cases hi:w.length=1
  · obtain ⟨i,rfl⟩:= List.length_eq_one_iff.mp hi; rw [mark_single S x _ _ _ simple,mark_single S x _ _ _ simple]
  by_cases hr:w.length=2
  · exact (pair_static S x simple).same _ _ _ _ w (fun i=>Bool.noConfusion i) hr
  rcases lt_or_eq_of_le (show 3≤w.length from by omega) with ht|ht
  · have hv s:= level1 S x s w (fun x=>Bool.noConfusion x) ht; rw [hv,hv]
  have he:= (MarkTop.corner S x).same b.1 t.1 b.2 t.2 w (fun h=> Bool.noConfusion h) ht.symm
  exact sub_left_inj.mp he

omit simple
lemma compare_context (K:TreeLine.Line G){X Y V A: Law G}(hx:∀w,0<w.length→net w=0→X w=Y w)(ha:∀w,0<w.length→ V w=A w): tree parity K X V=tree parity K Y A:= by
    funext w; unfold tree; apply scatter_congr; intro l r _; unfold attaches; simp_rw [hx ((_,-net l)::l) (by simp) (by simp), ha ((_,_)::r) (by simp)]

abbrev wall (v:ℝ): Law G:= Book.mask 2 (leap v (bulkD S) (0,0))
abbrev bridge (v t:ℝ): Law G:= tree parity (chi G t) (wall S v) N
abbrev settled (v:ℝ): Reading G:= leap v (R 2)-(bridge S x v ∘ Prod.snd)
local notation "Kx" => spaceD G
include simple
lemma token (v:ℝ)(t:Clock ℝ)(w:Legs (Lane4 G))(hw:0<w.length)(hr:net w=0): leap v (bulkD S) t w=wall S v w:= by
  by_cases hi:w.length=2
  · rw [wall,Book.enough _ (by omega)]; exact (static_b S simple v).same _ _ _ _ w (fun _=>hr) hi
  rw [wall,lonely S simple v t w (fun _=>hr) hw hi,Book.strange _ (by omega)]
lemma even_step (F:Law G)(hp:MarkTop.Completion x F)(v:ℝ)(t:Clock ℝ)(w:Legs (Lane4 G))(hw:w.length=2):
    leap v (recu Kx 0 1 U R 2) t w= tree parity ((Kx).meter t.2) (wall S v) N w:= by
  let s:=(t.1+v,t.2)
  let K:=(spaceD G).meter t.2
  have hc: cycle K (Kx).measure (R 2 s) w=cycle K (Kx).measure (R 2 t) w:=cycle_eq K _ (b:=false) (fun h=>Bool.noConfusion h) (fun z hz hr=> (MarkTop.evaluation S x F hp s z (by omega)).trans (MarkTop.evaluation S x F hp t z (by omega)).symm)
  have ht a: Heat.boulevard parity K (U 1 a) (R 1 a)= Heat.boulevard parity K (BulkTop.cub G) (R 1 a):= compare_context K (fun w hw he=> BulkTop.paid1 S simple a w hw he) (fun _ _=>rfl)
  have hx : Heat.boulevard parity K (BulkTop.cub G) (R 1 s)= Heat.boulevard parity K (BulkTop.cub G) (R 1 t):= compare_context K (fun _ _ _=>rfl) (fun w h=> sub_eq_zero.mp (first_quiet S x simple t w h v))
  have hv a : Heat.boulevard parity K (U 2 a) (R 0 a)= Heat.boulevard parity K (U 2 a) N:= compare_context K (fun _ _ _=> rfl) (fun w h=>starts S x a w h)
  have hi : Heat.boulevard parity K (U 2 s-U 2 t) N= Heat.boulevard parity K (wall S v) N:= compare_context K (fun w hw he=> token S simple v t w hw he) (fun _ _=>rfl)
  change recu Kx 0 1 _ _ 2 s w-recu Kx 0 1 _ _ 2 t w=_
  unfold recu; rw [tree_second,tree_second]
  simp only [←Heat.blvd,Pi.add_apply]; change cycle K _ _ _+(Heat.boulevard parity K _ _ w+Heat.boulevard parity K _ _ w)-(cycle K _ _ _+(Heat.boulevard parity K _ _ w+Heat.boulevard parity K _ _ w))=_
  rw [hc,hv,hv,ht,ht,hx,← hi,map_sub]; simp only [LinearMap.sub_apply,Pi.sub_apply]; abel
lemma bridge_static (F:Law G)(hp:MarkTop.Completion x F)(v:ℝ): Static (settled S x v) 2 4 false:= by
  have hc : Polish (wall S v):= by
    intro E _ _ w; by_cases he:w.length=2
    · have hx: fieldVal (wall S v) w=fieldVal (leap v (bulkD S) (0,0)) w:= funext fun x=> Book.enough _ (by simp [he])
      rw [hx]; exact (hair (bulkView S 2 (by omega)|>.host) (n:=0) (y:=0+v) (s:=0) w).sub (hair (bulkView S 2 (by omega)|>.host) (n:=0) (y:=0) (s:=0) w)
    rw [show fieldVal (wall S v) w=0 from funext fun x=> Book.strange _ (show ((sail w x).length:ℤ) ≠ 2 from by rw [sail_len]; omega)]; exact contDiff_const
  refine peel_static (D:=fun x' : Clock ℝ => tree parity (κ x'.2) (wall S v) N)
    (fun t=> Polish.sub (polish S x 2 (t.1+v,t.2)) (polish S x 2 t)) (verges _ (sheared S x 2 2)) (stamp_shift v (renew S x 2)) ?_ ?_ ?_ ?_
  · exact fun t=> hc.chi (fun E _ _ w=> ((born x).2.1 E w (fun h=>Bool.noConfusion h)).smooth) t
  · exact ((shear_form (F:=wall S v) ((bulk_class S simple v (0,0)).graded)).tree (shear_form (born x).2.1)).cov _
  · intro y t w hw hr; have h:=gap (u:=v) w (speed S x 2 (ray w)) (y,t) hw; rw [even_step S x simple F hp v _ w hr] at h; exact h
  exact fun _ t w _ _=> TreeView.tree_deriv ..
lemma per_mark (F:Law G)(hp:MarkTop.Completion x F)(v:ℝ)(t:Clock ℝ)(w:Legs (Lane4 G))(hw:w.length=2):
    leap v (R 2) t w = settled S x v (0,0) w + bridge S x v t.2 w := sub_eq_iff_eq_add.mp ((bridge_static S x simple F hp v).same _ _ _ _ w (fun h=> Bool.noConfusion h) hw)
end
end YM.SignedWilsonExpansion.MarkShift
