import YM.SignedWilsonExpansion.LocalForm
namespace YM.SignedWilsonExpansion.MarkTop
/-! Evaluating the finite one-loop shape prediction requires BOTH the vacuum and marked heat-responses of the commissioned formal system. This computes the marked one-field *high tree* prior and propagation with no other scale premise. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Outlook MS.Emit MS.Garment MS.Heat MS.Rake
open BulkTop HighRank HighScale TreeLine TreeView LocalForm MarkRows
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{B:Deck G}{M:Booked B} (S:MS_Data G M)
variable (x:I B→ℝ)
local notation "R" => packet S x
local notation "N" => ground x
local notation "U" => Archive 4 S.bulk
local notation "τx" => spaceD G
abbrev part (t:ℝ): Law G:= tree parity (chi G t) (cub G) N
local notation "T" => part x
lemma mark_lead (K:TreeLine.Line G)(t:Clock ℝ)(w:Legs (Lane4 G))(hr:w.length=3):
    tree parity K (U 1 t) (R 0 t) w=tree parity K (cub G) N w:=
  tree_peak K (n:=2) (m:=3) (b:=false) (fun v _ hv=> bulk_first S t v (by omega)) (fun v _ he=>starts S x t v (by omega))
    (fun v _ hv=>bulk_first_height S t v hv) (upper0 S x t) w (by omega) (fun h=>Bool.noConfusion h)
lemma corner : Static (R 1-(T∘Prod.snd)) 3 4 false:= by
  let D : Reading G:= fun t=> tree parity (PlanetD G t.2) (cub G) N
  refine peel_static (D:=D) (polish S x 1) (sheared S x 1 3) (renew S x 1) ?_ ?_ ?_ (fun y t w _ _=> TreeView.tree_deriv ..)
  · exact fun t=> cub_p.chi (F:=cub G) (H:=N) (fun E _ _ w=> ((born x).2.1 E w (fun h=>Bool.noConfusion h)).smooth) t
  · exact ((shear_form (form1 (b:=true))).tree (shear_form ((born x).2.1))).cov 3
  intro y t w hc hr; have he:=time_derivative w (speed S x 1 (ray w)) hc y t
  have hx: recu τx 0 1 U R 1 (y,t) w=D (y,t) w:= by
    unfold recu; rw [tree_first,Pi.add_apply,cycle_height _ _ _ w false hc (fun v h hz=>level1 S x _ v h (by omega)),zero_add,mark_lead S x _ _ w hr]; rfl
  rw [hx] at he; exact he
abbrev prior : Reading G:= R 1 - (T∘Prod.snd)
local notation "QX" => prior S x (0,0)
lemma front (w:Legs (Lane4 G))(h:w.length=3): Tendsto (fun t:ℝ=> R 1 (0,t) w) atBot (𝓝 (QX w)):=
  static_prior (corner S x) _ _ (fun h=>Bool.noConfusion h) h (tree_dies ..)
lemma un3 (t:Clock ℝ)(w:Legs (Lane4 G))(hr:w.length=3) :
    natQ (R 1 t) w= -(tree parity (qLine G t.2) (cub G) N w):= by
  rw [identities S x]; unfold Ward recu; rw [tree_first,Pi.neg_apply,Pi.add_apply,
    cycle_height _ _ _ w false (fun h=>Bool.noConfusion h) (fun i hi hx=> level1 S x _ i hi (by omega)),zero_add,mark_lead S x _ t w hr]
lemma prior_closed (w:Legs (Lane4 G))(h:w.length=3) :
    natQ QX w= - tree parity (qAt G) (cub G) N w:= by
  apply tendsto_nhds_unique (charge_limit (A:=R 1) (t:=0) (D:=QX) (w:=w) (fun v a b=>front S x v (b.trans h)) (show Course false w from fun h=>Bool.noConfusion h))
  simp_rw [un3 S x _ w h]
  exact (tree_limit (L:=qAt G) (fun _=>cub G) (fun _=>N) ward_cold (fun _=>tendsto_const_nhds) (fun _=>tendsto_const_nhds) w).neg

structure Completion (F:Law G) : Prop where
  structure_k : F∈Lease G 4 3 0
  ward (w:Legs (Lane4 G)):w.length=3 → natQ F w= - tree parity (qAt G) (cub G) N w
lemma initial (F:Law G)(hF:Completion x F): Book.mask 3 QX=F:= by
  let X:=Book.mask 3 QX; obtain ⟨h,hn⟩:= hF
  have hx := (lease_one.mp h)
  have hp:X∈ Lease G 4 3 0:= lease_one.mpr ⟨?_,masked (r:=3) _ (corner S x) (0,0),mask_rank⟩
  · apply sub_eq_zero.mp; refine cubic_free ((Lease G 4 3 0).sub_mem hp h) ?_; funext w; change natQ (X-F) w=0
    by_cases he:w.length=3
    · rw [map_sub,Pi.sub_apply,show natQ X=Book.mask 3 (natQ QX) from (MS.Lifting.mask_raises id QX 3).symm,Book.enough _ (by simp [he]),prior_closed S x w he,hn w he]; simp
    have eq : mask 3 (X-F)=X-F:= by
      apply rank_hat (F:=X-F) (3:ℤ) |>.mp
      exact (rankMod _ _).sub (show rank 3 F from fun w hw => hx.2.2 w (fun h=>Bool.noConfusion h) (by rw [mod_int] at hw; omega))
    have hz: natQ (X-F)=mask 3 (natQ (X-F)):= (congr_arg natQ eq).symm.trans (MS.Lifting.mask_raises id (X-F) 3).symm
    exact (congr_fun hz w).trans (Book.strange _ (by omega))
  · refine solid_limit (fun t:ℝ=> Book.mask 3 (R 1 (0,t))) (fun t=>solid_level (MarkRows.solid S x 1 (0,t)) _) fun w=> ?_
    by_cases he:w.length=3
    · convert front S x w he using 1; · funext t; exact Book.enough _ (by exact_mod_cast he)
      rw [show X w=QX w from Book.enough _ (by exact_mod_cast he)]
    unfold X; simp_rw [Book.strange w (show (w.length:ℤ)≠3 from by exact_mod_cast he)]; exact tendsto_const_nhds
lemma live (F:Law G)(h:Completion x F)(s:Clock ℝ)(w:Legs (Lane4 G))(p:w.length=3):
   R 1 s w= F w+ T s.2 w:= by
  rw [←initial S x F h,Book.enough _ (by omega)]
  exact sub_eq_iff_eq_add.mp ((corner S x).same s.1 0 s.2 0 w (fun u=>Bool.noConfusion u) p)

local notation "Gk" => PlanetD G
local notation "Gx" => TreeLine.chi G
local notation "Hb" => ((2:ℂ)⁻¹)
abbrev folded (s:ℝ)(L:TreeLine.Line G):Law G:=
  tree parity L (cloud G s) N+ tree parity L (cub G) (T s)
abbrev lump (F:Law G) (s:ℝ):Law G:= tree parity (Gx s) (qua G) N + tree parity (Gx s) (cub G) F
abbrev charged (F:Law G) (s:ℝ):Law G:= lump x F s + Hb • folded x s (Gx s)
abbrev Xd (F:Law G)(s:ℝ):Law G:= tree parity (Gk s) (qua G) N + tree parity (Gk s) (cub G) F + folded x s (Gk s)
lemma alters (F:Law G)(w:Legs (Lane4 G))(s:ℝ): HasDerivAt (fun u:ℝ=>charged x F u w) (Xd x F s w) s:= by
  let a:= cub G; let P: ℝ→ Law G:=fun u=> cloud G u
  let Q: ℝ→ Law G:=fun u=> T u
  let A:=fun s (f g:Law G)=> Heat.boulevard parity (Gk s) f g
  let b:=fun s (f g:Law G)=> Heat.boulevard parity (Gx s) f g
  let wick := Hb • A s a a; let bit:= A s a N
  have hp: Zip P wick s:= fun w=> (tree_deriv s w a a).const_mul Hb
  have hq: Zip Q bit s:= fun w=> tree_deriv s w a N
  have tv (a:Law G): Zip (fun _=>a) 0 s:= fun w=> hasDerivAt_const ..
  have hz: A s (P s) N + A s a (Q s)= b s wick N+b s a bit:= by
    have h:= orbit_even_pair (K:=Gx s) (L:=Gk s) (F:=a) (H:=N) (chi_closed s)
      ((MS.Garment.Wick.cl_a G s) 0) (Halo.B₁_P G 0|>.sym) cub_parity (ground_symm x)
    unfold wick bit P cloud Q A b part; rw [←LinearMap.flip_apply, map_smul, ←LinearMap.flip_apply (Heat.boulevard parity (Gx s)),map_smul]; convert congr_arg ((Hb) • ·) h using 1 <;> (simp only [two_nsmul, smul_add, LinearMap.flip_apply, blvd ]; rw [←add_smul,show (Hb+Hb)=(1:ℂ) from by norm_num,one_smul])
  have H:= (tree_zip_chi s hp (tv N)).add (tree_zip_chi s (tv a) hq)
  have hx : Zip (fun u=> folded x u (Gx u)) ((2:ℂ) • folded x s (Gk s)) s:= by
    change Zip _ ((2:ℂ) • (A s (P s) N + A s a (Q s))) _
    convert H using 1
    · rfl
    rw [two_smul]; change _= A s (P s) N + b s wick N + b s (P s) 0 + (A s a (Q s)+ b s 0 (Q s)+ b s a bit); rw [show b s (P s) 0=0 from map_zero (Heat.boulevard parity (Gx s) (P s)), show b s 0 (Q s)=0 from map_zero ((Heat.boulevard parity (Gx s)).flip (Q s))]; rw (occs:=.pos [2]) [hz]; abel
  apply HasDerivAt.add (f:=fun u=> lump x F u w) ((tree_deriv s w (qua G) N).add (tree_deriv s w a F))
  have hq:=(hx w).const_mul Hb; change HasDerivAt _ (Hb*((2:ℂ)*_)) s at hq; rw [inv_mul_cancel_left₀ (show (2:ℂ)≠0 from by norm_num)] at hq; exact hq
private lemma tree_bounded {F H:Law G}{m n r:ℕ}{b:Bool}(ht: m+n≤r+2)(h:Upper true m F)(hc:Upper b n H)(K:TreeLine.Line G): Upper b r (tree parity K F H):= by
  intro w hQ hw; refine tree_height K F H _ _ hQ fun i j hi=> ?_
  by_cases he:i<m
  · exact Or.inr fun v p q=> hc _ p (by omega)
  exact Or.inl fun v p q=>h _ (fun _=>p) (by omega)
lemma last_source (F:Law G)(p:Completion x F)(t:Clock ℝ)(w:Legs (Lane4 G))(hr:w.length=4):
  recu τx 0 1 U R 2 t w=Xd x F t.2 w:=by
  unfold recu; rw [tree_second,Pi.add_apply,cycle_height _ _ _ w false (fun h=>Bool.noConfusion h) (fun i hi hx=> level2 S x _ i hi (by omega)),zero_add]
  let E:=qua G + cloud G t.2; let P:= F+T t.2
  have cup: Upper true 3 (cub G):= fun v _ hv=> bulk1_r _ _ (by rw [mod_int]; omega)
  have fit: Upper false 2 N:= fun v p hv=>(born x).2.2 v p (by omega)
  have up:Upper true 4 E:=by
      intro v p hv; unfold E; rw [Pi.add_apply,show qua G v=0 from bulk2_r 0 _ (by rw [mod_int];omega),zero_add,cloud,Pi.smul_apply,tree_bounded (r:=4) (by decide) cup cup _ v p hv,smul_zero]
      -- pole
  have hi:Upper false 3 P:=by
      intro v h hv; change F v+T t.2 v=0; have hx:= (lease_one.mp p.structure_k).2.2 v h (by omega); rw [hx,zero_add]; exact tree_bounded (by norm_num: 3+2 ≤ 3+2) cup fit _ v h hv
  have e (v)(h:Course true v)(hv:4≤v.length): U 2 t v= E v :=by
      rcases lt_or_eq_of_le hv with z|z; · exact (bulk_height S t v h z).trans (up v h z).symm
      exact BulkTop.pulse S t v h z.symm
  have q (v)(h:Course false v)(hv:3≤v.length): R 1 t v=P v:=by
      rcases lt_or_eq_of_le hv with z|z; · exact (level1 S x t v h z).trans (hi v h z).symm
      exact live S x F p t v z.symm
  rw [Pi.add_apply, tree_peak ((τx).meter t.2) (b:=false) (n:=2) (m:=4) e (H:=R 0 t) (Q:=N) (fun v _ h=> starts S x _ _ (by omega)) (bulk_height S t) (upper0 S x t) w (by omega) (fun h=>Bool.noConfusion h),tree_peak ((τx).meter t.2) (b:=false) (n:=3) (m:=3) (F:=U 1 t) (P:=cub G) (fun v _ h=> bulk_first S t v (by omega)) q (fun v _ hv=> bulk_first_height S _ _ hv) (level1 S x t) w (by omega) (fun h=>Bool.noConfusion h)]
  unfold E P Xd folded PlanetD; simp_rw [← blvd,map_add,LinearMap.add_apply,Pi.add_apply]; abel

lemma static_top (F:Law G)(h:Completion x F): Static (R 2-(charged x F∘Prod.snd)) 4 4 false:= by
  refine peel_static (D:=fun t w=> Xd x F t.2 w) (polish S x 2) (sheared S x 2 4) (renew S x 2) ?_ ?_ ?_ (fun _ t w _ _=> alters x F w t)
  · have pf: Polish F:= fun E _ _ w=> ((lease_one.mp h.structure_k).2.1 E w (fun h=>Bool.noConfusion h)).smooth
    have ph:Polish N:= fun E _ _ w=> ((born x).2.1 E w (fun h=>Bool.noConfusion h)).smooth
    exact fun t=>(Polish.add (qua_p.chi ph t) (cub_p.chi pf t)).add
      ((Polish.add (((cub_p.chi cub_p t).smul Hb).chi ph t) (cub_p.chi (cub_p.chi ph t) t)).smul Hb)
  · have hf:= shear_form (lease_one.mp h.structure_k).2.1
    have hg:= shear_form ((born x).2.1)
    have ht:=shear_form (form1 (G:=G) (b:=true)); refine (shear.add (K:=lump x F) ?_ ((shear.add (ht.tree ht|>.smul Hb|>.tree hg) (ht.tree (ht.tree hg))).smul Hb)).cov 4
    exact (shear.tree (shear_form form2) hg).add (ht.tree hf)
  intro y t w _ hr; exact (last_source S x F h (y,t) w hr) ▸ (time_derivative w (speed S x 2 (ray w)) (fun h=>Bool.noConfusion h) y t)

abbrev markTopLocal (F:Law G) : Law G:= (((R 2 - (charged x F ∘ Prod.snd)): Reading G) (0,0))
lemma evaluation (F:Law G)(h:Completion x F)(t:Clock ℝ)(w:Legs (Lane4 G))(hr:w.length=4): R 2 t w= markTopLocal S x F w+charged x F t.2 w := sub_eq_iff_eq_add.mp ((static_top S x F h).same t.1 0 t.2 0 w (fun h=>Bool.noConfusion h) hr)
end
end YM.SignedWilsonExpansion.MarkTop
