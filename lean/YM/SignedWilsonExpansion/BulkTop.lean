import YM.SignedWilsonExpansion.TreeView
set_option autoImplicit false
noncomputable section
namespace YM.SignedWilsonExpansion.BulkTop
open Function Filter Set Finset MeasureTheory
open MS MS.Rake MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Pearl MS.Landau MS.Landau.Detect MS.Plane.Domain MS.Plane.Wire
open MS.Land MS.Dock MS.Outlook MS.Emit MS.Motif MS.Book MS.Arts MS.Heat
open SignedWilsonExpansion HighScale HighRank TreeLine TreeView
open scoped Topology BigOperators ContDiff
variable {G:Gauge} {n:ℕ}

variable {b:Bool}
lemma strictr {i j:ℤ} {F H: Mield G n}(f:∀ l,Book.rank i (F l))(h:∀ l,Book.rank j (H l)) : Book.rank (i+j) (sume F H):=
  Rails.sum _ fun k _=> (f k).product (h k)
lemma jaw_r {i j:ℤ} {F H: Mield G n}(f:∀ l,Book.rank i (F l))(h:∀ l,Book.rank j (H l))(l:G.ColorIndex): Book.rank (i+j) (jaw G n F H l):=by
  rw [chew]; exact Rails.sum _ fun k _=> Rails.sum _ fun j _=> ((f k).product (h j)).smul _
lemma quill_r (i j:Arts.L n) (k:G.ColorIndex): Book.rank 2 (quill i j k):=
  jaw_r (i:=1) (j:=1) (fun _=> mon_leaf _) (fun _=> mon_leaf _) k -- check possible implicit
lemma bulk1_r (m:ℕ) : Book.rank 3 (B₁ G m):= by
  unfold B₁ top3 cape
  apply Rails.add
  · refine Rails.smul _ (Rails.sum _ (fun i _=> Rails.sum _ (fun j _=>?_ ))) -- args
    exact Rails.add (strictr (rank_α i j) (quill_r i j)) (strictr (quill_r i j) (rank_α i j))
  apply Rails.sum; rintro ⟨_|a,c⟩ _
  · have he : Book.rank 2 (Sc 1 G m c):= (jaw_r (i:=1) (j:=1) (F:=cwave m G) (H:=cwave m G) (fun _=>mon_leaf _) (fun _=>mon_leaf _) _).smul _
    exact ((mon_leaf _).product he).smul _
  exact ((mon_leaf _).product (jaw_r (F:=Motif.A m G a) (H:=cwave m G) (i:=1) (j:=1) (fun _=>mon_leaf _) (fun _=>mon_leaf _) _)).smul _
lemma bulk2_r (m:ℕ): Book.rank 4 (B₂ G m):= by
  unfold B₂ top4; exact (Rails.sum _ (fun i _=> Rails.sum _ (fun j _=> strictr (quill_r i j) (quill_r i j) )) ).smul _

local notation "Σb" => Branch G Axis
abbrev cub (G:Gauge): Law G:= B₁ G 0
abbrev qua (G:Gauge): Law G:= B₂ G 0
lemma form1 : Form (cub G) wfield 4 b := Halo.snTag (Halo.B₁_P G)
lemma form2 : Form (qua G) wfield 4 b := Halo.snTag (Halo.B₂_P G)
lemma pulseTwo : pulseX G 2=B₂ G:= by simp [pulseX, Literal.hiss,Motif.χ]
lemma cub_p : Polish (cub G):=fun E _ _ w=>(form1 (b:=false) E w (fun h=>Bool.noConfusion h)).smooth
lemma qua_p : Polish (qua G):=fun E _ _ w=>(form2 (b:=false) E w (fun h=>Bool.noConfusion h)).smooth
lemma cub_parity : Pure (field (parity (C:=G.ColorIndex) (A:=Axis))) false (cub G):= Rails.parity (h:=0) (v:=ghostNo ∘ Prod.fst) (fun i=> Native.ghostParity i.1) (Halo.B₁_P G 0|>.ghost)
-- limit L_f2
variable {B: MS.Local.Physical.Deck G}{M: Booked B} (S: MS_Data G M)
local notation "Up" => S.bulk
local notation "Hb" => ((2:ℂ)⁻¹)
local notation "F2" => bulkD S
abbrev cloud (G:Gauge)(t:ℝ): Law G:= Hb • tree parity (TreeLine.chi G t) (cub G) (cub G)
local notation "C2" => cloud G
lemma paid1 (simple:G.Simple)(t:Clock ℝ)(w:Legs (Lane4 G))(hr:0<w.length)(hw:net w=0): Archive 4 S.bulk 1 t w=cub G w:= by
  rcases lt_or_eq_of_le (show 1≤w.length from hr) with h|h -- parse 0< ambiguous
  · exact bulk_first S t w (by omega)
  obtain ⟨i,rfl⟩:= List.length_eq_one_iff.mp h.symm
  rw [bulk_single S 1 t i hw simple]; exact (bulk1_r (G:=G) 0 [i] (by rw [mod_int]; simp)).symm
-- rank4 tree peak doesn't require off-shell
lemma highest (K:TreeLine.Line G)(t:Clock ℝ)(w:Legs (Lane4 G))(hw:net w=0)(hr:w.length=4):
    tree parity K (Archive 4 S.bulk 1 t) (Archive 4 S.bulk 1 t) w=tree parity K (cub G) (cub G) w:= by
  apply tree_peak (n:=3) (m:=3) (b:=true) K (fun v _ he=> bulk_first S t v (by omega)) (fun v _ he=> bulk_first S t v (by omega))
    (fun v _ hv=>bulk_first_height S t v hv) (fun v _ hv=>bulk_first_height S t v hv) w (by omega) (fun _=>hw)
lemma corner : Static ((F2-(C2 ∘ Prod.snd)): Reading G) 4 4 true := by
  let D : Reading G:= fun t=> Hb • tree parity (PlanetD G t.2) (cub G) (cub G)
  let hv:= bulkView S 2 (by omega)
  refine peel_static (D:=D) ?_ (fun _ _ _ _ _ _=> congr_fun (Port.Bx4 hv.host) _) (plant hv.host) ?_ ?_ ?_ ?_
  · intro t E _ _ w; exact Outlook.hair hv.host (n:=0) w
  · exact fun t=>(cub_p.chi cub_p t).smul Hb
  · exact ((shear_form (form1 (b:=true))).tree (shear_form (form1 (b:=true))) |>.smul Hb).cov 4
  · intro y t w hc hr
    let u:=(y,t)
    have he:= time_derivative w (hv.flow w (fun _=>by omega)) hc y t
    simp only [Pi.add_apply] at he
    have E:cycle (spaceD G|>.meter t) (spaceD G|>.measure) (F2 u) w=0:= cycle_height _ _ _ w true hc fun i hi hx=> bulk_height S u i hi (by omega)
    change HasDerivAt _ (cycle (spaceD G|>.meter t) (spaceD G|>.measure) (F2 u) w + ((spaceD G).using_tree 2 1 Hb (fun i=> Archive 4 S.bulk i u) (fun i=> Archive 4 S.bulk i u) u.2) w) t at he
    rw [E,zero_add,tree_two,Pi.smul_apply, highest S _ u w (hc rfl) hr] at he
    exact he
  intro y t w hc hr; exact (TreeView.tree_deriv ..).const_mul Hb

lemma un4 (t:ℝ)(w:Legs (Lane4 G))(h:Course true w)(hw:w.length=4):
    natQ (F2 (0,t)) w= -(Hb*tree parity (qLine G t) (cub G) (cub G) w):= by
  unfold natQ; rw [(Outlook.dock S.bulkOK Motif.wisdom).master.qfm 2 (0,t) w (by norm_num) (fun _=>by omega) h]; unfold Ward recu; rw [tree_two,Pi.neg_apply,Pi.add_apply,Pi.smul_apply]
  rw [cycle_height _ _ _ w true h (fun i hi hx=> bulk_height S _ i hi (by omega)),zero_add,highest S _ _ w (h rfl) hw]; rfl
lemma bare4 (w:Legs (Lane4 G))(h:Course true w) : natQ (qua G) w= -(Hb*tree parity (qAt G) (cub G) (cub G) w):= by
  have H:= (Motif.wisdom (G:=G)) 2 0 w h
  unfold BasisC at H
  rw [Convolve.paired, show antidiagonal 2={(0,2),(2,0),(1,1)} from by decide,
    sum_insert (by decide),sum_insert (by decide),sum_singleton] at H
  simp only [Up0, map_zero,LinearMap.zero_apply, zero_add,Halo.pulse1,pulseTwo] at H
  exact eq_neg_of_add_eq_zero_left H

lemma went (w:Legs (Lane4 G))(h:Course true w)(hw:w.length=4): Tendsto (fun t:ℝ=> F2 (0,t) w) atBot (𝓝 (((F2-(C2 ∘ Prod.snd)): Reading G) (0,0) w)):= by
  apply static_prior (corner S) 0 w h hw
  simp only [Function.comp_apply,cloud,Pi.smul_apply,smul_eq_mul]; simpa only [mul_zero] using (tree_dies (cub G) _ w).const_mul Hb
lemma slope_closed (w:Legs (Lane4 G))(h:Course true w)(hr:w.length=4) :
    natQ (((F2-(C2 ∘ Prod.snd)): Reading G) (0,0)-qua G) w=0:= by
  let f:= ((F2-(C2 ∘ Prod.snd)): Reading G) (0,0); rw [show natQ (f-qua G) w=natQ f w-natQ (qua G) w from congr_fun (map_sub natQ f (qua G)) w]
  have z:= charge_limit (A:=F2) (t:=0) (D:=f) (w:=w) (fun v a b=>went S v a (b.trans hr)) h
  refine sub_eq_zero.mpr (tendsto_nhds_unique z ?_)
  rw [bare4 w h]; simp_rw [un4 S _ w h hr]
  exact ((tree_limit (L:=qAt G) (fun _=>cub G) (fun _=>cub G) ward_cold (fun _=>tendsto_const_nhds) (fun _=>tendsto_const_nhds) w).const_mul Hb).neg
lemma noGhost (w:Legs (Lane4 G))(h:Course true w)(he:w.length=4)(hc:fieldDim ghostNo w≠0):
    (((F2-(C2 ∘ Prod.snd)): Reading G) (0,0)-qua G) w=0 := by
  have H(s:ℝ):F2 (0,s) w=0:= (Outlook.dock S.bulkOK Motif.wisdom).master.trueC 2 (0,s)|>.ghost w h hc
  have hm:= went S w h he; simp_rw [H] at hm
  have he' : B₂ G 0 w=0:= (Halo.B₂_P G 0).ghost w hc
  rw [Pi.sub_apply, tendsto_nhds_unique hm tendsto_const_nhds, show qua G w=0 from he',sub_zero]

open MS.Landau.Detect.Mark
lemma initial_match (w:Legs (Lane4 G))(h:Course true w)(hr:w.length=4):
    ((F2-(C2 ∘ Prod.snd)): Reading G) (0,0) w=qua G w:= by
  have ht: Static (((F2-(C2 ∘ Prod.snd)): Reading G)-(fun _=>qua G)) 4 4 true:=by
    let K:= fun _ :Clock ℝ=> qua G; have m:=corner S; refine ⟨?_,covariant_sub m.scales ?_,?_,?_⟩
    · intro y t l w hw hr; exact congr_arg (·-qua G w) (m.time y t l w hw hr)
    · exact (shear_form (form2 (G:=G) (b:=true))).cov 4
    · intro E _ _ w he hk t; exact (m.smooth E w he hk t).sub (qua_p E w)
    intro t w hw hr; exact MS.Logarithm.Ready.sub (m.size t w hw hr) (MS.Logarithm.Ready.const (fieldVal (qua G) (ray w)))
  let F:= fun s:Clock ℝ=> ((F2-(C2 ∘ Prod.snd)): Reading G) s-qua G
  apply sub_eq_zero.mp
  change F (0,0) w=0
  rcases lt_or_ge 4 (fieldDim wfield w) with ht'|hr'
  · exact ht.over 0 0 w h hr ht'
  have hh:=length_pay w
  have cost:fieldDim wfield w=4:= by omega
  by_cases e:fieldDim ghostNo w=0
  swap; · exact noGhost S w h hr e
  have all:=(pay_eq w (by rw [hr,cost]; rfl))
  have hp:∀i∈w,∃ a k p,i=W a k p:= fun i hi=> cost_vec i (all i hi) (no_eq w all e i hi)
  obtain ⟨x,y,z,t,rfl⟩:= List.length_eq_four.mp hr
  rw [List.forall_mem_cons,List.forall_mem_cons,List.forall_mem_cons,List.forall_mem_cons] at hp
  obtain ⟨⟨a,i,p,rfl⟩,⟨b,j,q,rfl⟩,⟨c,k,r,rfl⟩,⟨d,l,s,rfl⟩,_⟩:=hp
  let v:=spike a
  have e : ∀ m:Axis, F (0,0) [C i v,U m j (-v),W c k 0,W d l 0]=0:= fun m=> ht.over 0 0 _ (fun _=>by simp [net,C,W,qnote,U]) rfl (by norm_num [fieldDim,wfield,dim,C,W,qnote,U])
  have V : natQ (F (0,0)) [C i v,W b j (-v), W c k 0,W d l 0]=0:= slope_closed S _ (fun _=>by simp [net,C,W,qnote]) rfl
  rw [qGhost, qAA,qAA,qAA,q0] at V
  simp_rw [at_D,e] at V
  have hv x y: precision x y (0:Momentum Axis)=0:=by unfold precision delta Momentum.sq; simp
  simp only [hv, Complex.ofReal_zero,neg_zero,zero_mul,mul_zero,Finset.sum_const_zero,add_zero,sub_zero] at V
  rw [Finset.sum_eq_single a (fun j _ hj=>by simp [v,hj]) (by simp)] at V
  exact (flat_spins_static (f:=F) (0,0) ht _ _ h (show Course true [W a i v,W b j (-v),W c k 0,W d l 0] from fun _=>by simp [net,W,qnote]) hr cost rfl).trans (by simpa [v] using V)

theorem pulse (s:Clock ℝ)(w:Legs (Lane4 G))(h:Course true w)(hr:w.length=4):
    Archive 4 S.bulk 2 s w = qua G w + Hb*tree parity (chi G s.2) (cub G) (cub G) w := by
  have ht:= (corner S).same s.1 0 s.2 0 w h hr
  rw [initial_match S w h hr] at ht
  exact sub_eq_iff_eq_add.mp ht
end YM.SignedWilsonExpansion.BulkTop
