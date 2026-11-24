import YM.Contacts.Barrage.Jets
/-! The private tree hike extends *on the cover*, no monodromy discontinuity beyond the block ratio. Use for hypercubic epochs. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Contacts.Barrage.Slope
open Function Set Finset Filter RG Wilson Lattice Precision Exterior Push.AbsoluteSums Extra.Iteration
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F08
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent Draw PhysicalNext.RankCovariance
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{s η:ℝ≥0}{b:ℝ}{P: Patch}{B H:Bed}{m f L : Side}{S: StepData m f}{R: Spine.voyage S.patch.L}
private def dance (z:Cover) : Lattice.Walk := if _h : z=0 then [] else steer z :: dance (z+(steer z).vec)
termination_by Laurent.size z
decreasing_by apply Larch.rises _ _h
local notation "T" => (Larch.planting S.ratio S.patch.odd_side)
private lemma zero_site (P:Site m): lift P=0 ↔ P=0 := ⟨fun h=>by rw [← wrap_lift P,h,map_zero], fun h=> h.symm ▸ funext fun i=> ZMod.valMinAbs_zero m.val⟩
private lemma beats (x:Site f) : (T).hike x = dance (lift (S.ratio.residue x)) := by
   generalize hx: (T).height x=n
   induction n using Nat.strongRecOn generalizing x with| _ n ih=>
   rw [Forest.hike, dance]; by_cases he: leaf S.ratio x; swap; · rw [dif_neg he,dif_pos (by rw [fallen] at he; apply (zero_site _).2; tauto)]
   rw [dif_pos he,dif_neg (by rw [zero_site]; exact (fallen _).mp he)]; let z:=lift (S.ratio.residue x); let y:= x+((T).up x).vec; congr 1; rw [ih ((T).height y) (hx ▸ ((T).rise x he)) y rfl]; apply congr_arg; apply (S.ratio.internal S.patch.odd_side (Larch.unable z (fun k=> (fallen _|>.mp he) ((zero_site _).1 k)) _ (S.ratio.half_box S.patch.odd_side _))).1
private def lines (P:Patch) : Row (Co P.L (TypeFace 0)) (Co P.L (TypeFace 1)):= fun i=> Draw.path P.L (lift i.1) (dance (lift i.1)) - rootRow P vac
private lemma root_left (P:Patch): Ready (rootRow P vac):= by
   intro i s; obtain ⟨k,h,H⟩:= ready_rootRow P s; exact ⟨k,h,H vac i⟩
private theorem line_paid (P:Patch)(s:ℝ≥0): ∃ C≥(0:ℝ),(lines P).strip s C:= ready_strip (fun _=> (path_ready _ _).sub (root_left P)) _
def wave (R: Spine.voyage P.L): Row (Co P.L (TypeFace 0)) (TypeFace 1):= composeRows (lines P) R
-- compare all m periods. No choices of paths supplied per epoch
lemma halt (g:Ratio m f)(x:Site f): wrap f (lift (g.residue x))+g.embed (g.parent x)=x:= by
   rw [add_comm]; exact g.unpack_at x
lemma projects {R: Spine.voyage S.patch.L}(h:R.strip s b): installed S.ratio (wave R)= Precision.straighten S T (installed S.ratio R):= by
   let p:= S.ratio; let L:= lines S.patch; let e:= splitCo p (TypeFace 0); let t:= splitCo p (TypeFace 1); let J:= (L.acts m).submatrix e t; let K:=installed p R; have he:= (line_paid S.patch s).choose_spec.2; have ht: installed S.ratio (wave R)= J*K:= by
      unfold wave installed; erw [acts_compose s.property he h]; exact (Matrix.submatrix_mul_equiv _ _ _ t _).symm
   have hs(v:Body 0 f)(w:form 1 f): (J*ᵥ w) v=integralLink v.1 ((T).hike v.1) w - (fixRoot S *ᵥ w) (p.parent v.1,vac):= by
      let C:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Body 0 f=>ℝ) v; let P:= LinearMap.proj (R:=ℝ) (φ:=fun _ : Body 0 m=>ℝ) (p.parent v.1,vac); let A:=integralLink v.1 ((T).hike v.1) - P.comp (fixRoot S).mulVecLin; let M:= C.toLinearMap.comp J.mulVecLin; change M w=A w; congr 1; apply (Pi.basisFun ℝ _).ext; intro i; rw [Pi.basisFun_apply];
      change (J *ᵥ Pi.single i 1) v= _ - (fixRoot S *ᵥ Pi.single i 1) (p.parent v.1,vac); simp only [Matrix.mulVec_single_one]; unfold Matrix.col J e; erw [block_root, Matrix.transpose_apply,Matrix.transpose_apply, submatrix_apply, submatrix_apply, split_co]; change spot p (lines _ _) (p.parent v.1) i= _ - spot p (rootRow S.patch vac) (p.parent v.1) i; unfold lines; erw [spot_sub (g:=S.ratio) (p.parent v.1) i (path_ready _ _) (root_left S.patch), spot_path,halt, beats]; rfl
   apply Matrix.ext_iff_mulVec.mpr; intro v; rw [ht,← mulVec_mulVec]; exact funext fun i=> (hs i (K*ᵥ v)).trans (books ..).symm
open Origin
def lift0 (G:Gauge) (V:Cross L (TypeFace 0) (TypeFace 1)): Cross L (Loc G 0) (Dye G):= fun x y v=> if x.2.2=y.2 then V (x.1,x.2.1) y.1 v else 0
lemma life (h:Row.strip V s a)(hc:0≤a): (lift0 (L:=L) G V).strip s a:= by intro i j; unfold lift0; split; apply h; simpa [Width] using budget_loosen (budget_zero (α:=Cover)) hc
lemma lifted (R:Cross S.ratio.count (TypeFace 0) (TypeFace 1)): installed S.ratio (lift0 G R)=tensor G (installed S.ratio R):= by ext ⟨i,a,b⟩ ⟨j,x,y⟩; by_cases h:b=y <;> simp [installed,Row.acts,split_co,lift0,h,tensor]
def nest (P:Patch)(G:Gauge)(R:Spine.voyage P.L): Cross P.L (Candles G) (Dye G):= fun a=>Sum.elim (fun i b=>scaleRows (-1) (lift0 G (wave R)) (a.1,i) b) (fun i=>bleed G R (a.1,i)) a.2
def spanned (P:Patch)(s:ℝ≥0)(b:ℝ):= b+(Fintype.card (Co P.L (TypeFace 1)):ℝ)*((line_paid P s).choose*b)
lemma spanned_positive (h:0≤b): 0≤spanned P s b:= by have hL:=(line_paid P s).choose_spec.1; unfold spanned; positivity
lemma succeeds {R:Spine.voyage P.L} (h:R.strip s b) (ht:η≤ s) (hv:0≤b): (nest P G R).strip η (spanned P s b):= by
   let z:ℝ:= Fintype.card (Co P.L (TypeFace 1))*((line_paid P s).choose*b); have hz : 0≤z:=by have h':=(line_paid P s).choose_spec.1; unfold z; positivity
   have h': (scaleRows (-1) (lift0 G (wave R))).strip s z:= by simpa only [norm_neg,norm_one,one_mul] using strip_scale (life (G:=G) (V:=wave R) (strip_compose s.property (line_paid P s).choose_spec.2 h) hz) (-1:ℝ)
   rintro ⟨x,u|v⟩ b; exact ((h' _ b)).mono (by exact_mod_cast ht) (le_add_of_nonneg_left hv); exact (bleed_strip (G:=G) h hv _ b).mono (by exact_mod_cast ht) (le_add_of_nonneg_right hz)
local notation "F" => (Candles G)
private lemma hot_row (x:Site f)(i: Loc G 1) (w:Link G m): (installed S.ratio (nest S.patch G R)*ᵥ w) (x,Sum.inr i)= (installed S.ratio (bleed G R)*ᵥ w) (x,i):= rfl
private lemma cold_row (x:Site f)(i:Loc G 0)(w:Link G m): (installed S.ratio (nest S.patch G R)*ᵥ w) (x,Sum.inl i)= -(installed S.ratio (lift0 G (wave R))*ᵥ w) (x,i):= by
   change (installed S.ratio (scaleRows (-1) (lift0 G (wave (P:=S.patch) R)))*ᵥ w) (x,i)= _; rw [show installed S.ratio (scaleRows (-1) _) = - installed S.ratio (lift0 G (wave R)) from ?_,Matrix.neg_mulVec]; rfl; unfold installed; erw [acts_scale]; simp; rfl
lemma link_nest (x: Link G m): bundleLink (installed S.ratio (nest S.patch G R)*ᵥ x)= installed S.ratio (bleed G R)*ᵥ x:= by funext ⟨i,j⟩; exact hot_row i j x
lemma forestDrag (x: Link G m)(h:R.strip s b): fderiv ℝ (dragged G f) 0 (installed S.ratio (nest S.patch G R)*ᵥ x)= tensor G (extracted S T (installed S.ratio R))*ᵥ x:= by
   let y:= installed S.ratio (nest S.patch G R)*ᵥ x; let B:= wave R; let K:= lift0 G B; let L:= installed S.ratio (bleed G R); let u:= installed S.ratio K*ᵥ x; have hv : siteMap ℝ y= -u := funext fun i=> cold_row i.1 i.2 x;
   change _= tensor G _*ᵥ _; rw [interpolate, (show restMap ℝ y=L*ᵥ x from link_nest x),hv, map_neg,sub_neg_eq_add]; unfold u L K B; erw [bleeding, lifted (S:=S),Slope.projects (S:=S) h]; rw [extracted,promote_sum, promote_prod,Matrix.add_mulVec,← Matrix.mulVec_mulVec]; congr 1; -- gradient
   let z:= tensor G (straighten S T (installed S.ratio R))*ᵥ x; funext ⟨i,a,v⟩; change gradientA G f z _=_; obtain ⟨j,rfl⟩:= axisEquiv.surjective a; rw [coord_map]; change z (_,vac,v)-z _= (tensor G (d 0 f)*ᵥ z) _; rw [ show (tensor G (d 0 f)*ᵥ z) (i,coord j,v) = _ from congr_fun (component_mul (d 0 f) z v) (i,coord j), d_sites]; congr 3; exact congr_arg (fun b=> i+step b) (axisEquiv.symm_apply_apply j)
end YM.Contacts.Barrage.Slope
