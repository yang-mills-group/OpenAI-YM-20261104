import YM.FVA2.Generator.Bottom
/-!
# Scaling the physical live at the finite inversion regulator. Annular reposition

(a) exact transformation law for every order of every mark at all finite spacings, root kept
(b) diagonal projection of the order-one `harvest` difference even at nonunit dilation given
exactly by annular differences at appropriately normalized spacings; leading field-sector inversion
not needed. Note use of `forge` from XSpace here; commutes REAL not complex.
(c) passes actually to zero before nondiagonal powers are budgeted by NormStab.

Phase-independent. $Y$ any realization of the Wilson presentation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Generator.Penny
open Function Set Filter XSpace XSpace.Trace XSpace.Lows XSpace.Mu XSpace.Chart2 XSpace.Furlough XSpace.Future
open XSpace.Structure1 XSpace.Cirrus XSpace.Normalize
open Lattice FVA2.Scale FVA2.Scale.Level FVA2.Scale.Facets PowerSeries Maxwell
open scoped Topology BigOperators Classical
variable {G:Gauge}(s:ℝ){d n k:ℕ}
lemma token (j:E d): Extent.token s j.val * Extent.token ( -s ) j.val=1:= by
   unfold Extent.token; rw [ ← mul_pow,neg_neg, ← Complex.ofReal_mul, ← Real.exp_add,neg_add_cancel,Real.exp_zero,Complex.ofReal_one,one_pow ]
abbrev Wrt (s:ℝ)(d:ℕ){n:ℕ}(p:Tags G d n):= Dial d s ∘ p
lemma partDial (a:E d)(x:Sec G d): part d a ( Dial d s x )= Extent.token s a • part d a x:= by
    unfold Level.Dial; rw [LinearMap.sum_apply,map_sum]; simp only [LinearMap.smul_apply,map_smul]; rw [Finset.sum_eq_single a]; change _ • part d a.val (en (within a) _)=_; rw [part_same]; intro j _ hj; rw [show part d a (Level.proj j x)=0 from part_other _ (fun h=> hj (Fin.ext h.symm)) _ , smul_zero ]; exact within j; simp
lemma projectDial (a:E d)(x:Sec G d): Level.proj a ( Dial d s x )= Extent.token s a • proj a x:= by rw [ Level.proj,LinearMap.comp_apply,partDial,map_smul]; rfl
lemma diag_version (A:FieldEnd G d): diag (turner s A)=diag A:= by ext1 p; rw [ ← Level.all p,map_sum,map_sum ]; apply Finset.sum_congr rfl; intro i _; rw [ diagonals, diagonals ]; change Level.proj i (Dial d (-s) (A (Dial d s (proj i p)))) =_; rw [taken,map_smul,map_smul,map_smul, projectDial, smul_smul, token, one_smul]
lemma update_w (T:FieldEnd G d)(p:Tags G d n)(i:Fin n) : update (Wrt s d p) i (T ((Wrt s d p) i))= Wrt s d (update p i (turner s T (p i))):= by
    funext j; by_cases h:j=i; subst j; rw [update_self]; unfold Wrt; dsimp only [Function.comp_apply]; rw [update_self]; exact LinearMap.congr_fun (Level.transfer s T) (p i)
    rw [update_of_ne h]; unfold Wrt; dsimp only [Function.comp_apply]; rw [update_of_ne h]
lemma lotW (X Y:Point G d n)(H:∀ p,X (Wrt s d p)=Y p)(F:FieldEnd G d)(p:Tags G d n): lot X F (Wrt s d p)=lot Y (turner s F) p:= by rw [lots,lots]; simp_rw [ update_w, H ]
section increment
variable (W:Initialize G)
def wrist (s:ℝ) := Real.exp (-s)
private lemma vital (p:Mesh)(v: (Extent.march s p).Sites)(f:HP G d) : W.atSite (Extent.march s p) d v (Extent.token s d • f)= W.atSite p d v f:= by
    let x:=((p.spacing:ℂ)^d)⁻¹; let a:=Extent.token s d; have he: a≠0:=Level.rise_p s _; rw [map_smul]; unfold Initialize.atSite; simp only [LinearMap.smul_apply]; rw [show (↑(Extent.march s p).spacing:ℂ)^d=a*(p.spacing:ℂ)^d from (by unfold a Extent.token Extent.march; dsimp only; push_cast; rw [mul_pow])]; change a • ((_)⁻¹ • _)= x • _; rw [mul_inv,smul_smul,← mul_assoc,mul_inv_cancel₀ (by exact he),one_mul]; rfl
lemma moves (p:Tags G d n) (v:Sample n) : live W d (Extent.reaches s v) k (Wrt s d p)=live W d v k p:= by
    unfold live; rw [lite,lite]; apply Finset.sum_congr rfl; intro j _; simp_rw [Wrt,Function.comp_apply,partDial]; rw [Initialize.atTuple_eq, Initialize.atTuple_eq]; apply congr_arg; change Bare.normalized (W.tree v.F.p) G _= Bare.normalized (W.tree v.F.p) G _; apply congr_arg; exact Finset.prod_congr rfl fun i _=> vital s W v.F _ _
-- increment frame in orientation
private abbrev Ch (G:Gauge)(d:ℕ):= ↥( Normalize.Change G d )
variable (χ:Shade.Cut) (d:ℕ)
private abbrev Rσ (s a:ℝ):= (harvest W χ d (wrist s*a))
def acted (s:ℝ)(A: Ch G d) : Ch G d:= ⟨turner s A.val,turn_change s A.val A.property⟩ -- params d explicit?
def going (s:ℝ)(p:ℝ): Ch G d:= acted ( G:=G ) d s ( harvest W χ d (wrist s*p) )-harvest W χ d p
lemma bon (v:Sample n)(p:Tags G d n): fallRecords W d χ v p - fallRecords W d χ (Extent.reaches s v) (Wrt s d p)= lot (live W d v 0) (going W χ d s v.F.spacing).val p:= by
    simp only [fallRecords, records,sub_apply, going ]; rw [moves,lotW s _ (live W d v 0) (fun p=>moves s W p v)]; let f:= lot (live W d v 0); let x:= live W d v 1 p; let u:=turner s (harvest W χ d (wrist s*v.F.spacing)).val; let w:=(harvest W χ d v.F.spacing).val; change (x-f w p) - (x-f u p)= f (u-w) p; rw [show f (u-w)= _ from (map_sub f u w),_root_.sub_apply]; abel -- orientation
end increment
-- diagonal bill.evaluation-cost before NormStab. Projection to compatible horizons.
private lemma on_gates (a:E d)(t:ℂ)(p: Sec G d) : Normalize.part d a (gates t d p)=t^a.val • part d a p:= by
    unfold gates; rw [ LinearMap.sum_apply,map_sum ]; simp only [LinearMap.smul_apply, LinearMap.comp_apply,map_smul]; rw [Finset.sum_eq_single a,part_same]; intro i _ hi; rw [ part_other _ (fun h=>hi (Fin.ext h.symm)),smul_zero ]; simp
private lemma vertical {i:E d}(W:Initialize G)(χ:Shade.Cut)(t:ℝ)(h:0<t)(p:Sec G d): diag (ready W χ t d) (proj i p)= proj i ( up (within i) (repair W χ i.val t (part d i p))) := by
    rw [ diagonals ]; let f:=part d i p; change proj i (ready W χ t d (en (within i) f)) = _; rw [ready_one]; unfold Level.proj; rw [ LinearMap.comp_apply,LinearMap.comp_apply,part_up, part_up, classFee, LinearMap.smul_apply,LinearMap.comp_apply,map_smul, on_gates (d:=i.val) ⟨i.val,by omega⟩, smul_smul ]; change en (within i) ((((↑t:ℂ)⁻¹)^_*(↑t:ℂ)^_) • _) = _; rw [← mul_pow,inv_mul_cancel₀ (by exact_mod_cast h.ne'), one_pow,one_smul]
private lemma twisting (t:Signed)(p:Sec G d)(i:E d): τ t d (proj i p)=proj i (τ t d p):= (Level.orient ..).symm
private lemma pivot (X:FieldEnd G d)(t:Signed): diag (spiral t d X) = spiral t d (diag X):= by ext1 p; rw [← Level.all p,map_sum,map_sum]; apply Finset.sum_congr rfl; intro j _; rw [ diagonals, spirals,spirals,twisting, Level.diagonals, twisting] -- RHS focus
private lemma real (X:FieldEnd G d): diag (matR d X)= matR d (diag X) := by
    ext1 p; rw [ ← Level.all p, map_sum,map_sum ]; apply Finset.sum_congr rfl; intro j _; rw [ diagonals,rsa,rsa, ← Level.real, diagonals, ← Level.real] -- check
lemma charge (X:FieldEnd G d): diag (forge X)=forge (diag X):= by
    rw [Structure1.axes,Structure1.axes]; simp_rw [_root_.map_smul,map_sum,pivot,mid,map_smul,map_add,Penny.real] -- note order unfold mid? semilinear mismatch
section tend
variable {ι:Type}{L:Filter ι}[L.IsCountablyGenerated]{a:ι→ℝ}(S:Tendsto a L (𝓝 0))(h:∀ᶠ i in L, 0<a i) (W:Initialize G)(χ:Shade.Cut)(d:ℕ)
include S h
private lemma repeal (j:E d)(p:Sec G d): By ℂ L (fun i=>diag (ready W χ (wrist s*a i) d-ready W χ (a i) d) (proj j p)) 0:= by
    intro Q; let r:=wrist s; have hr:0<r:= Real.exp_pos _; let E':= Level.proj j ∘ₗ up (G:=G) (within j); obtain he:= Seals.Bottom.harvest S h χ r hr (Normalize.part d j.val p) W ( Q ∘ₗ E' ); simp_rw [map_sub,map_zero] at *; apply he.congr'; filter_upwards [h] with i hi; rw [show diag (ready W χ (wrist s*a i) d-ready W χ (a i) d)=_ from (map_sub (Level.diag (G:=G) (d:=d)) _ _),LinearMap.sub_apply,map_sub,vertical W χ _ (mul_pos (show 0<wrist s from hr) hi),vertical W χ _ hi]
    rfl
private theorem pointer : By ℂ L (fun i=>diag (ready W χ (wrist s*a i) d-ready W χ (a i) d)) 0:= by
    let K:= Sec G d × Module.Dual ℂ ( Sec G d ); let Y(t:K): Module.Dual ℂ (FieldEnd G d):= t.2 ∘ₗ LinearMap.applyₗ (R:=ℂ) t.1 -- name
    let b:=Module.finBasis ℂ (Sec G d); apply redeemBy Y; · intro k hk; ext1 i; apply b.equivFun.injective; rw [LinearMap.zero_apply,map_zero]; exact funext fun j=>hk ((i,b.coord j):K)
    intro t; obtain ⟨p,f⟩:=t; let c(i):=diag (ready W χ (wrist s * a i) d - ready W χ (a i) d); rw [map_zero]; change Tendsto (fun i=> f (c i p)) L _; rw [← Level.all p]; simp_rw [map_sum]; obtain he:=tendsto_finsetSum (x:=L) Finset.univ (fun j _=> repeal s S h W χ d j p f); simpa only [map_zero, Finset.sum_const_zero ] using he
omit S h [L.IsCountablyGenerated] in
private lemma bar (f:ι→FieldEnd G d)(H:By ℂ L f 0): By ℂ L (fun i=>mid (f i)) 0:=by
    intro V; let P : Module.Dual ℂ (FieldEnd G d):= { toFun:= fun t=>star ( V ( matR d t ) ), map_add' :=by intros; rw [map_add,map_add,star_add], map_smul' :=by intros; rw [(matR d).map_smulₛₗ,map_smul]; simp }
    obtain he := ( (H V).add ( ( H P ).star ) ).const_mul ((2:ℂ)⁻¹); simp_rw [map_zero,star_zero, add_zero,mul_zero] at he; rw [map_zero]; apply he.congr; intro i; unfold mid; rw [map_smul,map_add]; unfold P; simp
omit S h [L.IsCountablyGenerated] in
private lemma surfeit (f:ι→FieldEnd G d)(H:By ℂ L f 0): By ℂ L (fun i=> forge (f i)) 0:= by
    have hv:=bar d f H; intro X; rw [map_zero]; obtain he:= ( tendsto_finsetSum (x:=L) Finset.univ (fun i _=> hv (X ∘ₗ spiral i d ) ) ).const_mul (R Signed)⁻¹; simp_rw [ map_zero, Finset.sum_const_zero,mul_zero ] at he; refine he.congr fun i=>?_ ; dsimp only; rw [Structure1.axes,map_smul,map_sum]; rfl
-- TRUE pre-norm bound on diagonal
set_option backward.isDefEq.respectTransparency false in
lemma firstFare : By ℂ L (fun i=> diag (going W χ d s (a i)).val ) 0:= by
    let t(i):= diag ( ready W χ (wrist s*a i) d - ready W χ (a i) d ); have hp(i) : diag (going W χ d s (a i)).val = forge (t i):= by
       unfold going acted harvest; dsimp only [Submodule.coe_sub]; change diag (turner s (forge (ready W χ (wrist s*a i) d))-forge (ready W χ (a i) d))= _; rw [_root_.map_sub (Level.diag (G:=G) (d:=d)), diag_version, ← map_sub,show ∀ A B:FieldEnd G d, forge A-forge B=forge (A-B) from ?_,charge]
       intro a b; rw [Structure1.axes,Structure1.axes,Structure1.axes,show mid (a-b)= mid a-mid b from ?_] -- need after axes
       <;> try (simp_rw [show ∀ i:Signed, spiral i d (mid a - mid b)=_ from fun i=> map_sub (spiral i d) _ _, Finset.sum_sub_distrib, smul_sub])
       unfold mid; rw [show matR d (a-b)=_ from map_sub (matR d) a b,sub_add_sub_comm a b (matR d a) (matR d b)]; exact smul_sub _ _ _ --]
    simp_rw [hp]; apply surfeit d t ( pointer s S h W χ d )
end tend
end YM.FVA2.Generator.Penny
