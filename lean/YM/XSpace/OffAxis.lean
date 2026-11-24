import YM.XSpace.Furniture
import YM.XSpace.NormStab
/-!
# Odd field ambiguity lemma, does not need the H preservation thanks to parity

This helps on orientation-sensitive diagnostics. Certifies one may compare to even unbounded
pre-H-real subtraction charges, *provided they actually produce convergent answers*. At all finite
horizons with these hypotheses. (We only use first-order proof as of now.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.AxesTangent
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick Normalize Sample Structure1
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {d n:ℕ}
def Respects (T:FieldEnd G d) := ∀ p:Sec G d,reel d (T p)=T (reel d p)
def KillsFour (T:FieldEnd G d) := ∀ p: Sec G d,p.val∈ shellSector G 4 → T p=0
def Hush (T:FieldEnd G d):Prop:= ∀ (n:ℕ)(x:Points n),x∈conf n→ lot (scene x d) T=0

lemma hush_realized {T:FieldEnd G d}(H:Hush T)(x:Points n)(h:x∈conf n)(p:Tags G d n): lot (scene x d) T p=0:=by rw [H _ x h];rfl
lemma field_real (T:FieldEnd G d) (R:Respects T) (t:ℝ) (p:Sec G d): reel d (forward T t p)= forward T t (reel d p) :=by
  let U:=reelR (G:=G) d; let V:= T.restrictScalars ℝ; have h:Commute (err U) (t • err V):=by
    apply ContinuousLinearMap.ext; intro x; obtain ⟨p,rfl⟩:= (tableD G d).surjective x
    change err U (t • err V (tableD _ _ p))= t • err V (err U (tableD _ _ p)); simp_rw [map_smul,err_apply]; exact congr_arg (fun p:Sec G d=> t • tableD G d p) (R p)
  have he : ∀ x, err U (going T t x)= going T t (err U x):=fun x=>congr_arg (fun f:RSpace G d→L[ℝ] RSpace G d=> f x) h.exp_right.eq
  apply (tableD G d).injective; change tableD G d (U (forward T t p))=_; rw [← err_apply,forward_eq, he,err_apply,forward_eq]; rfl

lemma field_realizes (T:FieldEnd G d) (R:Respects T) (t:ℝ): Sample.RealMove (paintR T t) d:=by
  intro p h hp; let P:Sec G d:=⟨p,h⟩; have ht : reel d P=P:=Subtype.ext hp
  rw [show paintR T t p=(forward T t P).val from painted P t,← real_proj, field_real _ R,ht]

lemma field_move (T:FieldEnd G d) (R:Respects T) (H:Hush T) (h₄:KillsFour T) (hd:4≤d) (t:ℝ): Sample.Moves (paintR T t) d where
  fits p _:= (forward T t (project d p)).property
  quad p:= by
    let u : Sec G d:= ⟨team G p p, team_label p p hd⟩; change paintR _ _ u.val=u.val; rw [painted,frozen]
    exact h₄ u (team_label _ _ le_rfl)
  arrays n x p hx hp:= by
    let v (t:ℝ) i := forward T t (⟨p i,hp i⟩)
    let f (t:ℝ) (i : Fin n):= tableD G d (v t i); let A:= ((scene (G:=G) x d).restrictScalars ℝ).compLinearMap fun i:Fin n=> (tableD G d).symm.toLinearMap; let L:ContinuousMultilinearMap ℝ (fun _ : Fin n=> RSpace G d) ℂ:=⟨A,cont_land A⟩
    let D (t:ℝ) := scene x d (v t)
    have he' (t:ℝ) (i : Fin n): HasDerivAt (fun s=> f s i) (tableD G d (T (v t i))) t:= forwards _ _ _
    have hL (p): L (fun i=>tableD G d (p i))=scene x d p:=by change scene x d (fun i => (tableD G d).symm (tableD G d (p i)))=_; simp
    have he : D=L ∘ f:=funext fun i=>(hL (v i)).symm
    have hz (t:ℝ): HasDerivAt D 0 t := by
      let F (i : Fin n):= tableD G d (T (v t i))
      have hf : HasDerivAt f F t:= hasDerivAt_pi.mpr (he' t)
      rw [he]; apply ((L.hasFDerivAt (f t)).comp_hasDerivAt t hf).congr_deriv; rw [ContinuousMultilinearMap.linearDeriv_apply];
      have ha (i:Fin n): update (f t) i (F i)=fun j=> tableD G d (update (v t) i (T (v t i)) j):=by funext j; by_cases h:j=i <;> simp [h,f,F]
      simp_rw [ha,hL]; exact (_root_.Eq.trans (lots ..).symm (hush_realized H x hx _))
    have hs:= is_const_of_deriv_eq_zero (fun s=>(hz s).differentiableAt) (fun s=>(hz s).deriv) t 0
    apply Eq.trans _ (hs.trans ?_)
    · unfold D; rw [screen]; apply congr_arg; funext i; exact painted (⟨p i,hp i⟩:Sec G d) _
    unfold D v; simp [forward0,screen]
lemma field_stops (T:FieldEnd G d) (R:Respects T) (H:Hush T) (h₄:KillsFour T) (g:G.Simple) (hd:4≤d) (x:Sec G d) (he : reel d x=x): T x=0:=by
  have hi : realForm x.val=x.val:=congr_arg Subtype.val he
  let y (t : ℝ) (Z:TaylorTower G):= probe Z (forward T t x).val
  have hh (Z:TaylorTower G) : HasDerivAt (fun t=>y t Z) (probe Z (T x).val) 0:=by
    let L := LinearMap.toContinuousLinearMap (((probe Z).toLinearMap ∘ₗ coeS (G:=G) d).restrictScalars ℝ |>.comp (tableD G d).symm.toLinearMap)
    have he (p) : L (tableD G d p) = probe Z p.val:=by unfold L; simp; rfl
    have hk : (fun t=> y t Z)= L ∘ (fun t => tableD G d (forward T t x)):= funext fun t=> (he _).symm; rw [hk]; convert! L.hasFDerivAt.comp_hasDerivAt (0:ℝ) (forwards T x 0) using 1; rw [forward0, he]
  have hv := local_sing g x.property y (fun t=> sings (p:=(forward T t x).val) (forward T t x).property) (fun t=> ?_) (fun Z=> ?_)
  · apply Subtype.ext; apply equalPol; intro Z
    have hl : HasDerivAt (fun t=>y t Z) 0 0:=(hasDerivAt_const _ (probe Z x.val)).congr_of_eventuallyEq (hv.mono fun t h=> congr_fun h Z)
    rw [show probe Z (T x).val=0 from (hh Z).unique hl,Submodule.coe_zero,map_zero]
  · obtain ⟨M,hm,h⟩:= exists_wrench (coreColor g) (field_move T R H h₄ hd t) (field_realizes T R t) hd
    refine ⟨M,h,funext fun Z=>?_⟩; unfold y; rw [← painted x]; exact (hm Z x.val x.property hi).symm
  simpa only [y,forward0] using (hh Z).continuousAt.tendsto


theorem from_real (T:FieldEnd G d)(g:G.Simple)(R:Respects T)(h:4≤d)(H:KillsFour T)(S:Hush T): T=0:=by
  have hh: coeS d ∘ₗ T=0:= Normalize.real_tests fun x he=>by rw [LinearMap.comp_apply,field_stops T R S H g h x he,map_zero]; rfl
  ext1 p; apply Subtype.ext; exact DFunLike.congr_fun hh p
lemma realWind (x:Points n)(h:x∈conf n)(p:Tags G d n): scene x d (fun i=> reel d (p i)) = star (scene x d p):= moment_real x h (fun i=>(p i).val)
lemma hush_bar {T:FieldEnd G d}(H:Hush T): Hush (matR d T):=by
  intro n x hx; ext1 p; let u:=fun i: Fin n=> reel d (p i);
  have he (i:Fin n): scene x d (update p i (matR d T (p i)))= star (scene x d (update u i (T (u i)))):=by
    rw [← realWind x hx]; congr 1; ext1 j; by_cases h:j=i; subst j; simp [u,rsa]; simp [u,h,reel_back]
  rw [lots]; simp only [he,← star_sum,← lots, H n x hx,zero_apply,star_zero]
def Stopped (d:ℕ) : Submodule ℂ (FieldEnd G d) where
 carrier:= {T| KillsFour T ∧ Hush T}
 zero_mem':=⟨fun _ _=>rfl, fun _ _ _=> map_zero _⟩
 add_mem' := by rintro F T ⟨p,q⟩ ⟨u,v⟩; exact ⟨fun x hx=> by rw [LinearMap.add_apply, p x hx,u x hx,zero_add],fun i x h=> by rw [map_add,q i x h,v i x h,zero_add]⟩
 smul_mem' := by rintro a x ⟨p,q⟩; exact ⟨fun i h=> by rw [LinearMap.smul_apply,p i h,smul_zero],fun i y hy=> by rw [map_smul,q i y hy,smul_zero]⟩
lemma sinks {T:FieldEnd G d}(H:T∈ Stopped d): matR d T ∈ Stopped d:= ⟨fun p hp=> by rw [rsa,H.1 (reel d p) (closed_sector hp 1|>.2),map_zero], hush_bar H.2⟩
set_option backward.isDefEq.respectTransparency false in
theorem stopper (g:G.Simple)(h:4≤d){T:FieldEnd G d}(H:T∈ Stopped d): T=0:=by
  have he (T:FieldEnd G d)(H:T∈ Stopped d):mid T=0:= from_real _ g (mid_anchor T) h (show mid T∈ Stopped d from Submodule.smul_mem _ _ (Submodule.add_mem _ H (sinks H))).1 (show mid T∈ Stopped d from Submodule.smul_mem _ _ (Submodule.add_mem _ H (sinks H))).2
  have ht(x:FieldEnd G d)(h:x∈ Stopped d)(p:Sec G d): matR d x p= -x p:=by
    have hh: (2:ℂ)⁻¹ • (x p+matR d x p)=0:= DFunLike.congr_fun (he x h) p; have hx: x p+matR d x p=0:=(smul_eq_zero.mp hh).resolve_left (by norm_num); exact eq_neg_of_add_eq_zero_right hx -- order inspect
  ext1 p; have hh := ht _ ((Stopped d).smul_mem Complex.I H) p; rw [(matR d).map_smulₛₗ, LinearMap.smul_apply,LinearMap.smul_apply, ht T H, show (starRingEnd ℂ) Complex.I= -Complex.I by simp,neg_smul,smul_neg,neg_neg] at hh; have hp: Complex.I • T p=0:= by have hh:= add_eq_zero_iff_eq_neg.mpr hh; rw [← two_smul ℂ] at hh; exact (smul_eq_zero.mp hh).resolve_left two_ne_zero
  exact (smul_eq_zero.mp hp).resolve_left Complex.I_ne_zero

lemma same_low (h:G.Simple)(p:WickPol G) (hp:p∈ shellSector G 4): Taylor.mirror (Maxwell.Slot G) p=p:= by
  let T:Submodule ℂ (WickPol G):= LinearMap.ker ((Taylor.mirror _).toLinearMap-LinearMap.id); have ht:p∈T:=by apply (low_span T h).2 _ hp; refine ⟨sub_eq_zero.mpr (map_one (Taylor.mirror (Maxwell.Slot G))),fun i j _=> sub_eq_zero.mpr (show Taylor.mirror _ (label G i j)= _ from ?_)⟩; simp [label, team,map_sum,bit,Taylor.mirror_sym]
  exact sub_eq_zero.mp ht

def Twos (T: FieldEnd G d) := hinge d ∘ₗ T ∘ₗ hinge d
def Odd (d:ℕ): Submodule ℂ (FieldEnd G d) where
 carrier:= {T| T∈Tri G d ∧ ∀ p,Twos T p = - T p}
 zero_mem':=⟨Submodule.zero_mem _,fun p=> (by simp [Twos])⟩
 add_mem' := by rintro x y ⟨hx,h⟩ ⟨hy,H⟩; exact ⟨Submodule.add_mem _ hx hy,fun p=> by change hinge d (x (hinge d p)+y (hinge d p))=_; rw [map_add, ← show Twos x p=hinge d (x (hinge d p)) from rfl, ← show Twos y p=hinge d (y (hinge d p)) from rfl,h,H]; rw [LinearMap.add_apply]; abel⟩
 smul_mem' := by rintro a x ⟨hx,h⟩; exact ⟨Submodule.smul_mem _ _ hx,fun p=> by change hinge d (a • x (hinge d p))=_; rw [map_smul,← show Twos x p=hinge d (x (hinge d p)) from rfl,h,smul_neg];rfl⟩
lemma odd_four (g:G.Simple)(h:4≤d){T:FieldEnd G d}(H:T∈ Odd d): KillsFour T:=by
  rintro p hp; have he(p:Sec G d)(hp:p.val∈ shellSector G 4): hinge d p=p:=Subtype.ext (same_low g p.val hp); have ht:= H.2 p; unfold Twos at ht; simp only [LinearMap.comp_apply,he p hp,he (T p) ((tri_may T).1 H.1|>.2 4 h p hp)] at ht; have hh:= add_eq_zero_iff_eq_neg.mpr ht; rw [← two_smul ℂ] at hh; exact (smul_eq_zero.mp hh).resolve_left two_ne_zero
lemma odd_hush {T:FieldEnd G d}(h:T∈ Odd d)(g:G.Simple)(hd:4≤d)(H:Hush T): T=0:= stopper g hd ⟨odd_four g hd h,H⟩
end YM.XSpace.AxesTangent
