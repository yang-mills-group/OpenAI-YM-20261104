import YM.WilsonBridge.Wisdom
import YM.MS.Menus.Bulk
/-! Dilation-ray starting with engineering factors, not just Taylor order in r.
 This lets us compare midpoint and holonomy conventions without assuming mark is
 perfect past its stipulated horizon. -/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonBridge.Reader
open Function Finset Filter Set
open MS Book Koszul Cylinder Lab Native Native.Studio Native.Chart Plane Tone MS.Theater Landau Local Lifting
open Detect Mark Wire Tensor
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{N:Type}{d i j:ℕ}
local notation "Χ"=> Draft.DotFlip (G:=G) (P:= QP)
-- congruence including boundary at zero
structure Shares (d:ℕ) (f g:ℝ→ℂ): Prop where
   left : ContDiff ℝ ∞ f
   right: ContDiff ℝ ∞ g
   char (i:ℕ)(h:i≤d): reading i f = reading i g
namespace Shares
variable {f g u v : ℝ→ℂ}
lemma refl (h:ContDiff ℝ ∞ f): Shares d f f:= ⟨h,h,fun _ _=>rfl⟩
lemma sum (h:Shares d f g)(e:Shares d u v): Shares d (fun t=> f t+u t) (fun t=> g t+v t):= ⟨h.left.add e.left,h.right.add e.right,fun i hi=> by rw [read_add h.left e.left, read_add h.right e.right,h.char i hi,e.char i hi]⟩
lemma mul (h:Shares d f g)(e:Shares d u v): Shares d (fun t=> f t*u t) (fun t=> g t*v t):= by
    refine ⟨h.left.mul e.left,h.right.mul e.right,fun i hi=>?_⟩; rw [read_mul h.left e.left,read_mul h.right e.right]; apply Finset.sum_congr rfl; intro j hj; rw [h.char j (by simp at hj; omega),e.char (i-j) (by omega)]
lemma trans (h:Shares d f g)(e:Shares d g v): Shares d f v:=⟨h.left,e.right,fun i hi=> (h.char i hi).trans (e.char i hi)⟩
lemma scale (c:ℂ)(h:Shares d f g): Shares d (fun t=> c*f t) (fun t=> c*g t):=(refl contDiff_const).mul h
lemma scatter_eq (p:Sector N) {F H:ℝ→ Shared N ℂ}(w:Legs N) (h:∀ l r,Split l r w→ Shares d (fun t=>F t l r) (fun t=>H t l r)): Shares d (fun t=> scatter p w (F t)) (fun t=>scatter p w (H t)):= by
    induction w generalizing F H with
    | nil=> exact h _ _ .nil
    | cons a w ih=> simp_rw [scatter_cons]; exact ih ( F:=fun t l r=> F t (a::l) r+cross (p a) (degree p l)*F t l (a::r) ) (H:=fun t l r=> H t (a::l) r+cross (p a) (degree p l)*H t l (a::r)) (fun l r hv=>(h _ _ hv.left).sum ((h _ _ hv.right).scale _))
end Shares
-- powers may only be removed after this comparison
def extP (d:ℕ)(c:ℂ)(t:ℝ) := (t:ℂ)^d*c
lemma power_j (d k:ℕ)(c:ℂ): reading k (extP d c)=if d=k then c else 0:= by convert! read_pow (j:=k) c d using 2; ext1; simp only [extP,Complex.real_smul,Complex.ofReal_pow]
lemma power_s (d:ℕ)(c:ℂ): ContDiff ℝ ∞ (extP d c):= (Complex.ofRealCLM.contDiff.pow _).mul contDiff_const
lemma tpay (i k:ℕ){f:ℝ→ℂ}(hf:ContDiff ℝ ∞ f): reading i (fun t:ℝ=> (t:ℂ)^k * f t) = if k ≤ i then reading (i-k) f else 0:= by
    rw [show (fun t:ℝ=> (t:ℂ)^k * f t)=(fun t=>extP k 1 t *f t) from funext fun t=> by rw [extP,mul_one], read_mul (power_s ..) hf]; simp_rw [power_j]; split
    next hi=>
        rw [Finset.sum_eq_single_of_mem k (by simp; omega)]; · simp
        intro j hj he; rw [if_neg (Ne.symm he),zero_mul]
    next hi=> refine Finset.sum_eq_zero fun j hj=>?_ ; rw [if_neg (by simp at hj; omega),zero_mul]
lemma cancel_m {f g:ℝ→ℂ}{v:ℤ}{c:ℂ}(hf:ContDiff ℝ ∞ f) (hg:g 0=1) (h:Rest (fun t=> g t*f t) v c)(hG:ContDiff ℝ ∞ g): Rest f v c:= by
    refine ⟨hf, h.bottom,fun k hk=>?_⟩; induction k using Nat.strong_induction_on with
    | _ k ih=>
              refine Eq.trans ?_ ( h.home k hk ); symm; rw [read_mul hG hf, Finset.sum_eq_single_of_mem 0 (by simp)]; · rw [ show reading 0 g=1 from (by simp [reading,hg]),Nat.sub_zero,one_mul]
              intro i hi he; have hz : k-i < k:= (by simp only [Finset.mem_range] at hi; omega); rw [ih (k-i) hz (by omega), if_neg (by omega),mul_zero]

-- power-scaled evaluation (accounts for engineering costs)
abbrev W (G:Gauge):= List (Lane4 G)
def extent (w: W G):ℕ:= (w.map fun i=> Landau.dim i.1.1).sum
def extras (δ:Lane4 G→ℝ→ℂ)(t:ℝ)(w: W G):=(w.map fun j=>δ j t).prod
lemma inert (t:ℝ)(w:W G): extras (fun _ _=> 1) t w=1:= by induction w with| nil=> rfl| cons a w ih=> simp [extras] at *
@[simp] lemma extent_as (w:W G): fieldDim wfield w=(extent w:ℤ):= by induction w with| nil=>rfl| cons i w ih=> rw [field_cons,ih]; unfold extent; push_cast; simp
lemma extent_f {l r w:W G}(p:Split l r w):extent l+extent r=extent w := split_sum (fun i:Lane4 G=> Landau.dim i.1.1) p
lemma extent_x (δ:Lane4 G→ℝ→ℂ)(t:ℝ){l r w:W G}(p:Split l r w): extras δ t w=extras δ t l *extras δ t r:= by unfold extras; rw [← List.prod_append, ← List.map_append ]; exact ((split_perm p).map (fun j=>δ j t) |>.symm).prod_eq
lemma extra_s {δ:Lane4 G→ℝ→ℂ}(h:∀ t,ContDiff ℝ ∞ (δ t))(w:W G): ContDiff ℝ ∞ (fun t=> extras δ t w):= by induction w with| nil=> exact contDiff_const| cons a w ih=> simp_rw [extras,List.map_cons,List.prod_cons]; exact (h a).mul ih

variable (δ:Lane4 G→ℝ→ℂ)
def pose (w:W G): (Law G) →ₗ[ℂ] (ℝ→ℂ):= LinearMap.pi fun t=> ((t:ℂ)^extent w * extras δ t w ) • LinearMap.proj (sail (ray w) t)
lemma posing (w: W G)(t:ℝ)(L:Law G) : pose δ w L t= (t:ℂ)^extent w * (extras δ t w* fieldVal L (ray w) t):= mul_assoc ..
lemma poseM (w:W G)(t:ℝ)(L H:Law G) : pose δ w (product Χ L H) t= scatter Χ w (fun l r=> pose δ l L t * pose δ r H t):= by
    rw [posing]; unfold fieldVal; rw [scattered, ray_go, scatter_move _ (fun i:Lane4 G=> (i.1,t • i.2)) (fun _=>rfl) ]; rw [← mul_assoc]; let tot (l r:W G):=fieldVal L (ray l) t*fieldVal H (ray r) t; let p:=(t:ℂ)^extent w*extras δ t w
    have ha : ∀ w:W G,sail (ray w) t=w.map fun i=> (i.1,t • i.2):=fun w=>ray_go ..; simp_rw [← ha];
    change p • (allocate Χ w tot)= _; rw [← map_smul]; change scatter Χ w _= _; refine scatter_congr _ _ _ _ fun l r h=>?_ ; change p*(fieldVal L (ray l) t*fieldVal H (ray r) t)=_; rw [posing,posing]; unfold p; rw [← extent_f h,pow_add, extent_x δ t h]; ring


-- Bare `sail` agrees by itself. Use Shares.Put product.
abbrev base (w:W G):= pose (fun _ _=>1) w
def Adjoin (L H:Law G)(d:ℕ):= ∀ w:W G,Shares d (pose δ w L) (base w H)
lemma pose_share (w:W G){L:Law G}(t:ℝ): base w L t= ((t:ℂ) ^ extent w) * fieldVal L (ray w) t:= by rw [base,posing,inert,one_mul]
namespace Adjoin
variable {δ}{F H V L: Law G}
lemma sum (h:Adjoin δ F H d)(he:Adjoin δ V L d): Adjoin δ (F+V) (H+L) d:= by intro w; rw [map_add,map_add]; exact (h w).sum (he w)
lemma cash (c:ℂ)(h:Adjoin δ F H d): Adjoin δ (c • F) (c • H) d:= by intro w; rw [map_smul,map_smul]; exact (h w).scale c
lemma pair (h:Adjoin δ F H d)(g:Adjoin δ V L d): Adjoin δ (product Χ F V) (product Χ H L) d:= by
    intro w; rw [funext (fun t=>poseM δ w t F V), funext (fun t=> poseM (fun _ _=>1) w t H L)]; refine Shares.scatter_eq Χ w (F:=fun t l r=> pose δ l F t* pose δ r V t) (H:=fun t l r=> base l H t* base r L t) fun l r _=>?_ ; exact (h l).mul (g r)
lemma coinA (c:ℂ): Adjoin δ (coin (A:=Lane4 G) c) (coin c) d:= by
   rintro (_|w); · rw [show base ([]:W G) (coin c)=fun _=> c from ?_, show pose δ [] (coin c) = (fun _:ℝ=>c) from ?_]; exact Shares.refl contDiff_const; all_goals ext1 t; (first| unfold base|skip); rw [posing]; simp [extent,extras,fieldVal,coin] -- remove simp
   rename_i u; rw [show base (w::u) (coin c)= fun _=> 0 from ?_,show pose δ (w::u) (coin c)=(fun _:ℝ=> (0:ℂ)) from ?_]; exact Shares.refl contDiff_const; all_goals ext1 t; (first| unfold base| skip); rw [posing]; simp [extent,extras,fieldVal,coin]
lemma cancels {d:ℕ}{K:Dot G Lattice.Cover} (h:Adjoin δ (run K) H d)
        (hs:∀ i,ContDiff ℝ ∞ (δ i))(h1:∀ i,δ i 0=1)(h₂:Form H wfield d false) : Lifting.Face wfield (run K) H d false:= by
    intro w hw; let v:=fieldVal ( run K ) ( ray w ); let D:=fun t=> extras δ t w; have ha:= h w; have h':ContDiff ℝ ∞ v := Menus.all_smooth ..
    refine cancel_m h' ?_ ?_ (extra_s hs w); · simp only [extras, h1,List.map_const',List.prod_replicate,one_pow ]; -- order d:c cast notation
    have hH := h₂ ℝ (ray w) ( fun x=> Bool.noConfusion x ); rw [ray_dim] at hH; rw [extent_as] at *; refine ⟨(extra_s hs w).mul h',fun hk=> ?_,fun j hj=>?_⟩
    · simpa only [fieldVal,ray_sail,Pi.zero_apply] using congr_fun ( hH.charge hk ) 1
    let i:= j+extent w; rw [show j=i-extent w from (by unfold i;omega)]; -- at RHS too
    have he:=ha.char i (by unfold i; omega); rw [funext (fun t=>posing δ w t (run K)), tpay i (extent w) ((extra_s hs w).mul h'), if_pos (show extent w ≤ i from (by unfold i; omega))] at he; rw [he];
    rw [funext (fun t=>pose_share (L:=H) w t), tpay i _ hH.smooth, if_pos (show extent w ≤ i from (by unfold i;omega)) ];
    unfold fieldVal; rw [← torch_at] ; rw [ h₂.const_term w (fun v=>Bool.noConfusion v) ]; split <;> split <;> first| rfl| (rw [extent_as] at *; omega)
end Adjoin
open Labels Next.Foundations BV BV.Woven Physical
variable {u:Pol G}
local notation "Ψ"=> MS.Theater.orbit G
lemma hold {F:Law G}(h:Form F wfield d false)(w:W G)(t:ℝ): base w F t=extP d (F w) t:= by
    rw [pose_share]; let s:=fieldVal F (ray w); have he:s 1=F w:= by simp [s,fieldVal]
    obtain hu:= h ℝ (ray w) (fun k=>Bool.noConfusion k); rw [ray_dim,extent_as] at hu
    by_cases hv:extent w≤d
    · have hh : s t=t^(d-extent w) • F w:= by
           rw [show (d:ℤ)-(extent w:ℤ)= ((↑(d-extent w)):ℤ) from by omega] at hu; rw [← he,show s t=s (t • (1:ℝ)) from by simp]; simp_rw [show s (t • (1:ℝ))= _ from hu.scale t 1,zpow_natCast]; rfl
      change _*s t=_; unfold extP; rw [hh, Complex.real_smul,Complex.ofReal_pow,← mul_assoc,← pow_add, Nat.add_sub_of_le hv]
    have hZ:s=0:=hu.charge (by omega); rw [← he, show fieldVal F _ t=s t from rfl,hZ,Pi.zero_apply,extP,Pi.zero_apply,mul_zero,mul_zero]
lemma formA (h:At u (d,i)) : Form (Ψ u) wfield d false:= by
    obtain ⟨hx,hv,h'⟩:= tileCub.mp ( fare G _ _ ( setting_K h ).1 ); exact (shift_grade hv).mpr (by simpa using hx)
lemma monomial_A (w:Labels.Key G→₀ℕ) (c:ℂ): Form ( Ψ ( MvPolynomial.monomial w c )) wfield (height w) false := formA (i:= w.sum fun _ a=> a ) (( nodeId _ _ ).mpr ( MvPolynomial.isWeightedHomogeneous_monomial _ _ _ (weight_slot w) ))
lemma orbit_s (w:W G)(u:Pol G): ContDiff ℝ ∞ (base w (Ψ u)) := by
    induction u using MvPolynomial.induction_on' with
    | monomial p c=> rw [funext ( fun t=> hold (monomial_A p c) w t )]; exact power_s ..
    | add p q hp hq=> rw [map_add,map_add]; exact hp.add hq
lemma skill (u:Pol G)(k:ℕ) (w:W G): reading k (base w (Ψ u))= Ψ (tier k u) w:= by
    induction u using MvPolynomial.induction_on' with
    | monomial p c=>
       have hm := MvPolynomial.isWeightedHomogeneous_monomial generation p c (m:=Labels.height p) rfl
       rw [funext ( fun t=> hold (monomial_A p c) w t ),power_j]; split
       next he=> subst k; rw [tier,hm.weightedHomogeneousComponent_same]
       next hx=> rw [tier,hm.weightedHomogeneousComponent_ne k (Ne.symm hx),map_zero]; rfl
    | add p q hp hq=>
       simp_rw [map_add]; change reading k (fun t=>_+_)= _; rw [ read_add (orbit_s w p) (orbit_s w q),hp,hq ]; rfl
lemma Adjoin.trunc {L:Law G}(h:Adjoin δ L (Ψ u) d): Adjoin δ L (Ψ (capRead d u)) d:= by
    intro w; exact (h w).trans ⟨(h w).right,orbit_s ..,fun k hk=> by rw [skill,skill,tier_capRead d _ k hk]⟩
end YM.WilsonBridge.Reader
