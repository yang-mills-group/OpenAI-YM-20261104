import YM.PertExtension.ReflectFrame
import YM.Trace.Measuring
import YM.RG12.Kintsugi.Zen
/-!
# Angular calibration on protected rows

Compress *outlet* rows tested together in a traceless multi-Stress family
(corresponds to a 3d diag sector and a 6d off-diag sector under Signed).
We use an invariant free pairing to recognize these rows; no covariance or
orthogonality claim in physical *norm* or cutoff conventions.
-/
set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.RG12.Kintsugi
open Function Filter Finset Set Analysis Spec Org Climb Table Next.UVStress UVNext.FreeStress Work.A01 Maxwell
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{L:Register G}{S:Table L}(H:S.RealSpin)
-- target is defined schemewise (also free), so Sec: tests across frames
abbrev Auspect (S:Table L):= Axis→Axis→ S.Field 4 →L[ℂ] ℂ
structure Peal (f:Auspect S):Prop where
   sym i j : f i j=f j i
   were (i j:Axis)(v:S.Field 4): f i j (S.conj H 4 v) = star (f i j v)
   bars (k:Signed)(i j:Axis)(v:S.Field 4): f i j (S.mirror H 4 k⁻¹ v) = (eps k i * eps k j : ℝ) • f (k.perm i) (k.perm j) v
   track (v:S.Field 4): ∑ i:Axis,f i i v=0
-- a traceless invariant tensor scalar reading vanishes by group theory (incl unit)
lemma on_scalar {E:Type*}[AddCommGroup E][Module ℂ E][Module ℝ E][IsScalarTower ℝ ℂ E] (v:Axis→Axis→E)
   (h:∀ (k:Signed) i j,v i j=(eps k i*eps k j :ℝ) • v (k.perm i) (k.perm j)) (ht:∑ i:Axis,v i i=0): v=0:=by
   have he (i j : Axis) (he:i≠j): v i j=0 := by
      have hv := h (Signed.mirror i) i j
      have hp : (2:ℝ) • v i j=0:= by
         simp only [Signed.mirror,eps, Signed.matrix_at] at hv
         simp [he] at hv
         rw [two_smul]; exact eq_neg_iff_add_eq_zero.mp hv
      rcases smul_eq_zero.mp hp with h|h
      · norm_num at h
      exact h
   have hq (i : Axis) : v 0 0=v i i:=by
      let t:Signed:=⟨Equiv.swap 0 i,fun _=>false⟩
      have e:= h t 0 0
      rw [eps_self,one_smul] at e
      simpa [t] using e
   have ht: v 0 0=0:= by
      have hx : (4:ℝ) • v 0 0=0 := calc
        (4:ℝ) • v 0 0 = ∑ _i:Axis,v 0 0 := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]; exact Nat.cast_smul_eq_nsmul (R:=ℝ) ..
        _ = (0:E):= (Finset.sum_congr rfl (fun i _=>hq i)).trans ht
      exact (smul_eq_zero.mp hx).resolve_left (by norm_num)
   funext i j; rcases eq_or_ne i j with rfl|hk
   · exact (hq _).symm.trans ht
   exact he _ _ hk
lemma Peal.silence {f:Auspect S}(h:Peal H f)(w:S.Field 4)(he:∀ k:Signed,S.mirror H 4 k w=w)(a b:Axis):f a b w=0:=by
   have hk:=on_scalar (E:=ℂ) (fun i j=>f i j w) (fun k i j=>(congr_arg _ (he k⁻¹).symm).trans (h.bars k i j w)) (h.track w)
   exact congr_fun (congr_fun hk a) b
lemma Peal.axis {f:Auspect S}{J:S.Stress}(h:Peal H f)(ht:RawTensor H J) :
   ∀ (k:Signed)(i j a b:Axis), f (k.perm i) (k.perm j) (J (k.perm a) (k.perm b))= (eps k i*eps k j*(eps k a*eps k b):ℝ) • (f i j (J a b)):=by
    intro k i j a b
    have e:= h.bars k i j (J (k.perm a) (k.perm b))
    have he:= tensor_column ht k a b
    have hp i := eps_self k i
    let u:=eps k i *eps k j; let v:=eps k a * eps k b
    have hv(l m:Axis): (eps k l * eps k m)*(eps k l*eps k m)=1:=by
       have E : ∀ s t :ℝ,s*t*(s*t)=s*s*(t*t):=fun x y=>by ring
       rw [E,hp,hp,one_mul]
    have hx : J (k.perm a) (k.perm b)=(v:ℝ) • S.mirror H 4 k (J a b):=by rw [he,Complex.coe_smul,smul_smul,hv,one_smul]
    conv_lhs=>rw [hx]
    specialize e
    have hL := h.bars k i j (S.mirror H 4 k (J a b)); rw [← S.mirror_mul,inv_mul_cancel,S.mirror_one] at hL
    change f _ _ (_ • _)=(u*v) • _
    rw [map_real_smul_clm, hL, smul_smul]; congr 1
    change v=(u*v)*u; rw [mul_comm u v,mul_assoc,show u*u=1 from hv ..,mul_one]
where map_real_smul_clm (F:S.Field 4→L[ℂ] ℂ)(r:ℝ)(x:S.Field 4):F (r • x)=r • F x:=(F.restrictScalars ℝ).map_smul ..

-- Reuse reflection moment (sum at all oriented images) as the positive pairing.
variable {C:Family G}(T:MaxwellData C)
local notation "B!"=>Bel C.book
local notation "F!"=>C.book.grid
set_option quotPrecheck false
local notation "V!"=>(B!).Field 4
local notation "h!"=>T.hT.spin
open PertExtension.Rigidity.Positive

def crystals : (V!) →ₗ[ℝ] (V!) where
   toFun := (B!).conj (h!) 4
   map_add' _ _:= map_add ..
   map_smul' i x:=by
      rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smulₛₗ]
      change _= i • _
      simp [Complex.coe_smul]

def china : (V!)→ₗ[ℝ] (V!)→ₗ[ℝ] ℝ:=
   let q : LinearMap.BilinForm ℝ (V!):= positive (F!) T.hT
   q + LinearMap.BilinForm.comp q (crystals T) (crystals T)
lemma inscribed (v w : (V!)):china T v w=positive (F!) T.hT v w + positive (F!) T.hT ((B!).conj (h!) 4 v) ((B!).conj (h!) 4 w):=by unfold china crystals; simp
lemma ruby {v:V!}(hv:v≠0): 0 < china T v v:=by
   rw [inscribed]; have he:= positive_def (F!) T.hT hv
   let w := (B!).conj (h!) 4 v
   have hw:w≠0:=fun hh=>hv (by rw [← (B!).reflect_star (h!) 4 v, show (B!).conj (h!) 4 v = 0 from hh,map_zero])
   exact add_pos he (positive_def F! T.hT hw)
lemma scales (v w:V!)(s:Signed) : china T ((B!).mirror (h!) 4 s v) w=china T v ((B!).mirror (h!) 4 s⁻¹ w):=by
   have h₁ (x y:V!) : china T ((B!).mirror (h!) 4 s x) ((B!).mirror (h!) 4 s y)=china T x y:=by
      rw [inscribed,(B!).mirror_star,(B!).mirror_star, PertExtension.Rigidity.Positive.position_invariant (F!) T.hT x y s]
      rw [show _ = positive (F!) T.hT ((B!).conj (h!) 4 x) ((B!).conj (h!) 4 y) from position_invariant (F!) T.hT _ _ s,inscribed]
   rw [← h₁ v ((B!).mirror (h!) 4 s⁻¹ w), ← (B!).mirror_mul, mul_inv_cancel,(B!).mirror_one]
lemma swivels (v w:V!) : china T ((B!).conj (h!) 4 v) w=china T v ((B!).conj (h!) 4 w):=by
   simp_rw [inscribed,(B!).reflect_star]; rw [add_comm]
lemma china_full : Bijective (china T):=by
   have hi: Injective (china T):=LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (by
      intro v h
      by_contra! h₀; exact (ruby T h₀).ne' (DFunLike.congr_fun h v)))
   exact ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Module.finrank_linearMap_self ..).symm).1 hi⟩
end YM.RG12.Kintsugi
