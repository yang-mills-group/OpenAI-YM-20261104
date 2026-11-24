import YM.RG12.Kintsugi.Outlet
import YM.Trace.Measuring
/-! # Nonvacuous protected sector: actual stress-dual quotes with faithful detection
       on the complex span. Construction on S from rank into a canonical free metric.
       No claim that scale-dependent phases preserve Final.energy! -/
set_option maxRecDepth 6000
set_option maxHeartbeats 250000
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Kintsugi
open Filter Set Function Analysis Extraction Table Climb Ward Next.UVStress Spec Org Next.Rank
open UVNext.FreeStress Commission Work.A01
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(U : Final C f S)
local notation "h'"=>U.room.kernel.spin
local notation "J'"=>U.sector.energy
local notation "χ"=>C.path.levels.clock.hatBeta

-- trace removal (vacuum included)
def beamline {L:Register G}{S:Table L}(J:S.Stress): S.Stress:=fun i j=> J i j-if i=j then (1/4:ℝ) • ∑ x:Axis,J x x else 0
lemma tracing {L:Register G}{W:Table L}{H : W.RealSpin}{W':W.Stress}(hJ:W'∈SymSpace H):
   let x:=beamline W';
   (∀ i j,x i j = x j i) ∧ (∀ i j,W.conj H 4 (x i j)=x i j) ∧
   (∀ (k:Signed) i j,W.mirror H 4 k (x i j)=(eps k i *eps k j:ℝ) • x (k.perm i) (k.perm j))∧∑ i:Axis,x i i=0:= by
   obtain ⟨A,B,Q⟩:=sym_mem.mp hJ; intro x
   refine ⟨?_,?_,?_,?_⟩
   · intro i j; unfold x beamline; congr 1; exact A i j
     simp only [eq_comm]
   · intro i j; unfold x beamline
     split <;> rw [map_sub,B i j]; swap; rw [map_zero]
     rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) (1/4:ℝ),map_smulₛₗ,map_sum]; simp [B,map_ofNat]
   · intro s i j; unfold x beamline
     rw [map_sub,tensor_column Q,Complex.coe_smul]
     by_cases h:i=j
     · subst j; simp only [if_true,eps_self,one_smul,RCLike.real_smul_eq_coe_smul (K:=ℂ) (1/4:ℝ),map_smul,map_sum]
       congr 2; simp_rw [tensor_column Q,eps_self,Complex.ofReal_one,one_smul]; exact Equiv.sum_comp s.perm (fun i=>W' i i)
     simp only [if_neg h,map_zero,s.perm.apply_eq_iff_eq,sub_zero]
   unfold x beamline; simp only [if_true,Finset.sum_sub_distrib,Finset.sum_const, Finset.card_univ,Fintype.card_fin]
   rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul]; norm_num

def grain : S.Stress:=beamline (J')
lemma grain_mem : J' ∈ SymSpace (h') := sym_mem.mpr ⟨U.phase.transport.conserved.symmetric,U.phase.transport.conserved.real,fun s i j=>by rw [←U.phase.transport.spots.signed];exact U.phase.transport.spin ..⟩
def GrainSpace : Submodule ℂ (S.Field 4):= Submodule.span ℂ (Set.range fun p:Axis×Axis => grain U p.1 p.2)

local notation "B!"=>Bel C.book
set_option quotPrecheck false
local notation "W!"=> S.Field 4
local notation "κ" k:max=> C.S.a k

-- parameterize Hermitian lift by any invariant real pairing
section Applications
variable (p: LinearMap.BilinForm ℝ (S.Field 4))
def terra (w : W!) : W!→ₗ[ℂ]ℂ where
   toFun x := (p w x:ℂ) - Complex.I * (p w (Complex.I • x):ℂ)
   map_add' x y := by simp [map_add,smul_add];ring
   map_smul' r x:=by
      have h (r:ℂ) : r • x=r.re • x + r.im • (Complex.I • x):=by
         rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_smul,← add_smul]; simp
      simp only [smul_eq_mul,RingHom.id_apply,smul_smul]
      rw [h r,h (Complex.I*r)]
      simp only [map_add,map_smul,smul_eq_mul,Complex.ofReal_add,Complex.ofReal_mul,Complex.I_mul_re,Complex.I_mul_im]
      set a:= (p w x:ℝ); set b:= (p w (Complex.I • x):ℝ)
      apply Complex.ext <;> simp
lemma porcelain (h:∀ w x,p (S.conj U.room.kernel.spin 4 w) x=p w (S.conj U.room.kernel.spin 4 x)){w:W!}(hw:S.conj (h') 4 w=w)(x:W!): terra p w (S.conj (h') 4 x)=star (terra p w x):=by
   have he(x):p w (S.conj (h') 4 x)= p w x:=by rw [← h,hw]
   have ht:Complex.I • S.conj (h') 4 x = -S.conj (h') 4 (Complex.I • x):=by rw [map_smulₛₗ]; change _ = - (star (Complex.I:ℂ) • _); rw [Complex.star_def,Complex.conj_I,neg_smul,neg_neg]
   change (↑(p w (S.conj (h') 4 x)):ℂ) - Complex.I * (p w (Complex.I • S.conj (h') 4 x):ℂ) = star ((p w x :ℂ) - Complex.I * (p w (Complex.I • x):ℂ))
   rw [he,ht,map_neg,he]; simp
lemma duty (h:∀ (s:Signed) w x,p w (S.mirror U.room.kernel.spin 4 s⁻¹ x)=p (S.mirror U.room.kernel.spin 4 s w) x)(w x:W!)(s:Signed): terra p w (S.mirror (h') 4 s⁻¹ x)=terra p (S.mirror (h') 4 s w) x:=by
   have hs : Complex.I • S.mirror (h') 4 s⁻¹ x = S.mirror (h') 4 s⁻¹ (Complex.I • x):=(map_smul ..).symm
   simp only [terra,LinearMap.coe_mk,AddHom.coe_mk,hs,h]
lemma colorT (w x: W!)(i:ℝ): terra p (i • w) x=i • terra p w x:=by
   dsimp only [terra,LinearMap.coe_mk,AddHom.coe_mk]; rw [p.map_smul]
   simp only [LinearMap.smul_apply,smul_eq_mul,Complex.ofReal_mul,Complex.real_smul];ring
structure Vessel : Prop where
   spins : ∀ (s:Signed) w x,p w (S.mirror U.room.kernel.spin 4 s⁻¹ x)=p (S.mirror U.room.kernel.spin 4 s w) x
   real : ∀ w x,p (S.conj U.room.kernel.spin 4 w) x=p w (S.conj U.room.kernel.spin 4 x)
   pos : ∀ x,x≠0→ 0<p x x
lemma heated (hp:Vessel U p): ∃ L:Auspect S,Peal (h') L ∧ ∀ x: S.Field 4,x∈GrainSpace U → (∀ i j:Axis,L i j x=0) → x=0 := by
   let Z:= grain U
   let L i j : S.Field 4 →L[ℂ] ℂ:= LinearMap.toContinuousLinearMap (𝕜:=ℂ) (E:=S.Field 4) (F':=ℂ) (terra p (Z i j))
   obtain ⟨hS,hK,hC,hE⟩:= tracing (grain_mem U)
   refine ⟨L,⟨fun i j=> (show L i j=L j i from by unfold L Z grain; rw [hS]),fun i j w=>porcelain U p hp.real (hK i j) w,fun s i j w=> ?_,?_⟩,?_⟩
   · rw [show L i j _=_ from duty U p hp.spins (Z i j) w s,show S.mirror _ 4 s (Z i j) = _ from hC s i j]
     exact colorT p ..
   · intro v
     change ∑ i:Axis, terra p (Z i i) v=0
     simp only [terra,LinearMap.coe_mk,AddHom.coe_mk, Finset.sum_sub_distrib, ← Complex.ofReal_sum, ← Finset.mul_sum,← Complex.ofReal_sum]
     simp_rw [← LinearMap.sum_apply,← map_sum]
     change ∑ i:Axis,Z i i=0 at hE
     rw [hE,map_zero];simp
   intro x hx hh
   -- decompose x into real and imaginary parts of actual conjugation, both annihilated and in
   -- ℝ-span of the Zs. S projection exact. Could use complex span induction of testing
   -- but glaze not known to be Hermitian on nonreals; cover real/combin expression instead.
   have ht(v:S.Field 4)(hp:v∈GrainSpace U):∃ t:Axis×Axis→ℂ,v = ∑ i:Axis×Axis,t i • Z i.1 i.2:= by
     rw [GrainSpace] at hp
     induction hp using Submodule.span_induction with
     | mem x hx=>
       obtain ⟨i,rfl⟩:=hx; refine ⟨Pi.single i 1,?_⟩; simp [Pi.single_apply,ite_smul];rfl
       -- finset ite pos
     | zero=>exact ⟨0,by simp⟩
     | add a b _ _ i j=> obtain ⟨q,rfl⟩:=i; obtain ⟨t,rfl⟩:=j; exact ⟨q+t,by rw [← Finset.sum_add_distrib];simp [add_smul]⟩
     | smul c a _ i=> obtain ⟨q,rfl⟩:=i; exact ⟨c • q, by simp [Finset.smul_sum, Pi.smul_apply,smul_smul,smul_eq_mul]⟩
   obtain ⟨y,hy⟩:=ht x hx
   let A:Axis×Axis→_:=fun i=>Z i.1 i.2
   let r(t:Axis×Axis → ℝ):=∑ i,t i • A i
   have hr(t:Axis×Axis→ℝ) : S.conj (h') 4 (r t)=r t := by unfold r; simp only [map_sum, RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smulₛₗ];simp [A,Z,show ∀ i j,S.conj (h') 4 (grain U i j)=_ from hK]; rfl
   let a:=r (Complex.re ∘ y); let b:=r (Complex.im ∘ y)
   have he : x=a+Complex.I • b:=by
      rw [hy]; unfold a b r; simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)];rw [Finset.smul_sum,← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _=>?_
      rw [smul_smul]; unfold A; rw [← add_smul]; simp [mul_comm Complex.I]
   have hY :∀ i j t,S.conj (h') 4 t=t→ ((L i j) t).im=0:=fun i j t ht=>by
      have h1 := congr_arg Complex.im (porcelain U p hp.real (hK i j) t); rw [ht] at h1
      change ((L i j) t).im = -((L i j) t).im at h1;linarith
   rw [he] at hh
   have hL₀(i j):L i j a=0 ∧ L i j b=0:=by
      specialize hh i j; rw [map_add,map_smul] at hh
      have hx:= congr_arg Complex.re hh; have hT:= congr_arg Complex.im hh
      have h2:=hY i j a (hr _); have h3:=hY i j b (hr _)
      simp only [Complex.zero_re,Complex.zero_im,Complex.add_re,smul_eq_mul,Complex.mul_re,Complex.I_re,Complex.I_im,Complex.add_im,Complex.mul_im,h2,h3] at hx hT
      constructor <;> apply Complex.ext <;> first | exact h2 | exact h3 | change _=0;linarith
   have h0(t:Axis×Axis→ℝ)(ht: ∀ i j,L i j (r t)=0):r t=0:=by
      by_contra! h0
      have h1:= hp.pos (r t) h0
      have hu: ∀ i,p (A i) (r t)=0:=fun i=>by
        have ht:= congr_arg Complex.re (ht i.1 i.2)
        change ((↑(p (A i) (r t)):ℂ)-_).re=(0:ℝ) at ht
        simpa using ht
      rw [show r t = ∑ i, t i • A i from rfl,map_sum p,LinearMap.sum_apply] at h1
      change 0 < ∑ i:Axis×Axis,p (t i • A i) (r t) at h1; simp [hu] at h1
   rw [he];unfold a b;rw [h0 _ (fun i j=> (hL₀ i j).1),h0 _ (fun i j=> (hL₀ i j).2),smul_zero,add_zero]
end Applications

lemma onyx (T: MaxwellData C) (X : S.Field 4≃ₗ[ℂ](Bel C.book).Field 4)(h:Coherent U.room.kernel.spin T.hT.spin 4 X):∃ p,Vessel U p:=by
   let V:=Bel C.book; let Y:=X.toLinearMap.restrictScalars ℝ
   let p:=LinearMap.BilinForm.comp (china T) Y Y
   have hv(x y:S.Field 4) : p x y=china T (X x) (X y):=by
      unfold p;rw [LinearMap.BilinForm.comp_apply]
      congr
   refine ⟨p,fun s w x=> ?_,fun w x=> ?_,fun x hx=>?_⟩
   · rw [hv,hv,h.signed,h.signed]; exact (scales ..).symm
   · rw [hv,hv,h.stars,h.stars]; exact swivels ..
   rw [hv]; exact ruby T (fun he=>hx (X.injective (he.trans X.map_zero.symm)))
lemma kiln (hG:G.Simple): ∃ p:LinearMap.BilinForm ℝ (S.Field 4), Vessel U p :=by
   obtain ⟨T,-,-⟩:=oracle (C:=C) hG; obtain ⟨H,h⟩:=U.phase.transport.comparator
   obtain ⟨X,hx,hv⟩:=h 4; exact onyx U T X ⟨hx,hv⟩
end YM.RG12.Kintsugi
