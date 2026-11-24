import YM.Next.MAXWELL.Simple

/-!
# Lie-algebra part of the stabilizer argument at the true G (color
coordinates and spectrum theorem B supplied by clean Maxwell libraries).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Ice
open Maxwell.Free Function Gauge LinearMap
open scoped InnerProductSpace
variable {G:Gauge}
local notation "Y"=>G.Color
local notation "L"=>Module.End ℝ Y

def Derives (A:L) := ∀ i j, A (G.ad i j)=G.ad (A i) j+G.ad i (A j)

lemma Derives.commutator {A:L}(h:Derives A)(i) : A * G.ad i-G.ad i*A=G.ad (A i):=by
  apply LinearMap.ext; intro j; change A _-_= _; rw [h,Module.End.mul_apply,add_sub_cancel_right]

-- Embed via the supplied nondegenerate Killing metric.
def brevet (x:L) : Y→ₗ[ℝ]ℝ where
  toFun v:= trace ℝ Y (x*G.ad v)
  map_add' _ _:= by rw [map_add,mul_add,map_add]
  map_smul' _ _:= by simp

lemma Derives.lift {A:L}(h : Derives A)(hG:G.Simple):∃ y:Y,A=G.ad y:=by
  let v := (InnerProductSpace.toDual ℝ Y).symm ((brevet A).toContinuousLinearMap)
  let x : Y := (-G.casimir⁻¹) • v
  have ht (y : Y) : ⟪v,y⟫_ℝ = trace ℝ Y (A * G.ad y) := InnerProductSpace.toDual_symm_apply
  have hz (y) : trace ℝ Y ((A-G.ad x)*G.ad y)=0:= by
    rw [sub_mul,map_sub,← ht, show trace ℝ Y (G.ad x * G.ad y)=_ from neg_eq_iff_eq_neg.mp (Gauge.trace_adjoint hG x y),show ⟪x,y⟫_ℝ= _ from real_inner_smul_left v y (-G.casimir⁻¹)]; field_simp [(Gauge.casimir_pos hG).ne']; ring
  let Q:= A-G.ad x
  have hq (y) : trace ℝ Y (Q*G.ad y)=0:=hz y
  have he (p) : Q*G.ad p-G.ad p*Q=G.ad (Q p):=by
    change _-_=G.ad (A p-G.ad x p)
    rw [map_sub,Gauge.ad_jacobi,sub_mul,mul_sub,← h.commutator p]; abel
  suffices Q=0 by exact ⟨x,sub_eq_zero.mp this⟩
  apply LinearMap.ext; intro i; apply ext_inner_right ℝ; intro j
  apply mul_left_cancel₀ (Gauge.casimir_pos hG).ne'
  rw [← Gauge.trace_adjoint hG,← he,sub_mul,map_sub]
  have hT := hq (G.ad i j)
  rw [Gauge.ad_jacobi,mul_sub,map_sub,←mul_assoc, ←mul_assoc] at hT
  change _=G.casimir*⟪0,j⟫_ℝ
  rw [inner_zero_left,mul_zero,neg_sub]
  have hh : trace ℝ Y (G.ad i*Q*G.ad j) = trace ℝ Y (Q*G.ad j*G.ad i):=by rw [mul_assoc,trace_mul_comm]
  linarith

def OffKill (A:L) := ∀ i, trace ℝ Y (A*G.ad i)=0

def Celestial (A:L):=∀ i j:Y, inner ℝ (A i) j= -inner ℝ i (A j)

lemma off_kills_dawn {A:L}(hS:Celestial A)(h:OffKill A)(hG:G.Simple)
    (he : ∀ a,∃ b,A*G.ad a-G.ad a*A=G.ad b) : A=0:=by
  have ht (a z : Y) : trace ℝ Y ((A*G.ad a-G.ad a*A)*G.ad z)=0:=by
    have hp:=h (G.ad a z)
    rw [Gauge.ad_jacobi,mul_sub,map_sub,←mul_assoc, ← mul_assoc] at hp
    rw [sub_mul,map_sub]
    rw [show trace ℝ Y (G.ad a*A*G.ad z)= trace ℝ Y (A*G.ad z*G.ad a) by rw [mul_assoc,trace_mul_comm]]; exact hp
  have H (a v:Y): A (G.ad a v)=G.ad a (A v):=by
    obtain ⟨b,hb⟩:=he a; have hm := ht a b
    rw [hb, show trace ℝ Y (G.ad b* G.ad b)=_ from neg_eq_iff_eq_neg.mp (Gauge.trace_adjoint hG b b),real_inner_self_eq_norm_sq] at hm
    have hz:=casimir_pos hG
    have hm := (mul_eq_zero.mp (neg_eq_zero.mp hm)).resolve_left hz.ne'
    rw [show b=0 from norm_eq_zero.mp (by nlinarith [norm_nonneg b]),map_zero] at hb
    exact LinearMap.congr_fun (sub_eq_zero.mp hb) v
  -- an invariant skew bilinear form is zero already on commutators.
  let B:=fun a b:Y=>inner ℝ (A a) b
  have hf (a b c:Y): B (G.ad a b) c= - B b (G.ad a c):=by unfold B;rw [H,ad_skew]
  have hc (a b c:Y):B (G.ad a b) c=B a (G.ad b c):=by rw [skew_ad a b,show B (-G.ad b a) c= - B (G.ad b a) c by simp [B],hf,neg_neg]
  have hv (a b c:Y):B (G.ad a b) c=B c (G.ad a b) :=by
    rw [hf,skew_ad a c,show B b (-G.ad c a)= - B b (G.ad c a) by simp [B],neg_neg,←hc,hf,skew_ad b a,show B c (-G.ad a b)= -B c (G.ad a b) by simp [B],neg_neg]
  apply LinearMap.ext_on (ad_span hG); rintro z ⟨a,b,rfl⟩; apply ext_inner_right ℝ; intro c
  rw [LinearMap.zero_apply,inner_zero_left]
  change B _ c= _
  have his : B (G.ad a b) c= -B c (G.ad a b):= (hS ..).trans (congrArg Neg.neg (real_inner_comm ..))
  linarith [hv a b c]
end YM.RG11.Rigidity.Ice
