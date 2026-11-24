import YM.PertExtension.PositionSolve

/-!
# Triangular coupling substitution and sign conventions

This solves the *formal* change prescribed by a separated triangle
diagnostic on an X-space array, when its subtracted series has nonzero
first coefficient. It does not compute that coefficient.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace YM.PertExtension.Position
open Set Filter Function PowerSeries
open scoped Topology BigOperators Classical
variable {J P : Type*}

structure Triangle (shape : P → ℕ) (J : Type*) where
    triples : Mark J shape
    pair : Fin 3→Mark J shape   -- pair missing slot i
    one : Fin 3→Mark J shape
    slope : ℝ
    slope_ne : slope≠0

namespace Triangle
variable {shape:P→ℕ}(T:Triangle shape J)
variable {R : Type*}[CommRing R]
def connected (a : Mark J shape→R) :=
  a T.triples-(∑ i,a (T.pair i) * a (T.one i)) + 2*∏ i,a (T.one i)
abbrev fps:=PowerSeries ℝ
def deviation (A:fps) := A-C (constantCoeff A)
@[simp] lemma deviation_zero A : constantCoeff (deviation A)=0:= by simp [deviation]
def parameter (a:Mark J shape→fps) := C T.slope⁻¹ * deviation (T.connected a)
@[simp] lemma parameter_zero a : constantCoeff (T.parameter a)=0 := by simp [parameter]

lemma map_connected {S : Type*}[CommRing S] (a:Mark J shape→R)(f:R→+*S) :
    f (T.connected a)=T.connected (fun x=>f (a x)):=by simp [connected,map_sub,map_sum,map_prod, map_ofNat]

def inverseScale (a:fps) := if h : IsUnit (coeff 1 a) then a.substInvOfIsUnit h else X
lemma linearTest x : IsUnit (coeff 1 (T.parameter x)) ↔ coeff 1 (T.connected x)≠0:=by
  rw [parameter,coeff_C_mul,deviation,map_sub,coeff_C,if_neg (by decide)]; simp [T.slope_ne]

@[simp] lemma inverse_zero (a:fps): constantCoeff (inverseScale a)=0:=by
  unfold inverseScale; split_ifs <;> simp

def remeasured (a:Mark J shape→fps) (w:Mark J shape) :=
  PowerSeries.subst (inverseScale (T.parameter a)) (a w)

lemma good (A:fps)(h : constantCoeff A=0) : PowerSeries.HasSubst A:=(PowerSeries.HasSubst.of_constantCoeff_zero h)

lemma substitutes_zero {A B : fps}(hB : B.constantCoeff=0) : constantCoeff (PowerSeries.subst B A)=constantCoeff A:=by
  rw [← coeff_zero_eq_constantCoeff_apply]
  have he := coeff_subst (good B hB) A (Finsupp.single () 0)
  change coeff 0 _ = ∑ᶠ d, _ * coeff 0 (B^d) at he
  rw [he,finsum_eq_single (a:=(0:ℕ))];· simp
  intro i hi; simp [hB,hi]

theorem calibrated {a : Mark J shape→fps}(h : coeff 1 (T.connected a)≠0) :
    T.parameter (T.remeasured a)=X := by
   let b := inverseScale (T.parameter a)
   have he := good b (inverse_zero (T.parameter a))
   let f : fps→+*fps := (PowerSeries.substAlgHom (R:=ℝ) he)
   have hf (p:fps):f p=subst b p:= congr_fun (coe_substAlgHom (R:=ℝ) he) p
   have hC (r:ℝ) : f (C r)=C r := by rw [hf,subst_C];rfl
   have hA:T.connected (T.remeasured a) = f (T.connected a) := by unfold remeasured b at *; rw [T.map_connected]; simp only [hf]
   rw [parameter,deviation,hA,show constantCoeff (f _)=_ from hf _ ▸ substitutes_zero (A:=T.connected a) (B:=b) (inverse_zero _),←hC T.slope⁻¹,←hC (constantCoeff (T.connected a)),←map_sub,←map_mul]
   change f (T.parameter a) = X
   rw [hf]
   let H:= (linearTest T _).mpr h
   unfold b inverseScale; rw [dif_pos H]
   exact (T.parameter a).subst_substInvOfIsUnit_right (T.parameter_zero a) H

def parity (w : Mark J shape→ℕ)(A:Mark J shape→fps):=∀ i, (rescale (-1) (A i))=(-1:fps)^(w i)*A i

private lemma odd_has_zero {A:fps}(h:rescale (-1) A= -A) : A.constantCoeff=0 := by
  have ht := congr_arg (coeff (R:=ℝ) 0) h
  rw [coeff_rescale,pow_zero,one_mul,map_neg,coeff_zero_eq_constantCoeff_apply] at ht
  linarith

lemma rescale_inverse_odd {A:fps}(h:rescale (-1) A=-A)(ha:IsUnit (coeff 1 A)):
    rescale (-1) (inverseScale A)= -inverseScale A:=by
  -- injectivity after composing by inverse 
  have hA := odd_has_zero h
  let B:=inverseScale A
  let x:= -X (R:=ℝ)
  have H : (PowerSeries.subst A B)=X := by
    dsimp only [B, inverseScale]; rw [dif_pos ha];exact A.subst_substInvOfIsUnit_left hA ha
  have H' : (PowerSeries.subst B A)=X := by
    dsimp only [B, inverseScale]; rw [dif_pos ha]; exact A.subst_substInvOfIsUnit_right hA ha
  have hu:=good A hA
  have hv:=good B (inverse_zero A)
  have hw:=good x (by simp [x])
  have hf : ∀ p:fps,rescale (-1) p = PowerSeries.subst x p := by intro p;convert rescale_eq_subst (R:=ℝ) (-1) p using 2; simp [x]
  have he (u v : fps)(h : PowerSeries.subst A u=PowerSeries.subst A v) : u=v:=by
     obtain h := congr_arg (PowerSeries.subst B) h
     simp_rw [subst_comp_subst_apply hu hv _] at h
     rw [H'] at h; simpa using! h
  apply (he (rescale (-1) B) (-B))
  rw [hf, subst_comp_subst_apply hw hu]
  have h' : subst A x= -A:=by unfold x; rw [←coe_substAlgHom (R:=ℝ) hu,map_neg,coe_substAlgHom,subst_X hu]
  rw [h', ← h, hf, ← subst_comp_subst_apply hu hw, ← coe_substAlgHom (R:=ℝ) hu,map_neg,coe_substAlgHom,H,PowerSeries.subst_X hw]

variable (w:Mark J shape→ℕ) 
structure SignContract : Prop where
  triple : Odd (w T.triples)
  basket (i : Fin 3): Odd (w (T.pair i)+w (T.one i))
  singleton : Odd (∑ i,w (T.one i))

-- sign-compatible coupling convention at every coefficient
lemma coupling_odd {a : Mark J shape→fps} (h: T.SignContract w)(hp : parity w a) :
    rescale (-1) (T.parameter a) = -T.parameter a := by
   suffices H: rescale (-1) (T.connected a)= -T.connected a by
     have hz := odd_has_zero H
     simp [parameter,deviation,hz,H]; left
     rw [rescale_eq_subst]; exact subst_C _
   have he i : rescale (-1) (a (T.pair i) * a (T.one i))= -(a (T.pair i)*a (T.one i)) := by
       rw [map_mul,hp,hp, mul_assoc ( (-1:fps)^_) (a (T.pair i)) _,mul_left_comm (a (T.pair i)) ((-1:fps)^_) _,← mul_assoc, ← pow_add, (h.basket i).neg_pow,one_pow,neg_one_mul]
   have ht : rescale (-1) (∏ i,a (T.one i)) = -∏ i,a (T.one i):= by
       unfold parity at hp
       rw [map_prod,Finset.prod_congr rfl (show ∀ i∈Finset.univ,rescale (-1) (a (T.one i))=(-1:fps)^(w (T.one i))*a (T.one i) from fun i _=> hp _), Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,h.singleton.neg_pow]; simp
   simp only [connected,map_add,map_sub,map_sum,he,hp T.triples,h.triple.neg_pow,one_pow,neg_one_mul,map_mul,ht,map_ofNat, Finset.sum_neg_distrib]; ring

theorem carries_parity {a:Mark J shape→fps}(hw : T.SignContract w)(h : coeff 1 (T.connected a)≠0)(hp : parity w a): parity w (T.remeasured a):=by
  let B:=inverseScale (T.parameter a)
  have hB : rescale (-1) B= -B:=rescale_inverse_odd (T.coupling_odd w hw hp) (T.linearTest a |>.2 h)
  have hu:=good B (inverse_zero _)
  let x : fps := (-1:ℝ) • X
  have hx : ∀ p:fps,rescale (-1) p=PowerSeries.subst x p:=rescale_eq_subst (-1)
  have hv:=good x (by simp [x])
  intro i
  change rescale (-1) (PowerSeries.subst B _) = _
  rw [hx,subst_comp_subst_apply hu hv,←hx,hB,show -B=PowerSeries.subst B x from by simp only [x, neg_smul,one_smul,← coe_substAlgHom hu,map_neg, coe_substAlgHom,subst_X hu],
      ← subst_comp_subst_apply hv hu,←hx, hp i, ← coe_substAlgHom (R:=ℝ) hu,map_mul,map_pow,map_neg,map_one,coe_substAlgHom hu]
  rfl

end Triangle
end YM.PertExtension.Position
