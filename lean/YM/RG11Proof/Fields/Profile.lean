import YM.RG11Proof.Fields.Guard

/-!
# Profile readout in real coordinates, through any fixed horizon

Two useful adapters: finite *constant* piece of a common regulator's frame
using ACTUAL reflected Gram detector nondegeneracy in the free quotient, and
finite simultaneous shift rank via the actual `Frozen` property (not just a
label or an unspecified local operators class). Sparse separated profiles
must still be announced in the regulator/window estimates on ALL listed
coordinates. Leading result about that same physical free quotient does not
imply any MS_lift, Wilson capture, Diagram or interacting equality at
coefficient one, even if those reports are subsequently fed as a `rowReport`
into these API.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.RG11.Fields
open PowerSeries YM.RG11.Jets YM.RG11.Formal Labels PertExtension.Position Maxwell Extra.FD Pert.Position Function
open scoped Classical BigOperators
variable {G : Gauge} {F : Frames G} {d : ℕ} (B : Basis F d)

-- first actual binding of Gram-leading criterion (through announced h, actual
-- free fields and paired profile). Covers any admissible pure-YM G, given
-- `Hierarchy` free provider. Consumer must supply the raw identity onward.
theorem checks_leading {α} (B:Adapted F d) (H:(freeTable F).Hierarchy) (a:Axis) :
  ∃ f:Test 2,
    Bridge.Positive (freePair B.toBasis f) (frameMirror B.toBasis a) ∧
    ∀ (k:Rate.Budget α) (A : ArrayAt B.toBasis.J ℝ Bridge.two)
      (V D : α→ ArrayAt B.toBasis.J ℝ Bridge.two)
      (T : α→Change ℝ B.toBasis.J) (Y:Finset (Mark _ Bridge.two)),
      (∀ b, Anchored (T b).g) →
      (∀ i j, constantCoeff (A (Bridge.pair i j))=freePair B.toBasis f i j) →
      (∀ i j, level B j < level B i → Bridge.pair i j∈Y) →
      Bridge.Saves k 0 Y V D T →
      (∀ i j,Bridge.Crest k 0 V A (Bridge.pair i j)) →
      (∀ i j,level B j<level B i →Bridge.Crest k 0 D A (Bridge.pair i j)) →
      (∀ i j,level B i≤level B j →Rate.Near k (fun b=>Jets.piece 0 (T b).Z i j) ((1 : Square B.toBasis.J ℝ) i j)) →
      ∀ i,Bridge.Done k (fun b=>Jets.piece 0 (T b).Z) i:=by
  obtain ⟨f,hf⟩:= positive_profile B.toBasis H a
  exact ⟨f,hf,fun k A V D T Y hT hp=> Bridge.leading_of_paired A V D _ T hT _
      (fun _ _=>mirror_level B a) (by convert hf; exact Matrix.ext fun i j=> hp i j) Y⟩

-- Use all profiles (complex Test, but reading real part). From rank on the
-- tested leading orbit this returns a `Detector` on REAL price coordinates.
structure Place where
  order : ℕ
  test : Test order

abbrev form : Place→ℕ:=Place.order
abbrev point (B:Basis F d) := Mark B.J form

def rowZero (v:point B):ℝ:= (wickReading F d (v.1.test) (fun i=>B.b (v.2 i))).re

-- index transport in all slots.
def sends {n} (X:E F d→ₗ[ℂ] E F d) (k : Fin n) (i:Fin n) : E F d →ₗ[ℂ] E F d := if k=i then X else LinearMap.id

def firstColumn (M:Square B.J ℝ) (p:Place) : MultilinearMap ℂ (fun _:Fin (form p)=>E F d) ℂ :=
    ∑ i:Fin (form p),(wickReading F d p.test).compLinearMap (sends (B.liftRows M) i)

theorem column_apply (M:Square B.J ℝ) (p:Place) (v:Fin p.order → E F d):
    firstColumn B M p v=∑ i:Fin p.order, wickReading F d p.test (Function.update v i (B.liftRows M (v i))) := by
   change (∑ i:Fin p.order,(wickReading F d p.test).compLinearMap (sends _ i)) v=_
   rw [_root_.sum_apply]; apply Finset.sum_congr rfl; intro j hj
   simp only [MultilinearMap.compLinearMap_apply]; congr 1; funext l
   by_cases ht:j=l
   · subst j; simp [sends]
   simp [sends,ht, Function.update_of_ne (Ne.symm ht)]

theorem price_orbit (v:point B) (Z:Square B.J ℝ): orbit (rowZero B) v Z=(firstColumn B Z v.1 (fun i=>B.b (v.2 i))).re := by
   rw [column_apply,Complex.re_sum]
   unfold orbit rowZero
   apply Finset.sum_congr rfl; intro i _
   let b : Fin (v.1.order)→E F d:=fun j=>B.b (v.2 j)
   let W:= wickReading F d v.1.test
   let L:= W.toLinearMap b i
   have he h : W (Function.update b i h)=L h := rfl
   have hv t : (fun j:Fin (v.1.order)=> B.b (Function.update v.2 i t j))=Function.update b i (B.b t):= by
     funext j; by_cases h:j=i
     · subst i; simp
     rw [Function.update_of_ne h, Function.update_of_ne h]
   change (∑ j, Z (v.2 i) j * (W (fun l=>B.b (Function.update v.2 i j l))).re)= (W (Function.update b i (B.liftRows Z _))).re
   simp_rw [show B.liftRows Z (B.b (v.2 i)) = _ from B.row_basis Z (v.2 i),Basis.put_sum, hv,he,map_sum,Complex.re_sum,map_smul,smul_eq_mul,Complex.re_ofReal_mul]

-- `Frozen` quantifies all continuous point readings; the detector needs only
-- finitely many compact tests, not a test that uses the unknown perturbative
-- or actual system when choosing locations.
theorem free_from_frozen {A : ArrayAt B.J ℝ form} (ha : ∀ v,constantCoeff (A v)=rowZero B v)
    (hf : Frozen F d) : Jets.Free B.guard A:= by
  intro z hz
  have he : B.operates z=0 := by
    apply Pert.Position.detected F d hf
    intro q
    let p:Place:=⟨q.r,q.f⟩
    let M:= firstColumn B z.val p
    have hv (u:Fin (form p)→B.J): (M (fun i=>B.b (u i)))=0 := by
      -- real parts come from this profile; imaginary via i times this profile
      have hu (p:Place) (u:Fin (form p)→B.J): (firstColumn B z.val p (fun i=>B.b (u i))).re=0:= by
        have hh:= hz (⟨p,u⟩:point B)
        rw [show (fun w=>constantCoeff (A w))= rowZero B from funext ha, price_orbit] at hh
        exact hh
      have hh : (firstColumn B z.val ⟨p.order,Complex.I • p.test⟩ (fun i=>B.b (u i))) = Complex.I * M (fun i=>B.b (u i)):=by
        rw [column_apply,show M (fun i=>_) = _ from column_apply B z.val p (fun i=>B.b (u i)), Finset.mul_sum]
        change (∑ j:Fin p.order,(Complex.I • p.test).applyTo _) = _
        apply Finset.sum_congr rfl; intro j h
        exact price_scale ..
      apply Complex.ext
      · exact hu p u
      change (M _).im=0
      have ht := hu ⟨p.order,Complex.I • p.test⟩ u
      rw [hh,Complex.I_mul_re] at ht; exact neg_eq_zero.mp ht
    rw [feedback_eq]
    change Complex.re (∑ i:Fin (p.order), wickReading F d p.test
       (Function.update q.p i ((B.operates z).val (q.p i))))=0
    change Complex.re (∑ i:Fin (p.order), wickReading F d p.test (Function.update q.p i (B.liftRows z.val _))) = 0
    rw [← column_apply B z.val p q.p]
    have h : M q.p=0:= by
      conv_lhs=>rw [← funext fun j=> B.b.sum_equivFun (q.p j)]
      rw [MultilinearMap.map_sum_finset]; apply Finset.sum_eq_zero; intro j _
      rw [MultilinearMap.map_smul_univ,hv,smul_zero]
    rw [show firstColumn B z.val p _=0 from h]; rfl
  apply B.operates_inj
  rw [he]
  symm
  apply Subtype.ext
  have hz : B.realLift 0=0:= ContinuousLinearMap.ext fun p=>by rw [Basis.realLift,B.row_map_zero]; rfl
  exact hz
end YM.RG11.Fields
