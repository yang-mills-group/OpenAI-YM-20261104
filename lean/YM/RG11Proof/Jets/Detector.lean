import YM.RG11Proof.Jets.Pencil
/-!
# Finite detector from free orbit and coupling transversality

Joint variation on one common field horizon is finite-dimensional even though
the *separated tests* need not be finite-dimensional. Use with genuine
permitted orbit (on independent basis; for a redundant list one cannot
assume `Free` here; descend first). All linear functionals for `RulerTest`
are displayed finite combinations. e.g. any sign, real-part, connected at
first derivative etc must actually prove these conditions on the linear pencil.
Existence on independent Yang--Mills arrays (orbit `Free` and slope response from
first order) is not automatic. No use of finite-dimensional quantitative inverse
across growing source demand. -/

set_option autoImplicit false
noncomputable section
namespace YM.RG11.Jets
open PowerSeries YM.PertExtension.Position
open scoped Classical BigOperators

section detector
variable {R J P : Type*} [Field R] [Fintype J]
variable {arity:P→ℕ}

abbrev Step (L : Constraints R J) := L.vary × R

def fullRead (L : Constraints R J) (A : ArrayAt J R arity) : Step L →ₗ[R] (Mark J arity→R) :=
  LinearMap.pi fun v => (pencil A v).comp (L.vary.subtype.prodMap LinearMap.id)

theorem fullRead_eq (L : Constraints R J) (A : ArrayAt J R arity) (z : Step L) (v) :
    fullRead L A z v =
    orbit (fun w=>constantCoeff (A w)) v z.1.val + tangent (A v)* z.2 := rfl

def Free (L : Constraints R J) (A : ArrayAt J R arity) : Prop :=
  ∀ z : L.vary, (∀ v, orbit (fun w=>constantCoeff (A w)) v z.val = 0) → z = 0

/-- One finite ruler test modulo allowed frame redefinitions. -/
structure RulerTest (L : Constraints R J) (A : ArrayAt J R arity) where
  m : ℕ
  tests : Fin m→ Mark J arity
  meter : (Fin m→R)→ₗ[R] R
  zeroX (X : L.vary) : meter (fun i=> orbit (fun w=>constantCoeff (A w)) (tests i) X.val)=0
  unitSlope : meter (fun i=> tangent (A (tests i)))=1

def Sees (L : Constraints R J) (A : ArrayAt J R arity) : Prop :=
  Function.Injective (fullRead L A)

-- If the ruler test first slope is a fixed nonzero s instead, divide the
-- meter by s before using the frame pencil. This doesn't justify any preferred
-- relation of leading slopes *between* prescriptions by itself.
namespace RulerTest
variable {L : Constraints R J} {A : ArrayAt J R arity}

def ofSlope {m : ℕ} {tests : Fin m→ Mark J arity} (meter : (Fin m→R)→ₗ[R] R)
    (hb : ∀ X : L.vary, meter (fun i=> orbit (fun w=>constantCoeff (A w)) (tests i) X.val)=0)
    {s : R} (hs : s≠0) (h : meter (fun i=> tangent (A (tests i)))=s) : RulerTest L A where
  m := m
  tests := tests
  meter := s⁻¹ • meter
  zeroX _ := by rw [LinearMap.smul_apply,hb,smul_zero]
  unitSlope := by rw [LinearMap.smul_apply,h,smul_eq_mul,inv_mul_cancel₀ hs]

theorem reads (T : RulerTest L A) (x : Step L) : T.meter (fun i=> fullRead L A x (T.tests i)) = x.2 := by
  have he : (fun i=>fullRead L A x (T.tests i)) =
     (fun i=> orbit (fun w=>constantCoeff (A w)) (T.tests i) x.1.val) +
        x.2 • (fun i=> tangent (A (T.tests i))) := funext fun i=> by simp [fullRead_eq,mul_comm]
  rw [he,map_add,T.zeroX,map_smul,T.unitSlope,zero_add,smul_eq_mul,mul_one]
end RulerTest

namespace Sees
variable {L : Constraints R J} {A : ArrayAt J R arity}

theorem of_parts (h : Free L A) (T : RulerTest L A) : Sees L A := by
  refine LinearMap.ker_eq_bot.mp ((LinearMap.ker_eq_bot' (f:=fullRead L A)).mpr ?_)
  intro x hx
  have hz : x.2 = 0 := by
    rw [← T.reads x, hx]; exact map_zero T.meter
  have hw v := congrFun hx v
  simp only [fullRead_eq,hz,mul_zero,add_zero] at hw
  exact Prod.ext (h _ hw) hz

/-- Can rely on an explicit finite detector or prove separated orbit rank on
point configurations first (that still needs a continuity/profile adapter to
match a separated profile input). -/
theorem finite {L : Constraints R J} {A : ArrayAt J R arity} (h : Sees L A) :
    ∃ (m : ℕ) (test : Fin m → Mark J arity), Function.Injective
      (LinearMap.pi fun i=> (LinearMap.proj (R:=R) (φ:=fun _ : Mark J arity=>R) (test i)).comp
        (fullRead L A)) := by
  let K (v : Mark J arity) := (LinearMap.proj (R:=R) (φ:=fun _ : Mark J arity=>R) v).comp (fullRead L A)
  obtain ⟨s,hs,he,-⟩ := Submodule.exists_fun_fin_finrank_span_eq R (Set.range K)
  choose test ht using hs
  let E := LinearMap.pi fun i => K (test i)
  refine ⟨_,test,LinearMap.ker_eq_bot.mp ((LinearMap.ker_eq_bot' (f:=E)).mpr ?_)⟩
  intro x hx
  have hp v (hv : v∈ Submodule.span R (Set.range K)) : v x = 0 := by
    rw [←he] at hv
    induction hv using Submodule.span_induction with
    | mem v hv => obtain ⟨j,rfl⟩ := hv; rw [←(show K (test j)=_ from ht j)]; exact congrFun hx j
    | zero => rfl
    | add _ _ _ _ h1 h2 => exact congr_arg₂ (·+·) h1 h2 |>.trans (add_zero _)
    | smul r _ _ h1 => rw [LinearMap.smul_apply,h1,smul_zero]
  apply h
  rw [map_zero]; exact funext fun v=> hp (K v) (Submodule.subset_span ⟨v,rfl⟩)
end Sees

/-- Finite joint detector with left inverse. The tests are actual slot marks
through this field horizon; cross-order compatibility comes from using the same
tests and the same free/first array, not independent choices. -/
structure Detector (L : Constraints R J) (A : ArrayAt J R arity) where
  m : ℕ
  test : Fin m → Mark J arity
  restore : (Fin m→ R) →ₗ[R] Step L
  works (x : Step L) : restore (fun i=> fullRead L A x (test i))=x

namespace Detector
variable {L : Constraints R J} {A B : ArrayAt J R arity}

def ofSees (h : Sees L A) : Detector L A := by
  apply Classical.choice
  obtain ⟨m,test,hs⟩:=Sees.finite h
  let K : Step L →ₗ[R] (Fin m→R) := LinearMap.pi fun i=> (LinearMap.proj (R:=R) (φ:=fun _ : Mark J arity=>R) (test i)).comp (fullRead L A)
  obtain ⟨f,hf⟩ := LinearMap.exists_leftInverse_of_injective (V':=Fin m→R) K (LinearMap.ker_eq_bot.mpr hs)
  exact ⟨⟨m,test,f,fun x=> LinearMap.congr_fun hf x⟩⟩

theorem sees (T : Detector L A) : Sees L A := fun x y h=>
   (T.works x).symm.trans (Eq.trans (by rw [h]) (T.works y))

-- Detector compatibility when using array A instead of B before independent
-- construction through higher orders: detector depends ONLY through power 1.
def ofFirst (T : Detector L A)
    (h : ∀ v, Through 1 (A v) (B v)) : Detector L B :=
  { m := T.m
    test := T.test
    restore := T.restore
    works := fun x=>by
      have he v : fullRead L B x v=fullRead L A x v := by
        simp only [fullRead_eq, orbit,tangent]
        simp_rw [show ∀ (v:Mark J arity),constantCoeff (B v)=_ from fun v=> (h v).head.symm,
          show coeff 1 (B v)=_ from (h v 1 le_rfl).symm]
      exact (congrArg T.restore (funext fun _=> he _)).trans (T.works x) }
end Detector
end detector
end YM.RG11.Jets
