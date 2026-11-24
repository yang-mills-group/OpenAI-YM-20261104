import YM.XSpace.ComplexDiagrams
import YM.XSpace.Division
import YM.Next.FOUNDATIONS.Primary
import YM.Next.RANK.GlowLine

/-!
# Top input columns

`canonical` is independent of any solution of flow equations. `birth` is a
Taylor expansion of the *same* stencil, divided by exactly the slot-count
g power. `first` presents its degree-zero coefficient in linear plaquette
variables using the local `pop` representation. It still needs conversion by
the cover Wick-jet calibration; we are NOT using a continuum Wick
subtraction on these stencils!
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Set Filter MeasureTheory Lattice Wilson Source
open Next.Foundations Next.Rank Gauss Formal
open scoped Topology InnerProductSpace BigOperators ContDiff Matrix.Norms.Frobenius Classical

abbrev AKey := Beamer.Address
abbrev Frame (G : Gauge) (d : ℕ) := (Labels.frames G).level d
abbrev authors (G : Gauge) (d : ℕ) := Next.Foundations.localSection G d
abbrev Index (G : Gauge) (d : ℕ) := (Frame G d).Index

section germ
variable {G : Gauge}
lemma curl_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E)
    (V : E→G.El) (h : ContDiffAt ℝ ⊤ (fun y=>G.mat (V y)) x) : ContDiffAt ℝ ⊤ (G.curvature ∘ V) x := by
  change ContDiffAt ℝ ⊤ (fun y=> G.projectColor ((1/2:ℝ) • (G.mat (V y)-G.mat (V y)⁻¹))) x
  simp_rw [G.mat_inv]; exact G.projectColor.toContinuousLinearMap.contDiff.contDiffAt.comp x ((h.sub ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ h)).const_smul _)

-- A based Slot is exactly a curvature of a transported loop
lemma slot_eval {U : CoverConfig G} (s : RG.Slot) : s.eval U= G.curvature
    (travel U 0 s.walk * faceValue U (s.offset,s.plaq) * (travel U 0 s.walk)⁻¹) :=
  (G.curvature_conjugate _ _).symm
end germ

variable {G : Gauge} {d : ℕ}
structure Words (i : Index G d) where
  n : ℕ
  slots : Fin n → RG.Slot
  pose : Bid.Pose G n
  inside j : (slots j).stencil ⊆ (authors G d).stencil
  past : (authors G d).evaluate (Pi.single i 1)=Bid.lumin pose ∘ Bid.mapped slots
  starts : Bid.lows pose ((Frame G d).grades i).2

lemma written (i : Index G d) : Nonempty (Words i) := by
  obtain ⟨n,B,hb,P,H,F⟩ := valuation G d i; exact ⟨⟨n,B,P,hb,H,F⟩⟩

def chosen (i : Index G d) := Classical.choice (written i)
def locus (s : RG.Slot) (c : G.ColorIndex) : AKey G := (s.offset,s.plaq,c)
def ground {i : Index G d} (s : Words i) := MvPolynomial.rename (fun j:Fin s.n×G.ColorIndex=> locus (s.slots j.1) j.2)
    (homogeneousPart' s.pose ((Frame G d).grades i).2)

namespace Regulator.Tree
variable {R : Regulator} (T : R.Tree)

def cylinder (o : R.LSite) (A : T.Array G) := expandAt o (R.Lift (T.expLinks A))

def target (s : RG.Slot) (o : R.LSite) := wrap R.side s.offset+o

-- the two transports in slot_eval
lemma into_slot (o : R.LSite) (w : Walk) (x : Cover) : ContDiffAt ℝ ⊤ (fun A:T.Array G=> G.mat (travel (T.cylinder o A) x w)) 0 := by
  have he (e : R.LEdge) : ContDiffAt ℝ ⊤ (fun A : T.Array G=> G.mat (R.Lift (T.expLinks A) e)) 0 := by
    simp_rw [lift_expLinks]
    apply ContDiffAt.comp (g:=fun z=>G.mat (G.lieExp z)) _ G.exp_jet.contDiffAt
    exact (contDiffAt_apply ..).comp _ (T.periodic G).toContinuousLinearMap.contDiff.contDiffAt
  simp_rw [cylinder, travel_at, ← Work.F02.stringMat_physical]
  exact ((Work.F02.stringMat_contDiff (G:=G) _ _).restrict_scalars ℝ).contDiffAt.comp _ (Work.F02.physical_contDiffAt he)

def slotCurve (s : RG.Slot) (o : R.LSite) (A : T.Array G) := s.eval (T.cylinder o A)

lemma into_curve (s : RG.Slot) (o : R.LSite) : ContDiffAt ℝ ⊤ (T.slotCurve (G:=G) s o) 0 := by
  unfold slotCurve; simp_rw [slot_eval]; refine curl_smooth 0 (V:=fun A=>_) ?_
  simp_rw [G.mat_mul,G.mat_inv]; exact ((T.into_slot o _ _).mul (T.into_slot o _ _)).mul ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (T.into_slot o _ _))

@[simp] lemma slot_empty (s : RG.Slot) (o : R.LSite) : T.slotCurve s o (0:T.Array G)=0 := by
  rw [slotCurve,slot_eval]; unfold cylinder faceValue; simp_rw [travel_at]
  have he (x : R.LSite) (w : Walk) : travel (R.Lift (T.expLinks (G:=G) 0)) x w=1 := by
    simpa only [zero_smul] using T.cost_zero (G:=G) 0 w x
  simp_rw [he]; simp [Gauge.curvature_unit]

def slotMark (s : RG.Slot) (o : R.LSite) (c : G.ColorIndex) (A : T.Array G) := (↑(T.slotCurve s o A c):ℂ)

lemma slot_live (s : RG.Slot) o (c : G.ColorIndex) : ContDiffAt ℝ ⊤ (T.slotMark s o c) 0 :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((EuclideanSpace.proj (𝕜:=ℝ) c).contDiff.contDiffAt.comp _ (T.into_curve s o))

lemma bend (s : RG.Slot) (o) (A : T.Array G) :
    HasDerivAt (fun t : ℝ=> T.slotCurve s o (t • A)) (field (T.periodic G A) (target s o,s.plaq)) 0 := by
  unfold slotCurve; simp_rw [slot_eval,cylinder,faceValue,travel_at]
  refine Work.F03.curvature_of_hasDerivAt (V:=fun t=>_) ?_
  have he := T.line_tangent A (wrap R.side s.offset+o) (square s.plaq.val.1 s.plaq.val.2)
  rw [T.line_face] at he
  have ht := T.line_tangent A (wrap R.side 0 + o) s.walk
  simp_rw [G.mat_mul,G.mat_inv]; refine ((ht.mul he).mul ht.star).congr_deriv ?_
  simp only [Pi.mul_apply,T.cost_zero,G.mat_one,star_one,mul_one,one_mul,G.colorMat_skew,target,field]; abel

lemma born (s : RG.Slot) (o : R.LSite) (c : G.ColorIndex) :
    let p:= JetC (T.basisT G) (T.slotMark s o c)
    PowerSeries.coeff 0 p=0 ∧ PowerSeries.coeff 1 p=T.evaluateF G (MvPolynomial.X ((target s o,s.plaq),c)) := by
  intro p; refine ⟨?_,?_⟩
  · unfold p; rw [jet_zero]; simp [slotMark]
  apply using_test (T.basisT G); intro A
  unfold p; rw [jet_ray (T.basisT G) _ _ ((T.slot_live s o c).of_le le_top),T.substitute_apply]; simp only [Nat.factorial_one,Nat.cast_one, inv_one,one_mul, iteratedDeriv_one, MvPolynomial.aeval_X]
  exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 ((EuclideanSpace.proj (𝕜:=ℝ) c).hasFDerivAt.comp_hasDerivAt _ (T.bend s o A))).deriv

def canonical (o : R.LSite) (i : Index G d) (A : T.Array G) := (authors G d).evaluate (Pi.single i 1) (T.cylinder o A)
def birth (o : R.LSite) (i : Index G d) := pullOut ((Frame G d).grades i).2 (JetC (T.basisT G) (T.canonical o i))

def imprint (o : R.LSite) (k : AKey G) : FKey G R.side := ((wrap R.side k.1+o,k.2.1),k.2.2)

def factorsOf {i : Index G d} (s : Words i) (o : R.LSite) (j: Fin s.n×G.ColorIndex):= T.slotMark (s.slots j.1) o j.2
lemma canonical_comb {i : Index G d} (s : Words i) (o:R.LSite) : T.canonical o i= combine (T.factorsOf s o) s.pose := funext fun x=>by unfold canonical; rw [s.past]; rfl
lemma stencil_live (o : R.LSite) (i : Index G d) : ContDiffAt ℝ ⊤ (T.canonical o i) 0 := by
  rw [T.canonical_comb (chosen i)]; exact lush _ (fun _=>T.slot_live ..) _
lemma birth_jet {i:Index G d} (s : Words i) (o:R.LSite) : JetC (T.basisT G) (T.canonical o i)=
    MvPolynomial.eval₂Hom (PowerSeries.C.comp MvPolynomial.C) (fun j=>JetC (T.basisT G) (T.factorsOf s o j)) s.pose:= by
  rw [T.canonical_comb s]; exact jet_combine (T.basisT G) (T.factorsOf s o) (fun _=>T.slot_live ..) _
lemma birth_div {i:Index G d} (s : Words i) (o:R.LSite) : PowerSeries.X^((Frame G d).grades i).2 ∣ JetC (T.basisT G) (T.canonical o i) := by
  rw [T.birth_jet s]
  apply pull_div MvPolynomial.C (fun j => JetC (T.basisT G) (T.factorsOf s o j)) _ s.pose _ (show ∀ _, _ from s.starts)
  intro j; exact (T.born (s.slots j.1) o j.2).1
lemma birth_keeps (o : R.LSite) (i : Index G d) : T.birth o i*PowerSeries.X^((Frame G d).grades i).2 = JetC (T.basisT G) (T.canonical o i) :=
  (reorder _ _ (T.birth_div (chosen i) o)).symm
lemma lead_pose (o:R.LSite) (i:Index G d) (s:Words i) : PowerSeries.constantCoeff (T.birth o i)=
    MvPolynomial.eval₂Hom MvPolynomial.C (fun j=>PowerSeries.coeff 1 (JetC (T.basisT G) (T.factorsOf s o j))) (homogeneousPart' s.pose ((Frame G d).grades i).2) := by
  rw [birth,T.birth_jet s]; exact pull_read MvPolynomial.C (fun j => JetC (T.basisT G) (T.factorsOf s o j)) (fun j => (T.born (s.slots j.1) o j.2).1) _ _ (show ∀ _, _ from s.starts)
lemma first (o : R.LSite) (i : Index G d) (s : Words i) : PowerSeries.constantCoeff (T.birth o i) = T.evaluateF G (MvPolynomial.rename (imprint o) (ground s)) := by
  let f (j:Fin s.n × G.ColorIndex):= PowerSeries.coeff 1 (JetC (T.basisT G) (T.factorsOf s o j))
  let g : Fin s.n × G.ColorIndex → AKey G:= fun j=> locus (s.slots j.1) j.2
  have he : MvPolynomial.aeval (R:=ℂ) f=(T.evaluateF G).comp ((MvPolynomial.rename (imprint o)).comp (MvPolynomial.rename g)):= by
    ext1 j
    simp only [MvPolynomial.aeval_X,AlgHom.comp_apply,MvPolynomial.rename_X]
    exact (T.born (s.slots j.1) o j.2).2
  rw [T.lead_pose o i s]; exact DFunLike.congr_fun he (homogeneousPart' s.pose ((Frame G d).grades i).2)
end Regulator.Tree
end YM.XSpace
