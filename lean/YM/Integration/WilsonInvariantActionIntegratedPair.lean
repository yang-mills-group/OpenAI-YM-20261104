import YM.Integration.WilsonInvariantActionPairMarginals

/-! Signed tested extraction of the actual conditional and inherited
covariances of two upper nonlinear Wilson observables. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionIntegratedPair
open Filter Function Set MeasureTheory Table Spec Climb Maxwell Maxwell.Free
open Next.UVStress PhysicalNext.Repeat.Legato Lattice RG Wilson RGComparison.Core16
open Extraction Extraction.Order Push.GridApprox OPE OPE.Orbits OPE.Therm
open WilsonInvariantActionPairCovariance WilsonInvariantActionPairMarginals
open WilsonMacroscopicForwardTransfer
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {N p u : ℕ}

private def tags (a b : R.family.label 4) : Fin 2→R.family.book.Token :=
  fun i=>⟨4,Fin.cons (α:=fun _:Fin 2=>R.family.label 4) a (fun _=>b) i⟩

def posterior (T : Slices R.family.path.levels p) (h : u≤N) (a b : R.family.label 4)
    (x : Fin 2→Site (R.family.side N p)) : ℂ :=
  let X:=R.family.O N p a (x 0)
  let Y:=R.family.O N p b (x 1)
  let law:=scene R.family.path N p u
  let A:=WilsonInvariantActionPairPosterior.held R T h X
  let B:=WilsonInvariantActionPairPosterior.held R T h Y
  let pair:=WilsonInvariantActionPairPosterior.held R T h (fun U=>X U*Y U)
  (∫V,pair V-A V*B V ∂law)+((∫V,A V*B V ∂law)-(∫V,A V ∂law)*(∫V,B V ∂law))

private theorem product (a b : R.family.label 4) (x : Fin 2→Site (R.family.side N p)) :
    R.family.numeric N p (tags R a b) x=
      ∫U,R.family.O N p a (x 0) U*R.family.O N p b (x 1) U ∂scene R.family.path N p N := by
  rw [top (C:=R.family) R.makes N p,Family.num]
  simp [tags,Family.seen,Fin.prod_univ_two]

theorem finite (T : Slices R.family.path.levels p) (h : u≤N) (a b : R.family.label 4)
    (x : Fin 2→Site (R.family.side N p)) :
    posterior R T h a b x=R.family.numeric N p (tags R a b) x-single R a (x 0)*single R b (x 1) := by
  rw [product,marginal,marginal]
  exact (WilsonInvariantActionPairPosterior.original R T h a b (x 0) (x 1)).symm

private theorem inserted (hn : R.family.ref 4≤N) (b : R.family.label 4) (x : Fin 2→Site (R.family.side N p)) :
    R.family.numeric N p (tags R (R.family.refUnit 4) b) x=single R b (x 1) := by
  rw [product,marginal,R.family.constant R.makes 4 hn (x 0)]
  simp

def profile (cut : (N p:ℕ)→Fin (N+1)) (a b : R.family.label 4) (φ : Test 2) (N p : ℕ) : ℂ :=
  (R.family.S.a N:ℂ)^(4*2) * ∑x:Fin 2→Site (R.family.side N p),φ (cells R.family N p x) *
    posterior R (someSlices R.family.path.levels p) (Nat.le_of_lt_succ (cut N p).isLt) a b x

private theorem recorded (cut : (N p:ℕ)→Fin (N+1)) (a b : R.family.label 4) (φ : Test 2)
    (hn : R.family.ref 4≤N) :
    profile R cut a b φ N p=smears R.family N p (tags R a b) φ-
      single R a (0:Site (R.family.side N p))*smears R.family N p (tags R (R.family.refUnit 4) b) φ := by
  let T:=someSlices R.family.path.levels p
  let h:=Nat.le_of_lt_succ (cut N p).isLt
  have term (x : Fin 2→Site (R.family.side N p)) :
      φ (cells R.family N p x)*posterior R T h a b x=
      φ (cells R.family N p x)*R.family.numeric N p (tags R a b) x-
       single R a (0:Site (R.family.side N p))*
        (φ (cells R.family N p x)*R.family.numeric N p (tags R (R.family.refUnit 4) b) x) := by
    rw [finite,translation R hn a (x 0),inserted R hn]
    ring
  have summed :
      (∑x:Fin 2→Site (R.family.side N p),φ (cells R.family N p x)*posterior R T h a b x)=
      (∑x:Fin 2→Site (R.family.side N p),φ (cells R.family N p x)*R.family.numeric N p (tags R a b) x)-
       single R a (0:Site (R.family.side N p))*
        ∑x:Fin 2→Site (R.family.side N p),φ (cells R.family N p x)*R.family.numeric N p (tags R (R.family.refUnit 4) b) x := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _=>term x
  unfold profile smears
  rw [show someSlices R.family.path.levels p=T from rfl,summed]
  ring

variable {R} {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)

include F in
private theorem use (a b : R.family.label 4) {x : Points 2} (hx : x∈conf 2) :
    S.read x (tags R a b)=slot (S.project 4 b) x (S.project 4 a) := by
  rw [placed]
  have native:= S.class_agrees S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) (fun _:Fin 2=>4) hx
    (fun i=>Fin.cons (α:=fun _:Fin 2=>R.family.label 4) a (fun _=>b) i)
  apply native.symm.trans
  congr 1
  funext i
  fin_cases i <;> rfl

include F in
theorem ordered (cut : (N p:ℕ)→Fin (N+1)) (φ : Test 2) {r : ℝ} (rp : 0<r) (y b : S.Field 4) :
    f.limits (fun p=>suitable R.family.S p (dilate rp φ))
      (profile R cut (S.representative 4 y) (S.representative 4 b) (dilate rp φ))
      (WilsonInvariantActionPairCovariance.tested y b r φ) := by
  let first:=S.representative 4 y
  let second:=S.representative 4 b
  let id:=R.family.refUnit 4
  let t:=dilate rp φ
  let value (a:R.family.label 4) (x:Points 2):=S.read (r•x) (tags R a second)
  have raw (a:R.family.label 4) : f.limits (fun p=>suitable R.family.S p t)
      (fun N p=>smears R.family N p (tags R a second) t) (φ.applyTo (value a)) := by
    have reading:=F.room.ordered.reads 2 (tags R a second) (dilate rp φ)
    rw [zoom_integral] at reading
    exact reading
  have cash (a:R.family.label 4) : Integrable (fun x=>φ x*value a x) :=
    φ.smearing ((S.smooth_read F.room.kernel.smooth _).continuousOn.comp (by fun_prop) (fun _ hx=>Work.A05.smul_conf rp hx))
  have result : φ.applyTo (value first)-expectation S 4 y*φ.applyTo (value id)=
      WilsonInvariantActionPairCovariance.tested y b r φ := by
    unfold WilsonInvariantActionPairCovariance.tested Test.applyTo
    rw [←integral_const_mul,←integral_sub (cash first) ((cash id).const_mul _)]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx:x∈tsupport (φ:Points 2→ℂ)
    · have sep:=Work.A05.smul_conf rp (φ.tsupport_subset hx)
      dsimp only [value]
      rw [use F _ _ sep,use F _ _ sep,connected F _ _ sep,←placed]
      have one : S.project 4 id=S.unit 4:=rfl
      simp only [id,one,first,second,S.rep,unit F b sep]
      ring
    · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul,zero_mul,zero_mul,mul_zero,sub_zero]
  rw [←result]
  obtain ⟨existsP,fin,inner,outer⟩:=raw first
  obtain ⟨_,unitFin,unitInner,unitOuter⟩:=raw id
  obtain ⟨_,oneFin,oneInner,oneOuter⟩:=converge F y
  refine ⟨existsP,fun p=>fin p-oneFin p*unitFin p,fun p hp=>?_,outer.sub (oneOuter.mul unitOuter)⟩
  apply ((inner p hp).sub ((oneInner p trivial).mul (unitInner p hp))).congr'
  filter_upwards [f.mesh.cofinal.eventually (eventually_ge_atTop (R.family.ref 4))] with k hk
  exact (recorded R cut first second t hk).symm

end YM.Integration.WilsonInvariantActionIntegratedPair
