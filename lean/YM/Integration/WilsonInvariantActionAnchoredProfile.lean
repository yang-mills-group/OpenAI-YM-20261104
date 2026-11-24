import YM.Integration.WilsonInvariantActionCoarseTrace

/-! The full signed original two-point integral admits an embedded Ward insertion at every
coarse scale. The joint conditional and its inherited covariance retain the same exterior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionAnchoredProfile
open Function Filter MeasureTheory Lattice Wilson RG RGComparison.Core16 Extraction Extraction.Order
open Table Spec PhysicalNext.Repeat.Legato MergeProof.Accent Push.GridApprox OPE OPE.Therm
open WilsonInvariantActionIntegratedPair WilsonInvariantActionPairMarginals WilsonInvariantActionPairPosterior
open private tags from YM.Integration.WilsonInvariantActionIntegratedPair
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {N p k u : ℕ}

def relative (j : Fin 2) (x : Fin 2→Site (R.family.side N p)) : Fin 2→Site (R.family.side N p) :=
  fun i=>x i-x j

theorem translate (T : Slices R.family.path.levels p) (h : u≤N) (hk : k≤N)
    (hn : R.family.ref 4≤N) (a b : R.family.label 4) (j : Fin 2)
    (x : Fin 2→Site (R.family.side N p)) :
    posterior R T h a b x=posterior R T hk a b (relative R j x) := by
  have positions : relative R j x=(fun i=>x i + -x j) :=
    funext fun i=>sub_eq_add_neg (x i) (x j)
  have pair : R.family.numeric N p (tags R a b) (relative R j x)=R.family.numeric N p (tags R a b) x := by
    rw [positions]
    exact R.family.anchored (p:=p) R.makes (tags R a b) (fun _=>hn) (-(x j)) x
  rw [finite,finite,pair,translation R hn a (x 0),translation R hn a (relative R j x 0),
    translation R hn b (x 1),translation R hn b (relative R j x 1)]

private theorem transfer (T : Slices R.family.path.levels p) (hk : k≤N)
    (X : Config G (R.family.side N p)→ℂ) :
    held R T hk X=actualTransport R.family (N:=N) X hk := by
  have chain (A : History G) (n p j : ℕ) (f : Config G (A.S.side j p)→ℂ) {i : ℕ} (h : i≤j) :
      gust A n p j f i h=pushTo A n p h f := by
    induction h using Nat.decreasingInduction with
    | self=>rw [gust_base,pushTo_self]
    | of_succ z hz ih=>rw [gust_step A n p j f hz,Birth.push_first A n p hz,ih]
  let β:=line R.family.path p k N
  have start : (fun U=>(R.family.path.rep N p N).eval U • X U)=
      ((bare (β (traversal T hk).depth) : Config G (R.family.side N p)→ℝ) • X) := by
    funext U
    change _=bare (line R.family.path p k N (traversal T hk).depth) U • X U
    have head : (R.family.path.rep N p N).eval U=bare (R.family.path.β N p N) U :=
      congrFun (R.makes.wilson.starts N p).2 U
    rw [head,bare_beta T hk]
  funext U
  unfold held Descent.conditioned Descent.weighted actualTransport
  rw [congrFun (vacuum_eq T R.makes.wilson hk) U,chain,WilsonMacroscopicRichDescentPosterior.output R.family.path p T hk,start]

def old (hk : k≤N) (a : R.family.label 4) (r δ : ℝ) (U : Config G (R.family.side k p)) : ℂ :=
  (((r/R.family.S.a k)^4/(4*δ):ℝ):ℂ)*
    ((WilsonInheritedRegisteredField.packet R.makes hk a (0:Site (R.family.side k p))).density 0
      (R.family.localSection 4) (R.family.path.rep N p k) U / ((R.family.path.rep N p k).eval U:ℂ))

private theorem first (T : Slices R.family.path.levels p) (hk : k≤N) (live : R.family.ref 4≤k)
    (a : R.family.label 4) (x : Fin 2→Site (R.family.side N p)) (r δ : ℝ)
    (U : Config G (R.family.side k p)) :
    ((r^4/(4*δ):ℝ):ℂ)*held R T hk (R.family.O N p a (relative R 0 x 0)) U=old R hk a r δ U := by
  have zero : (R.family.S.toDepth hk p).embed (0:Site (R.family.side k p))=0 :=
    (R.family.S.toDepth hk p).root.map_zero
  rw [transfer,show relative R 0 x 0=(R.family.S.toDepth hk p).embed 0 by simp [relative,zero]]
  exact WilsonInvariantActionCoarseTrace.embedded (R:=R) hk live a 0 U r δ

def contribution (T : Slices R.family.path.levels p) (hk : k≤N) (a b : R.family.label 4)
    (z : Site (R.family.side N p)) (r δ : ℝ) : ℂ :=
  let Y:=R.family.O N p b z
  let B:=held R T hk Y
  let joint:=held R T hk (fun U=>R.family.O N p a 0 U*Y U)
  let law:=scene R.family.path N p k
  (∫U,((r^4/(4*δ):ℝ):ℂ)*joint U-old R hk a r δ U*B U ∂law)+
  ((∫U,old R hk a r δ U*B U ∂law)-(∫U,old R hk a r δ U ∂law)*(∫U,B U ∂law))

private theorem withdraw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (C : ℂ)
    (A B J D : Ω→ℂ) (sold : ∀U,C*A U=D U) :
    C*((∫U,J U-A U*B U ∂μ)+((∫U,A U*B U ∂μ)-(∫U,A U ∂μ)*(∫U,B U ∂μ)))=
    (∫U,C*J U-D U*B U ∂μ)+((∫U,D U*B U ∂μ)-(∫U,D U ∂μ)*(∫U,B U ∂μ)) := by
  have inside (U) : C*(J U-A U*B U)=C*J U-D U*B U := by rw [mul_sub,←mul_assoc,sold]
  have outside (U) : C*(A U*B U)=D U*B U := by rw [←mul_assoc,sold]
  rw [mul_add,mul_sub,←mul_assoc,←integral_const_mul (μ:=μ) C A,
    ←integral_const_mul (μ:=μ) C (fun U=>J U-A U*B U),
    ←integral_const_mul (μ:=μ) C (fun U=>A U*B U)]
  simp only [inside,outside,sold]

theorem original (cut : (N p:ℕ)→Fin (N+1)) (T : Slices R.family.path.levels p) (hk : k≤N)
    (live : R.family.ref 4≤k) (a b : R.family.label 4) (φ : Test 2) (r δ : ℝ) :
    ((r^4/(4*δ):ℝ):ℂ)*profile R cut a b φ N p=(R.family.S.a N:ℂ)^(4*2)*
      ∑x:Fin 2→Site (R.family.side N p),φ (cells R.family N p x)*contribution R T hk a b (x 1-x 0) r δ := by
  let C:ℂ:=((r^4/(4*δ):ℝ):ℂ)
  let T₀:=someSlices R.family.path.levels p
  let u:=Nat.le_of_lt_succ (cut N p).isLt
  have term (x : Fin 2→Site (R.family.side N p)) :
      C*posterior R T₀ u a b x=contribution R T hk a b (x 1-x 0) r δ := by
    have same : posterior R T₀ u a b x=posterior R T hk a b (relative R 0 x) := by
      rw [finite R T₀ u,←finite R T u,translate R T u hk (live.trans hk) a b 0]
    have mark:=first R T hk live a x r δ
    unfold relative at mark
    simp only [sub_self] at mark
    rw [same]
    simp only [posterior,contribution,relative,sub_self]
    exact withdraw _ C _ _ _ _ mark
  unfold profile
  change C*(_*_)=_
  rw [mul_left_comm,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_left_comm]
  exact congr_arg (φ (cells R.family N p x)*·) (term x)

end YM.Integration.WilsonInvariantActionAnchoredProfile
