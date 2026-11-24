import YM.Integration.SignedMarkedChartGerm
import YM.WilsonCoeffUV.Marked.Step.Inverse

/-! The complete native finite source exponential, with all independently active mixed hypervertices. Its primitive entries are the actual charged, measured field jets on the same finite forest. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedJointSourceMoments
open Function Filter Finset Lattice Laurent Wilson RG Precision Exterior Tree Bloch Matrix PowerSeries
open Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary
open scoped BigOperators Classical ContDiff Topology Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {ι : Type} [DecidableEq ι]

/-- Power carried by all source labels in a physical subtuple. This extends multiplication through disjoint partitions even when individual connected hypervertices have distinct Laurent shifts. -/
def clearing (b : ι→ℕ) (s : Finset ι) : ℕ := ∑a∈s,b a

variable {A R : Type} [CommRing A] [CommRing R] [Algebra ℝ A] [Algebra ℝ R]

def pushed (b : ι→ℕ) (X : R) (L : A→+* R) (f : Finset ι→A) (s : Finset ι) := X^(clearing b s)*L (f s)

omit [DecidableEq ι] [Algebra ℝ A] [Algebra ℝ R] in
private theorem dialed (b : ι→ℕ) (x : R) (L : A→+*R) (f : Finset ι→A) (s : Finset ι) :
    dial (pushed b x L f) s=pushed b x L (dial f) s := by simp [dial,pushed,nsmul_eq_mul,mul_left_comm]

omit [Algebra ℝ A] [Algebra ℝ R] in
private theorem joined (b : ι→ℕ) (x : R) (L : A→+*R) (f h : Finset ι→A) (s : Finset ι) :
    pushed b x L (shells f h) s=shells (pushed b x L f) (pushed b x L h) s := by
  unfold pushed shells
  rw [map_sum,mul_sum]
  apply sum_congr rfl
  intro t ht
  have hst := mem_powerset.mp ht
  have hd : clearing b s=clearing b t+clearing b (s\t) := (sum_sdiff hst).symm.trans (add_comm _ _)
  rw [hd,pow_add,map_mul];ring

include ι in
omit [Algebra ℝ A] [Algebra ℝ R] in
theorem transported (b : ι→ℕ) (x : R) (L : A→+*R) {f g : Finset ι→A} (h : Equation f g) :
    Equation (pushed b x L f) (pushed b x L g) := by
  refine ⟨by simp [pushed,clearing,h.1],by simp [pushed,h.2.1],?_⟩
  funext s
  rw [dialed,h.2.2,joined]
  apply sum_congr rfl
  intro t _
  rw [dialed]

/-- Complete product of marked sources. This recursion contains every disjoint split, including genuine nonsingleton incoming edges and all of their products. -/
def products (f : Finset ι→R) (s : Finset ι) : R :=
  if s=∅ then 1 else (s.card:ℝ)⁻¹ • ∑t∈s.powerset,if _w:t⊆s∧t≠∅ then (t.card • f t)*products f (s\t) else 0
termination_by s.card
decreasing_by exact Finset.card_lt_card (sh_k _w.1 _w.2)

private theorem equation (f : Finset ι→R) (h : f ∅=0) : Equation (products f) f := by
  refine ⟨by rw [products,if_pos rfl],h,?_⟩
  funext s
  by_cases hs:s=∅
  · subst s;simp [dial,shells]
  have hc : (s.card:ℝ)≠0 := by exact_mod_cast card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hs)
  rw [dial,products,if_neg hs,←Nat.cast_smul_eq_nsmul ℝ,smul_smul,mul_inv_cancel₀ hc,one_smul]
  apply sum_congr rfl
  intro t ht
  by_cases h₀:t=∅
  · subst t;simp [dial]
  · simp [mem_powerset.mp ht,h₀,dial]

section fields
variable {G : Gauge} {c f : Side} (S : StepData c f) (F : Forest S.ratio) (M : Matrix (Woods G f) (Woods G c) ℝ) (ρ : fieldDir G c 1→ AxisChart G F)
variable {D : ι→ℕ} (k b : ι→ℕ)

/-- A finite original source ledger in the native joint field/marker representation. Every hypervertex carries its actual support, grade and field/current. -/
structure Bank (G : Gauge) (D : ι→ℕ) where
  keys : Finset ι→ Finset ℕ
  vac : keys ∅=∅
  rank : Finset ι→ℕ→ℕ
  head : Finset ι→ℕ→ℕ
  src (s : Finset ι) (i : ℕ) : Comet G (Pen D s) (rank s i)

variable (P : Bank G D)

def given (s : Finset ι) : Era G (Pen D s) := ∑i∈P.keys s,volumeR (P.src s i) (P.head s i)

def entry (A : Case D) (s : Finset ι) : Ink (Active G F⊕Woods G c) := ∑i∈P.keys s,
  X^(clearing b s+P.head s i-P.rank s i)*jet (fun y : Sloc S F G=>(dip (P.src s i) (touch A s)).unmasked (Work.F03.live F (SignedMarkedChartGerm.chart S F ρ y)) 0)

omit [DecidableEq ι] in
theorem authentic (hs : ∀s i,i∈P.keys s→shadeStar (P.src s i)) (h : ∀s i,i∈P.keys s→P.rank s i≤mass k s+P.head s i) : Eu k (given P) :=
  fun s=>Auth.sum (fun i hi=>aug_auth (P.src s i) (hs s i hi) (h s i hi))

/-- On the one true numerical chart, the complete cleared source moment is exactly the full unintegrated physical exponential, in every coefficient and every named subset. -/
theorem original (hs : ∀s i,i∈P.keys s→shadeStar (P.src s i)) (h : ∀s i,i∈P.keys s→P.rank s i≤mass k s+P.head s i)
    (hclear : ∀s i,i∈P.keys s→P.rank s i≤clearing b s+P.head s i)
    (hM : M=reveal G S F*((reveal G S F).transpose*M)) (hρ : ContDiffAt ℝ ω ρ 0) (h₀ : ρ 0=0) (A : Case D) (s : Finset ι) :
    (X:Ink (Active G F⊕Woods G c))^(clearing b s)*retool (shore S F M ρ) (loom (camSlice G S F M) (flash (pPly A s ((levelsO (given P) s).1 f))))=
      products (entry S F ρ b P A) s := by
  let L := (retool (shore S F M ρ)).comp (loom (camSlice G S F M))
  have hK := authentic k P hs h
  have hE : given P ∅=0 := by simp [given,P.vac]
  have received := transported b (X:Ink (Active G F⊕Woods G c)) L (levels_exp _ hK hE A f)
  have he : pushed b X L (feeble (given P) A f)=entry S F ρ b P A := by
    funext t
    change X^(clearing b t)*L (readO A (∑i∈P.keys t,volumeR (P.src t i) (P.head t i)) f)=_
    rw [read_Sum A f (fun i hi=>aug_auth (P.src t i) (hs t i hi) (h t i hi)),map_sum,mul_sum]
    apply sum_congr rfl
    intro i hi
    exact SignedMarkedChartGerm.cleared S F M ρ (P.src t i) (touch A t) (P.head t i) (clearing b t) _ (by have := hclear t i hi;omega) hM hρ h₀
  rw [he] at received
  exact congr_fun (Equation.prod_u _ _ _ received (equation _ (by simp [entry,P.vac]))) s
end fields
end YM.Integration.SignedJointSourceMoments
