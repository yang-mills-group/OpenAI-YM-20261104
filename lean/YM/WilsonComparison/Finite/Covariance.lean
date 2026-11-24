import YM.WilsonComparison.Finite.Spectrum
import YM.AlbaMS.Cutis.Hot

/-!
# Finite-regulator propagator bridge to PhysicalSum

Interpret Native stencils as Taylor vertices on the positive-link/site coordinates of
Odom.Book at `deck n`. The change of conventions between that real-space Landau Wick
rule and the momentum-space PhysicalSum Wick rule includes a sign on K and L
(as well as signs in the action). We realize the change over C. All variables are
formally independent; inversion restrictions are imposed by the propagator, not by
deleting momentum labels. B (called L on the Book side) has no contraction lines.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonComparison.Finite
open Function Matrix Lattice Bloch
open MS MS.Landau MS.Tone MS.City MS.Orbit MS.Swirl.Near
open MSBar MSBar.Bric MSBar.Loft MSBar.Inlay MSBar.Cutis MSBar.Cutis.Winter
open scoped BigOperators Matrix Classical
open Complex (I)
variable {G : Gauge} {n : Side}

abbrev LegPosition (G : Gauge) (P : Type) := Leaf G (Edge P) P
def tagPosition (G : Gauge) (P : Type) : LegPosition G P ≃ MS.Native.LightMode G P where
  toFun x := match x with
  | .inl (.inl ((x,i),c)) => ((MS.Landau.gauge i,c),x)
  | .inl (.inr ((x,i),c)) => ((anti i,c),x)
  | .inr (.inl (x,c)) => ((ghost,c),x)
  | .inr (.inr (x,c)) => ((gaugeC,c),x)
  invFun x := match x with
  | (((some i,false),c),x) => .inl (.inl ((x,i),c))
  | (((some i,true),c),x) => .inl (.inr ((x,i),c))
  | (((none,false),c),x) => .inr (.inl (x,c))
  | (((none,true),c),x) => .inr (.inr (x,c))
  left_inv x := by rcases x with (⟨⟨_,_⟩,_⟩|⟨⟨_,_⟩,_⟩) | (⟨_,_⟩|⟨_,_⟩) <;> rfl
  right_inv x := by rcases x with ⟨⟨⟨_|_, _|_⟩,_⟩,_⟩ <;> rfl
lemma tagParity {P : Type} (i : LegPosition G P) : parity (tagPosition G P i).1 = ø i := by
  rcases i with (i|i)|(i|i) <;> rfl

/- multiplier for taking Alba vertices (as functions of position link coordinates)
 to MS site kernels. The L/B choice is unphysical; contractions there are zero.
-/
def kSign (i : Atom Axis) : ℂ := if i.2 then -1 else 1
abbrev FT (i : FixedMode G n) (p : FixedMode G n) := if i.1=p.1 then cell p.2 i.2 else 0

def fieldChange (x : LegPosition G (Site n)) (p : FixedMode G n) :=
  let i := tagPosition G (Site n) x
  kSign i.1.1 * FT i p

lemma legalChange : Bric.Coil.Routes ø σbranch (fieldChange (G:=G) (n:=n)) := by
  intro i j hv; unfold fieldChange FT at hv
  dsimp only at hv
  by_cases h:(tagPosition G (Site n) i).1=j.1
  · rw [← tagParity i,h]
  exact False.elim (hv (by rw [if_neg h,mul_zero]))

-- two periodic orbits. interpret Φ.Send. Pull both Wick ends by transform (complex bilinear)
def readLine (Z : Cog.Grain (FixedMode G n)) (i j : FixedMode G n) : ℂ :=
  ∑ p : FixedMode G n, ∑ q : FixedMode G n, FT i p * Z p q * FT j q
lemma read_expand (Z : Cog.Grain (FixedMode G n)) (k l : BH G) (x y : Site n) :
    readLine Z (k,x) (l,y) = ∑ p : Site n, ∑ q : Site n,
      cell p x * Z (k,p) (l,q) * cell q y := by
  unfold readLine
  simp_rw [Fintype.sum_prod_type (α₁:=BH G) (α₂:=Site n)]
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _)]
  · refine Finset.sum_congr rfl fun i _=> ?_; rw [Finset.sum_eq_single_of_mem l (Finset.mem_univ _)]
    · refine Finset.sum_congr rfl fun j _=> by simp only [FT, if_true]
    intro b _ hb; simp [FT,Ne.symm hb]
  intro b _ hb; simp [FT, Ne.symm hb]

lemma straight_line (T : MS.Latch.Edge G) (k l : BH G) (x y : Site n) :
    readLine (mat n T) (k,x) (l,y) = ∑ p : Site n,
      cell p x * (scaleZ n * T k l (Coord p)) * cell (-p) y := by
  rw [read_expand]; refine Finset.sum_congr rfl fun i _=> ?_
  rw [Finset.sum_eq_single_of_mem (-i) (Finset.mem_univ _)]
  · simp [mat]
  intro j _ h; unfold mat; simp [show ¬ i = -j from fun he=> h (by rw [he, neg_neg])]

lemma image_line (T : MS.Latch.Edge G) (k l : BH G) (x y : Site n) :
    readLine (Cog.imageW (iota G n) (mat n T)) (k,x) (l,y) = ∑ p : Site n,
      cell p x * (scaleZ n * T k l (Coord p) * switch (l,-Coord p)) * cell p y := by
  rw [read_expand]; refine Finset.sum_congr rfl fun i _=> ?_
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · dsimp only [Cog.imageW]; rw [iota_spin, iota_mode]; simp only [mat, neg_neg, if_true];
    change cell i x * (_ * switch (l, Coord (-i))) * _ = _
    rw [show switch (l,-Coord i)= _ from (switch_pin l (ξ_neg i) : switch (l,-Coord i)=switch (l,Coord (-i)))]
  intro j _ h; simp [Cog.imageW,mat,iota_mode, Ne.symm h]

lemma read_add (Z Y : Cog.Grain (FixedMode G n)) (i j : FixedMode G n) :
    readLine (Z+Y) i j = readLine Z i j + readLine Y i j := by
  simp only [readLine,Pi.add_apply,mul_add,add_mul,Finset.sum_add_distrib]

-- vertex positions reflect into image terms w/ correct link shift
abbrev imageOf (k : Atom Axis) (x : Site n) := k.1.elim (-x) (fun i=> -x-step i)
abbrev imageSign (k : Atom Axis) := if k.1.isSome then (-1:ℂ) else 1
lemma switch_link (i : Axis) (b : Bool) (c : G.ColorIndex) (p x : Site n) :
    switch (((some i,b),c),-(Coord p)) * cell p x = -cell (-p) (-x-step i) := by
  change ((-1:ℂ) * (MS.Tone.bill (-(-Coord p)) (MS.Tone.Frame.z i))^2) * cell p x = _
  rw [neg_neg]
  change _ * midPhase p i ^ 2 * cell p x = _
  rw [pow_two, ← step_eq_phase, cell_left_neg, show -x-step i = -(x+step i) by abel, cell_inverse,
    inv_inv,cell_add]; ring
lemma imageOf_eq (l : BH G) (x p : Site n) :
    switch (l,-Coord p) * cell p x = imageSign l.1 * cell (-p) (imageOf l.1 x) := by
  match l with
  | ((some i,b),c)=> rw [switch_link]; exact (neg_one_mul ..).symm
  | ((none,b),c)=>
    change (1 * (MS.Tone.bill _ 0)^2 : ℂ) * cell p x = 1 * cell (-p) (-x)
    rw [cell_left_neg,cell_inverse]; simp
lemma quotient_line (k l : BH G) (x y : Site n) :
    readLine (Master G n true) (k,x) (l,y)=
      readLine (mat n (FinalK G)) (k,x) (l,y)+
      imageSign l.1*readLine (mat n (FinalK G)) (k,x) (l,imageOf l.1 y) := by
  rw [show Master G n true = mat n (FinalK G) + Cog.imageW (iota G n) (mat n (FinalK G)) from rfl,
    read_add,image_line]; congr 1; rw [straight_line,Finset.mul_sum]; refine Finset.sum_congr rfl fun p _=>?_
  linear_combination cell p x * (scaleZ n * FinalK G k l (Coord p)) * imageOf_eq l y p

lemma pull_ends (Z : Cog.Grain (FixedMode G n)) (i j : LegPosition G (Site n)) :
    ∑ p : FixedMode G n, ∑ q : FixedMode G n, fieldChange i p * Z p q * fieldChange j q =
      kSign (tagPosition G _ i).1.1 * kSign (tagPosition G _ j).1.1 * readLine Z (tagPosition G _ i) (tagPosition G _ j) := by
  simp_rw [fieldChange, readLine, Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intros; ring
open Coil
private lemma read_A (x y : Edge (Site n)) (c d : G.ColorIndex) :
    readLine (mat n (FinalK G)) ((MS.Landau.gauge x.2,c),x.1)
      ((MS.Landau.gauge y.2,d),y.1) = (dotC G (W n) (x,c) (y,d):ℂ)/2 := by
  rw [straight_line]; obtain ⟨x,i⟩:=x; obtain ⟨y,j⟩:=y
  simp only [FinalK,Bass,dotC,chip,Matrix.of_apply,MS.Landau.choir]
  split_ifs with h
  · rw [W_entries, Finset.sum_div]
    refine Finset.sum_congr rfl fun p _=>?_
    change _ * (_ * (midPhase p i * MS.Tone.bill (-Coord p) (MS.Tone.Frame.z j) * _ / 2)) * _= _
    rw [MS.Tone.opp]; unfold midPhase; ring
  simp
private lemma read_K (x : Edge (Site n)) (y : Site n) (c d : G.ColorIndex) :
    readLine (mat n (FinalK G)) ((anti x.2,c),x.1) ((ghost,d),y) =
      (dotC G (Winter.U n) (x,c) (y,d):ℂ)/2 := by
  rw [straight_line]; obtain ⟨x,i⟩:=x
  simp only [FinalK,Bass,dotC,chip, Matrix.of_apply, Landau.choir]
  split_ifs with h
  · rw [U_entries, Finset.sum_div]
    refine Finset.sum_congr rfl fun p _=>?_
    change _ * ( _ * (midPhase p i * (MS.Tone.bill _ 0) * _ / 2)) * _ = _
    rw [right0]; ring
  simp

lemma quotient_A (x y : Edge (Site n)) (c d : G.ColorIndex) :
    readLine (Master G n true) ((MS.Landau.gauge x.2,c),x.1) ((MS.Landau.gauge y.2,d),y.1)=
      ((extoll G n 1).H (x,c) (y,d):ℂ)/2 := by
  rw [quotient_line, read_A];
  rw [show ( ( (MS.Landau.gauge y.2,d):BH G), imageOf (MS.Landau.gauge y.2) y.1) =
    (((MS.Landau.gauge ((Odom.copper n).σ y).2,d):BH G), ((Odom.copper n).σ y).1) from rfl]
  rw [read_A];
  change _ + (-1:ℂ)*_=_
  simp only [extoll,one_pow,inv_one,one_smul,dotC,chip,Matrix.of_apply,
    Matrix.add_apply,aura_right]
  split_ifs <;> push_cast <;> ring

lemma quotient_K (x : Edge (Site n)) (y : Site n) (c d : G.ColorIndex) :
    readLine (Master G n true) ((anti x.2,c),x.1) ((ghost,d),y)=
      ((extoll G n 1).U (x,c) (y,d):ℂ)/2 := by
  rw [quotient_line, read_K, read_K];
  change (dotC G _ _ (y,d):ℂ)/2 + 1*((dotC G _ _ (-y,d):ℂ)/2)=_
  simp only [extoll,one_pow,inv_one,one_smul,dotC,chip,Matrix.of_apply, UU,
    Matrix.add_apply,flow_right]; split_ifs <;> push_cast <;> ring

lemma read_symm (k l : BH G) (x y : Site n) :
    readLine (Master G n true) (k,x) (l,y) =
      MS.Koszul.cross (parity k) (parity l) * readLine (Master G n true) (l,y) (k,x) := by
  rw [read_expand,read_expand]; conv_rhs => rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _=> ?_
  refine Finset.sum_congr rfl fun q _=> ?_; rw [paySym true (k,p)]; change _ *
    ( MS.Koszul.cross (parity k) (parity l) * _) * _ = _; ring

lemma pair_off (k l : BH G) (h : ∀ p, Tail k.1 l.1 p=0) (x y : Site n) :
    readLine (Master G n true) (k,x) (l,y)=0 := by
  have he (y:Site n) : readLine (mat n (FinalK G)) (k,x) (l,y)=0:= by
    rw [straight_line]; simp [FinalK,Bass,Landau.choir,h]
  rw [quotient_line,he,he]; ring

private lemma coeffHalf (f:ℝ) : ((halve ℝ * f : ℝ):ℂ) = (f:ℂ)/2 := by
  rw [show halve ℝ=1/2 from ?_]; · push_cast; ring
  norm_num [halve]

private lemma covariance_A (x y : Edge (Site n)) (c d : G.ColorIndex) :
    ∑ p : FixedMode G n, ∑ q : FixedMode G n,
      fieldChange (.inl (.inl (x,c))) p * Master G n true p q * fieldChange (.inl (.inl (y,d))) q
      = ((extoll G n 1).hop (Loft.Place.a (x,c)) (Loft.Place.a (y,d)):ℂ) := by
  rw [pull_ends]
  change 1*1* readLine _ ((MS.Landau.gauge _,c),x.1) ((MS.Landau.gauge _,d),y.1)= ((halve ℝ* _ : ℝ):ℂ)
  rw [one_mul,one_mul,quotient_A,coeffHalf]; rfl

private lemma covariance_K (x : Edge (Site n)) (y : Site n) (c d : G.ColorIndex) :
    ∑ p : FixedMode G n, ∑ q : FixedMode G n,
      fieldChange (.inl (.inr (x,c))) p * Master G n true p q * fieldChange (.inr (.inl (y,d))) q
      = ((extoll G n 1).hop (Place.k (x,c)) (Place.c (y,d)):ℂ) := by
  rw [pull_ends]
  change (-1)*1*readLine _ ((anti _,c),x.1) ((ghost,d),y) = ((halve ℝ * - (extoll G n 1).U _ _ : ℝ):ℂ)
  rw [quotient_K, coeffHalf]; push_cast; ring

private lemma covariance_c (x : Edge (Site n)) (y : Site n) (c d : G.ColorIndex) :
    ∑ p : FixedMode G n, ∑ q : FixedMode G n,
      fieldChange (.inr (.inl (y,d))) p * Master G n true p q * fieldChange (.inl (.inr (x,c))) q
      = ((extoll G n 1).hop (Place.c (y,d)) (Place.k (x,c)):ℂ) := by
  rw [pull_ends]
  change 1*(-1)*readLine _ ((ghost,d),y) ((anti _,c),x.1) = ((halve ℝ* _ : ℝ):ℂ)
  rw [read_symm, quotient_K, coeffHalf]; rw [show (Koszul.cross (parity (ghost,d)) (parity (anti x.2,c)):ℂ)=-1 from rfl]; simp [Fritz.rose]

set_option maxHeartbeats 800000 in
/-- Exact Fourier and link/site chart convention change on these Landau propagators. Both sides include
  the `1/2` (Wick operator coefficients, not the raw two-point moment).
  This holds with the inverse-zero convention, and carries the signs for c,K.
  Even side not needed until interpreting the quotient action. -/
theorem covariance (i j : LegPosition G (Site n)) :
    ∑ p : FixedMode G n, ∑ q : FixedMode G n, fieldChange i p * Master G n true p q * fieldChange j q =
      ((extoll G n 1).hop i j : ℂ) := by
  rcases i with (⟨i,c⟩|⟨i,c⟩)|(⟨i,c⟩|⟨i,c⟩) <;> rcases j with (⟨j,d⟩|⟨j,d⟩)|(⟨j,d⟩|⟨j,d⟩)
  all_goals first| exact covariance_A i j c d| exact covariance_K i j c d| exact covariance_c j i d c| skip
  all_goals
    rw [pull_ends];
    change _ * readLine _ (_,_) (_,_) = ( (halve ℝ*0 : ℝ):ℂ)
    rw [pair_off _ _ (fun p=> rfl)]
    simp
end YM.WilsonComparison.Finite
