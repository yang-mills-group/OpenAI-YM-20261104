import YM.Integration.WilsonPositionProgramInfraredWindow
import YM.Integration.WilsonPositionProgramSubmittedRate
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramSubmittedDates
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open WilsonPositionProgramCommonWindow WilsonPositionProgramInfraredWindow
variable {G : Gauge} (C : Run G) (D : XSpace.Run) (simple : G.Simple)
local notation "Λ" => RG16.Lambda C.family.path.levels
local notation "β" => C.family.path.levels.clock.hatBeta

private theorem uniform (L : ℝ) (hL : 0 < L) (v : ℕ) (ell : ℝ) (h : 1  ≤  ell) (i : ℕ)
    (upper : (i:ℝ)*L  ≤  ell^((3:ℝ)/2)+2*ell) :
    (v*i*i:ℕ)  ≤  (v:ℝ)*(3/L)^2*ell^4 := by
  have sq : ell^((3:ℝ)/2)  ≤  ell^2 := by
    rw [←Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le h (by norm_num)
  have base : ell  ≤  ell^2 := by nlinarith only [mul_nonneg (zero_le_one.trans h) (sub_nonneg.mpr h)]
  have cnt : (i:ℝ)  ≤  (3/L)*ell^2 := by
    apply (le_div_iff₀ hL).2 at upper
    calc _  ≤  (ell^((3:ℝ)/2)+2*ell)/L := upper
         _  ≤  (3*ell^2)/L := by apply div_le_div_of_nonneg_right _ hL.le; linarith
         _ = _ := by ring
  have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg i) cnt 2) (Nat.cast_nonneg v)
  push_cast
  nlinarith only [hs]

include simple in
private theorem timely (start : ℕ) (w : ℕ → ℕ) (blocks : ∀ t,
    (C.family.S.block (start+t)).val=D.ratio^(w t)) (stage fine : ℕ) :
    ∀ᶠ n in atTop, ∀ b i : ℕ, b ≤ n →
      Λ (start+n)^((3:ℝ)/2)  ≤  (i:ℝ)*Real.log D.ratio →
      (i:ℝ)*Real.log D.ratio  ≤  Λ (start+n)^((3:ℝ)/2)+2*Λ (start+n) →
      elapsed w b + D.reserve*i*i=elapsed w n →
      stage ≤ start+b ∧ fine  ≤  i ∧ 1 ≤ β (start+b) ∧ Λ (start+b)  ≤  (i:ℝ)*Real.log D.ratio := by
  let l := Real.log (D.ratio:ℝ)
  let K := (D.reserve:ℝ)*(3/l)^2
  let B := (elapsed w stage:ℝ)
  have L : 0<l := Real.log_pos (by exact_mod_cast (show 1<D.ratio from (by decide : 1<3).trans_le D.large))
  have rise := WilsonPositionProgramInfraredRoom.capacity C simple D start w blocks (K+B+1) 4
  have shift : Tendsto (fun n:ℕ => start+n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_left n start) tendsto_id
  have enough := ((RG16.Literal.lambda_leads C.family simple).comp shift).eventually_ge_atTop ((fine:ℝ)*l)
  filter_upwards [rise,enough] with n room weight
  intro b i hb lo hi stock
  have ell : 1 ≤ Λ (start+n) := by
    have pos := (C.family.path.levels.fits.delayed (start+n)).le
    change 1 ≤ 2+Real.log (β (start+n));linarith [Real.log_nonneg pos]
  have one : (1:ℝ) ≤ (Λ (start+n))^4 := one_le_pow₀ ell
  have bound := uniform l L D.reserve (Λ (start+n)) ell i hi
  change (D.reserve*i*i:ℕ)  ≤  K*(Λ (start+n))^4 at bound
  have coarse : stage ≤ start+b := by
    by_contra h
    have before : b ≤ stage := by omega
    have cmp : elapsed w b ≤ elapsed w stage := Finset.sum_le_sum_of_subset (Finset.range_mono before)
    have cmpR : (elapsed w b:ℝ) ≤ B := by dsimp only [B]; exact_mod_cast cmp
    have eqR := congrArg (fun k:ℕ => (k:ℝ)) (show elapsed w b+D.reserve*i*i=elapsed w n from stock)
    push_cast at eqR bound
    have b0 : 0 ≤ B := by positivity
    nlinarith only [room,bound,eqR,cmpR,one,mul_nonneg b0 (sub_nonneg.mpr one)]
  have elo : Λ (start+n)  ≤  Λ (start+n)^((3:ℝ)/2) := by
    calc _ = Λ (start+n)^(1:ℝ) := (Real.rpow_one _).symm
         _  ≤  _ := Real.rpow_le_rpow_of_exponent_le ell (by norm_num)
  have age := (RG16.Literal.lambda_mono C.family simple).monotone (Nat.add_le_add_left hb start)
  refine ⟨coarse, ?_,(C.family.path.levels.fits.delayed _).le,age.trans (elo.trans lo)⟩
  exact_mod_cast (le_of_mul_le_mul_right (weight.trans (elo.trans lo)) L)

include simple in
/-- Every pre-elected local resource and every subsequently required numerical error threshold
applies on the very same constant-block re-expression of the actual variable Wilson dates. -/
theorem original {a : Axis} {ε : ℝ} (purchase : WilsonPositionProgramNestedElection.course simple a ε C.kit) {d : ℕ}
    (hd : 0<d) (ratio : D.ratio=(3:ℕ)^d) (pace : ∀ m, ((C.family.S.block m).val:ℝ) ≤ Real.log (Λ m)) :
    ∃ start : ℕ, ∃ w : ℕ→ℕ, (∀ k, (C.family.S.block (start+k)).val=D.ratio^(w k)) ∧
      ∀ stage fine : ℕ, ∀ᶠ n in atTop, ∃ b ≤ n, ∃ j>0, let i := elapsed (next w n) j
        stage ≤ start+b ∧ fine  ≤  i ∧ 1 ≤ β (start+b) ∧ Λ (start+b) ≤ (i:ℝ)*Real.log D.ratio ∧
        C.family.S.a ((start+n)+j)/C.family.S.a (start+n)=(D.step i).spacing ∧
        Λ (start+n)^((3:ℝ)/2)  ≤  (i:ℝ)*Real.log D.ratio ∧
        (i:ℝ)*Real.log D.ratio  ≤  Λ (start+n)^((3:ℝ)/2)+2*Λ (start+n) ∧
        elapsed w b+D.reserve*i*i=elapsed w n ∧ elapsed (next w b) (n+j-b)=D.reserve*i*i+i := by
  obtain ⟨start,w,blocks,dates⟩ := WilsonPositionProgramInfraredWindow.chosen C D (simple:=simple) purchase hd ratio pace
  refine ⟨start,w,blocks,fun stage fine => ?_⟩
  filter_upwards [dates,timely C D simple start w blocks stage fine] with n choose due
  obtain ⟨b,hb,j,hj,spacing,lo,hi,eq,full⟩ := choose
  obtain ⟨age,index,initial,meter⟩ := due b _ hb lo hi eq
  exact ⟨b,hb,j,hj,age,index,initial,meter,spacing,lo,hi,eq,full⟩

end YM.Integration.WilsonPositionProgramSubmittedDates
