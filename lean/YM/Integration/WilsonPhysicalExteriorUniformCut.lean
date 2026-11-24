import YM.Integration.WilsonPhysicalExteriorFirstCutPrice

/-! Uniform first-cut estimates, at the original physical finite source and
the independent booked MS row, at every placement in a moving far window.
The signed source value at stage j only reads that stage's actual mesh.
Consequently arbitrary independent placements can be chosen after j and p. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorUniformCut
open Filter Real Lattice RG RG16 PhysicalNext.Repeat.Legato
open MS MS.Dial MS.Menus MS.Land MS.Rake MS.Tide MS.Fleet MS.Tone
open FVA2 Register YM.FVAAlt2 RegulatorIR.FVAAlt2.Lodge
open WilsonPhysicalExteriorActualSides WilsonPhysicalExteriorResolvedCutoff
open WilsonPhysicalExteriorUVStory WilsonPhysicalExteriorFirstCut
open scoped Topology Classical

variable {G:Gauge} (R:Run G)
local notation "B₀" => Press.portDeck G
local notation "M₀" => MS_Data G (Position.OpenAxis.Plot B₀)
local notation "Λ₀" => RG16.Lambda R.family.path.levels
private abbrev clock (c:ℝ) (j:ℕ) := WilsonPhysicalExteriorActualSides.time R c j

private theorem local_row {n:ℕ} (M:M₀) (Q:Prescription B₀) (D:Fin n→Label B₀)
    (c:ℝ) (W W':Fin n→ℕ→ Cover) (b:Bool) (k:ℕ) (u:ℝ) (j p:ℕ)
    (same:∀i,W i j=W' i j) :
    signed R M Q D c W b k u (j,p)=signed R M Q D c W' b k u (j,p) := by
  let F(x:Fin n→ Cover):=signed R M Q D c (fun i _=>x i) b k u (j,p)
  calc
    _=F (fun i=>W i j) := by cases b <;> rfl
    _=F (fun i=>W' i j) := congrArg F (funext same)
    _=_ := by cases b <;> rfl

theorem window {n:ℕ} {I:Type} [Nonempty I] (M:M₀) (Q:Prescription B₀)
    (rows:WilsonPhysicalExteriorFirstCutPrice.Rows R M Q)
    (D:Fin n→Label B₀) (c c':ℝ) (V:I→Fin n→ℕ→ Cover)
    (slow:∀m:ℕ,((R.family.S.block m).val:ℝ)≤log (Λ₀ m))
    (h₁:1<c') (h₂:c'<c) (h₃:c<2) (lo:ℕ→ℕ)
    (reach:∀i,∃A:ℝ,0<A ∧ ∃e:ℕ,∀j x,‖Tone.embed (V x i j)‖≤A*(exp (clock R c j))^e)
    (separated:∀i l:Fin n,i≠l → ∃B:ℝ,0<B ∧
      ∀j x,exp (clock R c j)≤B*‖Tone.embed (V x i j)-Tone.embed (V x l j)‖)
    (μ q:ℝ) (k h:ℕ) :
    ∀ᶠ j:ℕ in atTop,∀ x:I,∀ side:Bool,∀ p≥floor R c lo j,
      let T:=WilsonPhysicalExteriorFirstCutScale.ratio R c' j
      let err:=fun u:ℝ=>T^h*‖signed R M Q D c (V x) side k u (j,p)‖
      err μ≤exp (-q*Λ₀ j) ∧ err (μ+R.family.S.scale j)≤exp (-q*Λ₀ j) := by
  let P (j:ℕ) (x:I) : Prop:=∀ side:Bool,∀ p≥floor R c lo j,
    let T:=WilsonPhysicalExteriorFirstCutScale.ratio R c' j
    let err:=fun u:ℝ=>T^h*‖signed R M Q D c (V x) side k u (j,p)‖
    err μ≤exp (-q*Λ₀ j) ∧ err (μ+R.family.S.scale j)≤exp (-q*Λ₀ j)
  let choice (j:ℕ) : I:=if bad:∃x,¬P j x then bad.choose else Classical.choice inferInstance
  let W (i:Fin n) (j:ℕ):=V (choice j) i j
  have rv:Reach (geometry R c 0) (field R c 0 W).off := by
    intro i
    obtain ⟨A,hA,e,fee⟩:=reach i
    exact ⟨A,hA,e,fun z=>fee z.1 (choice z.1)⟩
  have sv:Resolved (geometry R c 0) (info (field R c 0 W).off) := by
    intro i l ne
    obtain ⟨B,hB,fee⟩:=separated i l ne
    exact ⟨B,hB,fun z=>fee z.1 (choice z.1)⟩
  filter_upwards [rows n D c c' W slow h₁ h₂ h₃ lo rv sv μ q k h] with j hj
  change ∀x,P j x
  by_contra! bad
  have fail:¬P j (choice j):=by simpa only [choice,dif_pos bad] using bad.choose_spec
  apply fail
  intro side p hp
  change _ ∧ _
  have at_stage (u:ℝ) := local_row R M Q D c W (V (choice j)) side k u j p (fun _=>rfl)
  obtain ⟨a,b⟩:=hj side p hp
  dsimp only at a b ⊢
  rw [at_stage μ] at a
  rw [at_stage (μ+R.family.S.scale j)] at b
  exact ⟨a,b⟩

/-- An initial collision or a coarse finite mesh incurs no assumption on a
genuinely resolved late window. Its whole finite prefix can be filled using
the original positions at its first resolved member, uniformly in the probe. -/
theorem eventual {n:ℕ} {I:Type} [Nonempty I] (M:M₀) (Q:Prescription B₀)
    (rows:WilsonPhysicalExteriorFirstCutPrice.Rows R M Q)
    (D:Fin n→Label B₀) (c c':ℝ) (V:I→Fin n→ℕ→ Cover)
    (slow:∀m:ℕ,((R.family.S.block m).val:ℝ)≤log (Λ₀ m))
    (h₁:1<c') (h₂:c'<c) (h₃:c<2) (lo:ℕ→ℕ)
    (A B:ℝ) (hA:0<A) (hB:0<B) (d:ℕ)
    (room:∀ᶠ j:ℕ in atTop,∀x:I,
      (∀i,‖Tone.embed (V x i j)‖≤A*(exp (clock R c j))^d) ∧
      ∀i l,i≠l → exp (clock R c j)≤B*‖Tone.embed (V x i j)-Tone.embed (V x l j)‖)
    (μ q:ℝ) (k h:ℕ) :
    ∀ᶠ j:ℕ in atTop,∀ x:I,∀ side:Bool,∀ p≥floor R c lo j,
      let T:=WilsonPhysicalExteriorFirstCutScale.ratio R c' j
      let err:=fun u:ℝ=>T^h*‖signed R M Q D c (V x) side k u (j,p)‖
      err μ≤exp (-q*Λ₀ j) ∧ err (μ+R.family.S.scale j)≤exp (-q*Λ₀ j) := by
  obtain ⟨j₀,hw⟩:=eventually_atTop.mp room
  let late (x:I) (i:Fin n) (j:ℕ):=V x i (max j₀ j)
  let E(j:ℕ):=exp (clock R c j)
  let K:ℝ:=1+∑ j ∈ Finset.range j₀,E j
  have pos (j:ℕ):0<E j:=exp_pos _
  have E₁ (j:ℕ):1≤E j:=Real.one_le_exp
    ((rpow_nonneg (Literal.lambda_pos R.family j).le c).trans (time_at_least R c j))
  have K₁:1≤K:=by dsimp only [K];linarith only [Finset.sum_nonneg (s:=Finset.range j₀) (f:=E) (fun i _=>(pos i).le)]
  have ep:0<K:=zero_lt_one.trans_le K₁
  have early {j:ℕ} (hj:j<j₀):E j≤K := by
    have hh:E j≤∑ i ∈ Finset.range j₀,E i:=Finset.single_le_sum (fun i _=>(pos i).le) (Finset.mem_range.mpr hj)
    dsimp only [K];linarith
  have upper (i:Fin n):∃A':ℝ,0<A' ∧ ∃e:ℕ,∀j x,‖Tone.embed (late x i j)‖≤A'*(exp (clock R c j))^e := by
    refine ⟨A*(E j₀)^d,mul_pos hA (pow_pos (pos _) _),d,?_⟩
    intro j x
    by_cases hj:j₀≤j
    · simpa only [late,max_eq_right hj] using ((hw j hj x).1 i).trans
        (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hA.le (one_le_pow₀ (E₁ j₀))) (pow_nonneg (pos j).le d))
    · simpa only [late,max_eq_left (le_of_not_ge hj)] using ((hw j₀ le_rfl x).1 i).trans
        (le_mul_of_one_le_right (mul_nonneg hA.le (pow_nonneg (pos j₀).le d)) (one_le_pow₀ (E₁ j)))
  have lower (i l:Fin n) (ne:i≠l):∃B':ℝ,0<B' ∧ ∀j x,exp (clock R c j)≤
      B'*‖Tone.embed (late x i j)-Tone.embed (late x l j)‖ := by
    refine ⟨K*B,mul_pos ep hB,?_⟩
    intro j x
    by_cases hj:j₀≤j
    · simpa only [late,max_eq_right hj] using ((hw j hj x).2 i l ne).trans
        (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hB.le K₁) (norm_nonneg _))
    · have hd:=((E₁ j₀).trans ((hw j₀ le_rfl x).2 i l ne))
      calc
        _≤K:=early (lt_of_not_ge hj)
        _≤K*(B*‖Tone.embed (V x i j₀)-Tone.embed (V x l j₀)‖):=le_mul_of_one_le_right ep.le hd
        _ = _ := by simp only [late,max_eq_left (le_of_not_ge hj),mul_assoc]
  filter_upwards [window R M Q rows D c c' late slow h₁ h₂ h₃ lo upper lower μ q k h,
    eventually_ge_atTop j₀] with j hj hv x side p hp
  have eq (u:ℝ) := local_row R M Q D c (late x) (V x) side k u j p
    (fun _=>by simp only [late,max_eq_right hv])
  obtain ⟨a,b⟩:=hj x side p hp
  dsimp only at a b ⊢
  rw [eq μ] at a
  rw [eq (μ+R.family.S.scale j)] at b
  exact ⟨a,b⟩

end YM.Integration.WilsonPhysicalExteriorUniformCut
end
