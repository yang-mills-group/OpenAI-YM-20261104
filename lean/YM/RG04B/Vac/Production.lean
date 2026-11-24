import YM.RG04B.Vac.Victory

/-!
# Uniform arrays of *representations* on the actual physical trajectory

Produces the vacuum/kinetic estimate from the ONLY needed local hypothesis
`LocalPay` (plus unmasked presentation/fee inputs). Every remaining gate
with these qev and prereport reset price shapes is discharged for the
recursion. Don't interpret `route` as another History generating path betas.
β, g and all conditional measures still and always from C.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG04B.Vac
open Function Filter Finset RG Wilson PhysicalNext.Repeat.Legato
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {R : Run G} (T : Campaign R)

abbrev Track (C : Family G) (p : ℕ) := ∀ i:ℕ, Rep G (C.side i p)

/-- Export to subsequent single and multi-mark steps. No `top` changes
of trajectories. -/
structure Delivered {C : Family G} (M : Render C) (tagged : Conjoint C) (N p t r : ℕ)
    (ε : ℝ) (x : Track C p) : Prop where
  first : x N = C.path.rep N p N
  admits (j : ℕ) : t ≤ j → j ≤ N → Sliced M N p j r (x j) (money C r N p j ε)
  connects (j : ℕ) : t ≤ j → j < N →
      tagged N p j (x (j+1)) (x j) ∧
      (∃ c : ℝ, 0 ≤ c ∧ Sliced M N p j r (x j) c ∧ c * toll C.path.levels j ≤ money C r N p (j+1) ε) ∧
        |C.path.β N p j - guess M r N p j| ≤ kiosks (gAt C N p (j+1)) r ε

include T
set_option maxHeartbeats 900000 in
/-- Physical unmarked iterative step prerequisite. Uniform in p AND also
in all ancestors above t (can run over the **same** t). Standing uses
constructor for existence of the extra bookings. Not claiming LocalPay for
any current module, nor any ultraviolet or phase limit of these approximations. -/
theorem residency (D : Drag) (F : Fees)
    (hs : stripe F R.family.path.levels)
    (ht : Booked D.fund R.family.path.levels)
    (hk : Booked requireConversion R.family.path.levels)
    (hu : Booked (Startup.temperatures G) R.family.path.levels)
    (M : Render R.family) (hM : OrderedStart M) (tagged : Conjoint R.family)
    {r : ℕ} {τ : ℝ} (hε : 0<τ) (hτ : τ ≤ 1/2) (he : 2≤r) {u : ℕ→ℝ} {K k i : ℕ}
    (hU : Budgeted R.family.path.levels u)
    (hA : LocalPay M r τ D F i u K k tagged) : ∀ᶠ t : ℕ in atTop,
      ∀ N, t ≤ N → ∀ p : ℕ, ∃ x : Track R.family p, Delivered M tagged N p t r τ x := by
  have hG:=T.gains.SimpleR; have hC: R.family.Makes := R.makes
  have hp:=Startup.issues T hu r hε zero_lt_one he
  have hz:= sealed hC hG hs ht hk M r hU i k hε hτ he
  have ho:=offsets hC hG hk K
  obtain ⟨m,hm⟩:=eventually_atTop.mp (hp.and (hz.and (ho.and hA)))
  filter_upwards [eventually_ge_atTop m] with t hv N hN p
  induction hN using Nat.decreasingInduction with
  | self =>
    obtain ⟨X,-,-,-,hk,hb⟩:= hm N hv|>.1 p -- lets
    let W:= R.family.path.rep N p N
    have ht := hM r he N p
    have hShape : Sliced M N p N r W (money R.family r N p N τ) := by
      refine ⟨X,ht.2,?_,?_⟩
      · unfold error; rw [ht.1]; exact hk
      unfold error; rw [ht.1]; rw [one_mul] at hb; exact hb
    exact ⟨_,⟨(rfl : (R.family.path.rep N p) N=_),fun j h₁ h₂=> by obtain rfl := le_antisymm h₂ h₁; exact hShape,fun _ h₁ h₂=> False.elim (h₁.not_gt h₂)⟩⟩
  | of_succ j hj IH =>
    obtain ⟨x,hX⟩:=IH (hv.trans j.le_succ)
    let y₀:=x (j+1); let f:= money R.family r N p (j+1) τ
    have h1:= (hX.admits (j+1) le_rfl hj)
    have hh:0≤f:= Real.rpow_nonneg (running_pos R.makes _ _ _ hj).le _
    obtain ⟨y,b,c,hb,hT⟩:= (hm _ hv).2.2.2 _ p hj _ _ hh h1 le_rfl ((hm (j+1) (hv.trans j.le_succ)).2.2.1 N hj p y₀ h1.same)
    obtain ⟨he',hr,hk'⟩:= (hm _ hv).2.1 N p hj _ _ _ _ _ hh h1.same le_rfl hb
    let z : Track R.family p:= Function.update x j y
    refine ⟨z,⟨by rw [show z N=x N from Function.update_of_ne hj.ne' _ _,hX.first],fun a hA ha=>?_,fun a hA ha=>?_⟩⟩
    · rcases hA.eq_or_lt with h|h
      · subst a; rw [show z j = y from update_self ..]; exact hb.passed.2.widen hr
      rw [show z a=x a from Function.update_of_ne h.ne' ..]; exact hX.admits a h ha
    rcases hA.eq_or_lt with h|h
    · subst a; simp only [z,update_self,Function.update_of_ne (Nat.succ_ne_self _)]
      exact ⟨hT,⟨c,hb.passed.1,hb.passed.2,he'⟩,hk'⟩
    simp only [z,Function.update_of_ne (show a≠j from h.ne'),Function.update_of_ne (show a+1≠j from (h.trans (Nat.lt_succ_self _)).ne')]; exact hX.connects _ h ha
end YM.RG04B.Vac
