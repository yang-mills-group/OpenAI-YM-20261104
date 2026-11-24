import YM.Integration.WilsonFiniteIncomingMarkedWinding

/-! The same-charge part of the genuine periodic marked heat step is one
Gaussian line. Proper marked subwords and positive quiet grades have strictly
smaller coupling degree plus occupancy. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonFiniteMarkedWickDiagonal
open Function Finset Lattice Wilson RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open scoped Classical BigOperators

variable {U ι : Type} [Fintype U] [DecidableEq ι] {D k : ι → ℕ} {S J : Finset ι}
variable {G : Gauge} {Z : Finset ι} {e : ℕ} {I : Arch G}

private theorem zero_left (C : Matrix U U ℝ) (hj : J ⊆ S) (B : Gen (Pen D (S\J)) U) :
    logos C hj (0 : Gen (Pen D J) U) B = 0 := by
  have unary (x : U) : sever x (0 : Gen (Pen D J) U) = 0 := by
    funext r v; simp [sever,prune]
  have bilinear (Y : Gen (Pen D (S\J)) U) : cob hj (0 : Gen (Pen D J) U) Y = 0 := by
    funext r
    have z (i : ℕ × ℕ) : cobT hj (0 : Ten (Pen D J) U i.1) (Y i.2) r = 0 := by
      funext v; unfold cobT; split <;> simp
    simp [cob,z,swirl]
    funext v; simp
  simp [logos,unary,bilinear]

private theorem zero_right (C : Matrix U U ℝ) (hj : J ⊆ S) (A : Gen (Pen D J) U) :
    logos C hj A (0 : Gen (Pen D (S\J)) U) = 0 := by
  have unary (x : U) : sever x (0 : Gen (Pen D (S\J)) U) = 0 := by
    funext r v; simp [sever,prune]
  have bilinear (X : Gen (Pen D J) U) : cob hj X (0 : Gen (Pen D (S\J)) U) = 0 := by
    funext r
    have z (i : ℕ × ℕ) : cobT hj (X i.1) (0 : Ten (Pen D (S\J)) U i.2) r = 0 := by
      funext v; unfold cobT; split <;> simp
    simp [cob,z,swirl]
    funext v; simp
  simp [logos,unary,bilinear]

private theorem joins (C : Matrix U U ℝ) {X Y : thalamus D U} (h a : ℕ)
    (quietX : ∀ j i, X ∅ j i=0) (quietY : ∀ j i, Y ∅ j i=0)
    (proper : ∀ T ⊂ S, ∀ i≤a, ∀ j, X T j i=Y T j i) (T : Finset ι) (sub : T⊆S) :
    sewsV C sub (X T) (X (S\T)) h a = sewsV C sub (Y T) (Y (S\T)) h a := by
  unfold sewsV
  apply sum_congr rfl; intro b _
  apply sum_congr rfl; intro u hu
  have grade := mem_antidiagonal.mp hu
  by_cases empty : T=∅
  · subst T; rw [quietX,quietY,zero_left,zero_left]
  by_cases full : T=S
  · subst T
    have hush (A : thalamus D U) (empty : ∀ j i,A ∅ j i=0) (J : Finset ι) (hj : J=∅) :
        A J b.2 u.2=0 := by subst J; exact empty _ _
    rw [hush X quietX _ sdiff_self,hush Y quietY _ sdiff_self,zero_right,zero_right]
  have rest : S\T ⊂ S := sdiff_ssubset sub (nonempty_iff_ne_empty.mpr empty)
  rw [proper T (ssubset_of_subset_of_ne sub full) _ (by omega) _,
    proper (S\T) rest _ (by omega) _]

omit [DecidableEq ι] in
private theorem quiet_vertices (C : Matrix U U ℝ) {R T : Layers ℝ U} {X Y : Layers (Pen D S) U}
    (h a : ℕ) (flat : ∀ j, R j 0=0) (bank : ∀ j i,i≤a → R j i=T j i)
    (lower : ∀ j i,i<a → X j i=Y j i) : ravel C R X h a = ravel C T Y h a := by
  unfold ravel
  apply sum_congr rfl; intro v _
  apply sum_congr rfl; intro w hw
  have total := mem_antidiagonal.mp hw
  rw [←bank v.1 w.1 (by omega)]
  by_cases old : w.1=0
  · rw [old,flat]
    funext r
    rw [arbor_zero_at C _ _ r (fun _ _ _ => Or.inl rfl),
      arbor_zero_at C _ _ r (fun _ _ _ => Or.inl rfl)]
  rw [lower v.2 w.2 (by omega)]

def step (C : Matrix U U ℝ) (R : Layers ℝ U) (X : thalamus D U) (h a : ℕ) (S : Finset ι) :=
  ((h+1 : ℕ):ℝ)⁻¹ • (ripple C (X S h a)+ravel C R (X S) h a+ravel C.transpose R (X S) h a+
    ∑ J∈S.powerset,if sub:J⊆S then sewsV C sub (X J) (X (S\J)) h a else 0)

private theorem diagonal (C : Matrix U U ℝ) {R T : Layers ℝ U} {X Y : thalamus D U}
    (h a : ℕ) (flat : ∀ j,R j 0=0) (bank : ∀ j i,i≤a → R j i=T j i)
    (quietX : ∀ j i,X ∅ j i=0) (quietY : ∀ j i,Y ∅ j i=0)
    (proper : ∀ J ⊂ S,∀ i≤a,∀ j,X J j i=Y J j i)
    (lower : ∀ j i,i<a → X S j i=Y S j i) :
    step C R X h a S-step C T Y h a S =
      ((h+1 : ℕ):ℝ)⁻¹ • (ripple C (X S h a)-ripple C (Y S h a)) := by
  have joint : (∑ J∈S.powerset,if sub:J⊆S then sewsV C sub (X J) (X (S\J)) h a else 0) =
      ∑ J∈S.powerset,if sub:J⊆S then sewsV C sub (Y J) (Y (S\J)) h a else 0 := by
    apply sum_congr rfl; intro J hJ
    have sub := mem_powerset.mp hJ
    rw [dif_pos sub,dif_pos sub,joins C h a quietX quietY proper J sub]
  unfold step
  rw [quiet_vertices C h a flat bank lower,quiet_vertices C.transpose h a flat bank lower,joint]
  funext r x
  simp only [Pi.sub_apply,Pi.smul_apply,Pi.add_apply,smul_add,smul_sub]
  abel

/-- On the original finite Gaussian, one unpaired discrepancy at coupling
grade a is transported by its covariance. The same-charge field rank strictly
drops by two each time the diagonal acts. -/
theorem original (p : PackOne Z D k e I) {S : Finset ι} (h a : ℕ)
    (T : Layers ℝ (Site p.V.n × I.dial)) (Y : thalamus D (Site p.V.n × I.dial))
    (bank : ∀ j i,i≤a → p.V.vault j i=T j i)
    (hush : ∀ j i,Y ∅ j i=0)
    (proper : ∀ J ⊂ S,∀ i≤a,∀ j,p.surfU J j i=Y J j i)
    (lower : ∀ j i,i<a → p.surfU S j i=Y S j i) :
    p.surfU S (h+1) a-step p.N T Y h a S =
      ((h+1 : ℕ):ℝ)⁻¹ • (ripple p.N (p.surfU S h a)-ripple p.N (Y S h a)) := by
  have flat (j : ℕ) : p.V.vault j 0=0 := by
    rw [p.V.vaultTip]
    apply bare_abr
    unfold ScrollV.archCold
    rw [pack_zero _ I.pay]
    rfl
  have quiet (j i : ℕ) : p.surfU ∅ j i=0 := funext (p.zen j i)
  rw [show p.surfU S (h+1) a=step p.N p.V.vault p.surfU h a S from p.more S h a]
  exact diagonal p.N h a flat bank quiet hush proper lower

end YM.Integration.WilsonFiniteMarkedWickDiagonal
