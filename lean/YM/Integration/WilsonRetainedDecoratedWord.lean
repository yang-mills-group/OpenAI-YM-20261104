import YM.Integration.WilsonRetainedMiniatureRoot

/-! Replacing the genuine short interactions in the marked Mayer word.
The original factorials, all unaltered factors, and the rooted weights stay visible. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true

noncomputable section
namespace YM.Integration.WilsonRetainedDecoratedWord

open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open LocalTaylorR2 LocalTaylorR2.Port RGLocalTaylor RGLocalTaylor.Insert RGLocalTaylor.Mayer
open WilsonRetainedMiniatureTaylor
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

private theorem multiply {a b c d u v s t : ℝ}
    (ha : |a|≤u) (hd : |d|≤t) (left : |a-b|≤v-u) (right : |c-d|≤t-s) :
    |a*c-b*d|≤v*t-u*s := calc
  |a*c-b*d| = |(a-b)*d+a*(c-d)| := by ring_nf
  _ ≤ |a-b| *|d|+|a| *|c-d| := by simpa only [abs_mul] using abs_add_le ((a-b)*d) (a*(c-d))
  _ ≤ (v-u)*t+u*(t-s) := add_le_add
    (mul_le_mul left hd (abs_nonneg _) ((abs_nonneg _).trans left))
    (mul_le_mul ha right (abs_nonneg _) ((abs_nonneg _).trans ha))
  _ = v*t-u*s := by ring

private theorem other {a b u v : ℝ} (first : |a|≤u) (gap : |a-b|≤v-u) : |b|≤v := calc
  |b| = |a+(b-a)| := by ring_nf
  _ ≤ |a|+|b-a| := abs_add_le _ _
  _ = |a|+|a-b| := by rw [abs_sub_comm b a]
  _ ≤ u+(v-u) := add_le_add first gap
  _ = v := by ring

private theorem power {a b u v : ℝ} (first : |a|≤u) (gap : |a-b|≤v-u) (n : ℕ) :
    |a^n-b^n|≤v^n-u^n := by
  have bound := other first gap
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ']
    apply multiply first _ gap ih
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) bound n

private theorem product {ι : Type*} (J : Finset ι) (a b u v : ι → ℝ)
    (first : ∀i, |a i|≤u i) (gap : ∀i, |a i-b i|≤v i-u i) :
    |(∏i∈J,a i)-(∏i∈J,b i)|≤(∏i∈J,v i)-(∏i∈J,u i) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | @insert i J hi ih =>
    simp only [prod_insert hi]
    apply multiply (first i) _ (gap i) ih
    rw [abs_prod]
    exact prod_le_prod (fun k _ => abs_nonneg _) (fun k _ => other (first k) (gap k))

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
  {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W s μ C : ℝ} {o : Target.Order G W}
  {R : Rep G f} {H : Cash W s μ L Q o C T R} {team select : Molecule S} {M : ℕ}

def carry (w : Miniature c f → ℝ) (q : LogIndex c f) : ℝ := match q with
  | .inr (.inl k) => w k
  | _ => 0

def filed (H : Cash W s μ L Q o C T R) (p : ℕ) (X : Coat T F) (z : Air f G) (q : LogIndex c f) : ℝ :=
  match q with
  | .inr (.inl k) => Pavilion.mosaics H p (letter k) F X z
  | _ => X.farLog R o.a Q.table z q

def index (start : Start select) (i : ↥select) : LogIndex c f := Classical.choose (start i.val i.property)

def book (u : Decors select M) (w : LogIndex c f → ℝ) (start : Start select) : ℝ :=
  ∏ i : ↥select, Series.mono ((u i).val+1) (w (index start i))

def partners (team select : Molecule S) (f' : Head S → Insert T)
    (X : Coat T F) (z : momentSpace X) : ℝ :=
  ∏ i∈team\select,(f' i).joint X z

def model (H : Cash W s μ L Q o C T R) (p : ℕ) (team : Molecule S) (start : Start select)
    (u : Decors select M) (f' : Head S → Insert T) (X : Coat T F) (z : momentSpace X) : ℝ :=
  partners team select f' X z * book u (filed H p (X.wrapY z.1) z.2) start

theorem sampled (H : Cash W s μ L Q o C T R) (p : ℕ) (w : Miniature c f → ℝ)
    (X : Coat T F) (z : momentSpace X) (hx : X.x=s) (hw : X.width=o.K) (hm : X.manifest)
    (hs : select⊆team) (start : Start select) (u : Decors select M) (f' : Head S → Insert T)
    (healthy : Healthy (Pressure.temp s) (H.unionP team) X.V)
    (paid : ∀ k : Miniature c f,
      Healthy (Pressure.temp X.x) (sleeve S X.B Q.halo k) X.V →
      |Mayer.exponent H (X.wrapY z.1) z.2 (identityLog (letter k)) -
        Pavilion.mosaics H p (letter k) F (X.wrapY z.1) z.2| ≤ w k) :
    |Mayer.planned H team u f' X z - model H p team start u f' X z| ≤
      |partners team select f' X z| * (book u (H.w+carry w) start-book u H.w start) := by
  let Y := X.wrapY z.1
  let a (i : ↥select) := exponent H Y z.2 i.val
  let b (i : ↥select) := filed H p Y z.2 (index start i)
  let t (i : ↥select) := H.w (index start i)
  let e (i : ↥select) := carry w (index start i)
  have here i : badge S (index start i)=i.val := Classical.choose_spec (start i.val i.property)
  have hA (i : ↥select) : |a i|≤t i := by
    dsimp only [a,t]
    rw [← here i]
    exact ((H.quotes F Y hx hw hm).2.1 (index start i) z.2).1
  have hE (i : ↥select) : |a i-b i|≤(t i+e i)-t i := by
    rw [add_sub_cancel_left]
    dsimp only [a,b,e]
    rw [← here i]
    generalize hq : index start i=q
    rcases q with q|(k|q)
    · simp [exponent,carry,filed]
    · apply paid k
      have body : Healthy (Pressure.temp s) (H.supportP i.val) X.V :=
        Finset.disjoint_of_subset_left (subset_biUnion_of_mem H.supportP (hs i.property)) healthy
      rw [← here i,hq] at body
      change Healthy (Pressure.temp X.x) (sleeve S (radiusB X.x) Q.halo k) X.V
      rw [hx]
      exact body
    · simp [exponent,carry,filed]
  let n (i : ↥select) := (u i).val+1
  have full := product (univ : Finset (↥select))
    (fun i => Series.mono (n i) (a i)) (fun i => Series.mono (n i) (b i))
    (fun i => Series.mono (n i) (t i)) (fun i => Series.mono (n i) (t i+e i)) (by
      intro i; simp only [Series.mono,abs_div,abs_pow,abs_of_nonneg (show 0≤((n i).factorial:ℝ) from Nat.cast_nonneg _)]
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hA i) _) (Nat.cast_nonneg _)) (by
      intro i; simp only [Series.mono,←sub_div,abs_div,abs_of_nonneg (show 0≤((n i).factorial:ℝ) from Nat.cast_nonneg _)]
      exact div_le_div_of_nonneg_right (power (hA i) (hE i) _) (Nat.cast_nonneg _))
  unfold planned model partners
  rw [← mul_sub,abs_mul]
  exact mul_le_mul_of_nonneg_left full (abs_nonneg _)

end YM.Integration.WilsonRetainedDecoratedWord
end
