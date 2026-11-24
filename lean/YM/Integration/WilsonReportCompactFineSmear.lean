import YM.Integration.WilsonReportFineSmear
import YM.Integration.WilsonReportCompactWindow

/-! The actual signed finite Wilson smear on the translated compact collapse
geometry. The period bound is uniform in the top and arbitrary exterior cells. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportCompactFineSmear
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction
open Next.Rank Next.Rank.Spindle OPE OPE.Yarn OPE.Strobe OPE.Strobe.Vista26
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Ribbons.ManyCopies.Patrol Push.GridApprox
open WilsonReportFineSmear
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {W r D} {n a k N p : ℕ}

private theorem unwrapped (S : Schedule) (u v : Site (S.side N p))
    (inside : 2*‖S.place u-S.place v‖<(S.period p).val) :
    S.place (u-v)=S.place u-S.place v := by
  let w := lift u-lift v
  have lift_eq : lift (u-v)=w := by
    apply lift_eq_iff.mpr
    refine ⟨by simp [w],?_⟩
    intro i
    have coord := PiLp.norm_apply_le (S.place u-S.place v) i
    have coordinate : S.a N*|(w i:ℝ)|≤‖S.place u-S.place v‖ := by
      have eq : S.a N*|(w i:ℝ)|=|(S.place u-S.place v) i| := by
        calc
          _ = |S.a N*(w i:ℝ)| := by rw [abs_mul,abs_of_pos (S.a_pos N)]
          _ = _ := congrArg abs (by
            change S.a N*((lift u i-lift v i:ℤ):ℝ)=S.a N*(lift u i)-S.a N*(lift v i)
            push_cast; ring)
      rw [eq]
      simpa only [Real.norm_eq_abs] using coord
    have c : S.a N*(2*|(w i:ℝ)|) < S.a N*((S.side N p).val:ℝ) := by
      rw [S.span_side]
      linarith only [coordinate,inside]
    have h' := lt_of_mul_lt_mul_left c (S.a_pos N).le
    have z : 2*|w i|<((S.side N p).val:ℤ) := by exact_mod_cast h'
    have z' : |2*w i|<((S.side N p).val:ℤ) := by rw [abs_mul,abs_of_pos (by decide : 0<(2:ℤ))]; exact z
    exact ⟨(abs_lt.mp z').1,(abs_lt.mp z').2.le⟩
  apply PiLp.ext
  intro i
  change S.a N*((lift (u-v) i:ℤ):ℝ)=S.a N*(lift u i)-S.a N*(lift v i)
  rw [lift_eq]
  change S.a N*((lift u i-lift v i:ℤ):ℝ)=_
  push_cast
  ring

private theorem scale_gate (C : Family G) (hG : G.Simple) (B : ℕ) (big : 17≤B) {c : ℝ} (hc : 0<c) :
    ∀ᶠ k : ℕ in atTop,∀ s : ℝ,Real.log (C.path.levels.clock.hatBeta k)^B ≤ s/C.S.a k →
    2*C.S.a k*((C.path.levels.budget k).B^8:ℕ) ≤ s*c := by
  let L := fun k => Real.log (C.path.levels.clock.hatBeta k)
  have growth : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate C.path.levels hG)
  filter_upwards [growth.eventually_ge_atTop (max 1 (2^9/c))] with k high s purchase
  let l := L k
  have h1 : 1≤l := (le_max_left ..).trans high
  have hcL : (2:ℝ)^9≤c*l := by
    have hh := (div_le_iff₀ hc).mp ((le_max_right ..).trans high)
    simpa only [mul_comm] using hh
  have up : (⌈l^2⌉₊:ℝ)≤2*l^2 := by
    linarith only [(Nat.ceil_lt_add_one (sq_nonneg l)).le,one_le_pow₀ h1 (n:=2)]
  have buy : 2*((C.path.levels.budget k).B^8:ℕ)≤c*l^B := by
    change 2*((⌈l^2⌉₊^8:ℕ):ℝ)≤c*l^B
    rw [Nat.cast_pow]
    calc
      _ ≤ 2*(2*l^2)^8 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) up _) (by norm_num)
      _ = (2:ℝ)^9*l^16 := by ring
      _ ≤ (c*l)*l^16 := mul_le_mul_of_nonneg_right hcL (pow_nonneg (zero_le_one.trans h1) _)
      _ = c*l^17 := by ring
      _ ≤ c*l^B := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 big) hc.le
  have sold : l^B*C.S.a k ≤ s := (le_div_iff₀ (C.S.a_pos k)).mp purchase
  calc
    _ = C.S.a k*(2*((C.path.levels.budget k).B^8:ℕ)) := by ring
    _ ≤ C.S.a k*(c*l^B) := mul_le_mul_of_nonneg_left buy (C.S.a_pos k).le
    _ = (l^B*C.S.a k)*c := by ring
    _ ≤ s*c := mul_le_mul_of_nonneg_right sold hc.le

/-- Only the collapsing marked root cluster obeys this support condition;
absolute positions and relative distances of all microscopic exterior fields are free. -/
def supported (C : Family G) {N p n a : ℕ} (K : Set (Points n)) (s : ℝ) (ψ : Test (n+a)) : Prop :=
  ∀ y : Sites C N p n a, ψ (Order.cells C N p y)≠0 → ∃ z∈K, ∃ o : E4,
    ∀ j : Fin n, C.S.place (y (Fin.castAdd a j))=s•z j+o

/-- All actual fine cells of each translated compact signed test satisfy the
physical spacing needed for the native charged-sector estimate at the same k.
The chosen period threshold is even independent of the coarse/fine cutoffs. -/
theorem geometry (C : Family G) (hG : G.Simple) {K : Set (Points n)} (hK : IsCompact K) (hc : K⊆conf n)
    (B : ℕ) (big : 17≤B) :
    ∀ᶠ k : ℕ in atTop, ∀ s : ℝ, 0<s → s≤1 → Real.log (C.path.levels.clock.hatBeta k)^B ≤ s/C.S.a k →
    ∀ᶠ p : ℕ in atTop,∀ N a : ℕ,∀ ψ : Test (n+a), supported C (N:=N) (p:=p) K s ψ →
      ∀ y : Sites C N p n a,ψ (Order.cells C N p y)≠0 → ∀ j l : Fin n,j≠l →
        2*C.S.a k*((C.path.levels.budget k).B^8:ℕ)≤‖C.S.place (y (Fin.castAdd a j)-y (Fin.castAdd a l))‖ := by
  obtain ⟨c,hc,rooms⟩ := Gaps.someGrows C.S hK hc
  obtain ⟨p0,room⟩ := rooms.exists
  obtain ⟨A,cap⟩ := hK.exists_bound_of_continuousOn (f:=fun z : Points n => z) continuous_id.continuousOn
  have wide := tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp C.S.period_strict.tendsto_atTop
  filter_upwards [scale_gate C hG B big hc] with k coarse
  intro s ps unit paid
  filter_upwards [wide.eventually_gt_atTop (4*|A|)] with p period N a ψ origin y hy j l ne
  obtain ⟨z,hz,o,place⟩ := origin y hy
  obtain ⟨i,axis⟩ := room z hz l j (Ne.symm ne)
  have lower : c≤‖z j-z l‖ := by
    have gap : c≤|z j i-z l i| := by simpa [Gaps.distances,Real.dist_eq] using axis (0:ℤ)
    exact gap.trans (by simpa only [Real.norm_eq_abs,PiLp.sub_apply] using PiLp.norm_apply_le (z j-z l) i)
  have bound (l : Fin n) : ‖z l‖≤|A| := (PiLp.norm_apply_le z l).trans ((cap z hz).trans (le_abs_self _))
  have upper : ‖z j-z l‖≤2*|A| := (norm_sub_le ..).trans (by linarith only [bound j,bound l])
  let u := y (Fin.castAdd a j)
  let v := y (Fin.castAdd a l)
  have fixed : ‖C.S.place u-C.S.place v‖=s*‖z j-z l‖ := by
    rw [place j,place l,add_sub_add_right_eq_sub,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos ps]
  have range : 2*‖C.S.place u-C.S.place v‖<(C.S.period p).val := by
    rw [fixed]
    have f := mul_le_of_le_one_left (norm_nonneg (z j-z l)) unit
    change 4*|A|<((C.S.period p).val:ℝ) at period
    linarith only [f,upper,period]
  rw [unwrapped C.S u v range,fixed]
  exact (coarse s paid).trans (mul_le_mul_of_nonneg_left lower ps.le)

/-- The pre-report numerics at every finite cutoff on a compact separated
translated field test, with the true mesh and the original microscopic past. -/
theorem purchased (hG : G.Simple) (hC : C.Makes) (book : Log.OnBudget C.path.levels)
    (citizen : Citizen C W r D) (d : Fin n→ℕ) (t : ℕ) {K : Set (Points n)} (hK : IsCompact K)
    (hc : K⊆conf n) (B : ℕ) (big : 17≤B) :
    ∀ᶠ k : ℕ in atTop,∀ s : ℝ,0<s → s≤1 → Real.log (C.path.levels.clock.hatBeta k)^B ≤ s/C.S.a k →
    ∀ᶠ p : ℕ in atTop,∀ N : ℕ,∀ hk : k<N,∀ v : (j:Fin n)→C.label (d j),
    (∀ j,Spindle.paid C (d j) k N p (v j)≤C.path.levels.clock.hatBeta k^t) →
    ∀ a : ℕ,∀ E : Fin a→C.book.Token,∀ ψ : Test (n+a), supported C (N:=N) (p:=p) K s ψ →
    ‖Order.smears C N p (Fin.append (fun j => ⟨d j,v j⟩) E) ψ-
      ∑ y : Sites C N p n a,weight C ψ y*(sampled hk.le d v E y+offset hk.le d v E y+early hk.le d v E y)‖ ≤
    ∑ y : Sites C N p n a, ‖weight C ψ y‖*((∫ Z,‖exterior E y Z‖ ∂law G (C.side N p) (C.beta N p))*
      Real.exp (-((C.path.levels.budget k).B:ℝ))) := by
  filter_upwards [WilsonReportFineSmear.purchased hG hC book citizen d t, geometry C hG hK hc B big] with k exacts geo
  intro s hs1 hs2 window
  filter_upwards [geo s hs1 hs2 window] with p hit N hk v paid a E ψ support
  exact exacts N p hk v paid a E ψ (hit N a ψ support)

end YM.Integration.WilsonReportCompactFineSmear
end

