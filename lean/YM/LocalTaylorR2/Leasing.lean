import YM.LocalTaylorR2.Deck
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Typhos

/-!
# Extra power when the receipts actually buy it

Purchase faithful rates before any summation (adaptation Typhos).
Long-path arrays may be omitted; keep their additional exponent for this
step; not forgetting the actual log in any gap identity. Small constants
or powers on Big-O here *per staged choice of parameters, uniform in geometries via Sales.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}

open Port Channel Next.Foundations Push.AbsoluteSums.Paths
open scoped ENNReal
variable {l:ℕ} {u x α:ℝ}

/-- Exponents of βF-fugacities to be paid (this is ADDITIONAL to the
common price used for estimating log insertions). -/
def leaseRaw (u:ℝ) (c f : Side) : Raw.LogLetter c f → ℝ := Sum.elim (fun _=>3/5) (Sum.elim (fun _=>0) (Sum.elim (fun _=>1/2) (Sum.elim (fun _=>1/2) (fun _=>u))))
def leaseLog (u:ℝ) (c f : Side) : LogIndex c f → ℝ := Sum.elim (leaseRaw u c f) (Sum.elim (fun _=>0) (fun _=>u))
def lease (u:ℝ) (c f : Side) : Alphabet c f→ℝ := Sum.elim (fun _=> u) (Sum.elim (leaseLog u c f) (fun _=>u))
lemma leaseNN (hu:0≤u) (i:Alphabet c f):0≤lease u c f i := by
  unfold lease; rcases i with i|i|i <;> simp only [Sum.elim]; exact hu
  swap; · exact hu
  unfold leaseLog
  rcases i with (i|i|i|i|i|i)|i|i <;> simp only [Sum.elim,leaseRaw] <;> norm_num <;> assumption

lemma leaseHigh {i:LogIndex c f} (he:slowLog c f i ≠ 0) : lease u c f (.inr (.inl i))=u := by
  rcases i with (i|i|i|i|i|i)|i|i <;> simp_all only [slowLog, slowRaw, ne_eq, not_true_eq_false, lease,leaseLog,leaseRaw,Sum.elim]
lemma loosen {ι:Type*} {e:ι→ℝ} (he:∀ i,0≤e i) {d:ι→Support c} {w:ι→ℝ} {E:ι→ℕ} {a v k:ℝ} (hv:1≤v)
    (h: Sales l a u d (fun i=> v^e i*w i) E k): Sales l a u d w E k := by
  have hh i:0≤w i:= nonneg_of_mul_nonneg_right (h.nonneg i) (Real.rpow_pos_of_pos (zero_lt_one.trans_le hv) _)
  refine (one_mul k) ▸ h.shift zero_le_one hh (fun i=> ?_)
  rw [one_mul]; exact le_mul_of_one_le_left (hh _) (Real.one_le_rpow hv (he _))
lemma adjust {q:ℝ} (hx:1≤x) {u:ℝ} : x^u*x^(q-u)=x^q := by rw [← Real.rpow_add (zero_lt_one.trans_le hx), add_sub_cancel]
theorem inherit_leased (G : Gauge) (P : Teller G) (l : ℕ) {a ε : ℝ} (he : 0<ε) (ha : 0≤a)
    (hx : 4*ε < P.top.supportExponent) (hy : 8*ε < P.top.width) (hz : 8*ε < P.below.width) :
    ∃ n : ℕ, ∀ L : Side, n ≤ L.val → ∀ r : ℝ, -(1/2:ℝ) < r → ∀ u : ℝ,
      ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f), S.patch.L=L →
      Intake P T x R →
      ∃ z : LogLetter c f → ℝ, (∀ U V i, |expo T x R U V i| ≤ z i) ∧
        Sales (radiusB x) a ε (Raw.space T l (radiusB x) R) (fun i=>betaF G x L^leaseRaw u c f i*z i) (extra T R) (betaF G x L ^ r) ∧
      ∃ w : ℕ → ℝ, (∀ i U, |R.activities.K i U| ≤ w i) ∧
        Sales (radiusB x) a ε (forcedFoot S.ratio l (radiusB x) R) (fun i=> betaF G x L^u * w i) (forcedExtra R) (betaF G x L ^ r) := by
  obtain ⟨n,hn⟩ := core_bills P l he ha hx
  refine ⟨n,fun L hL r hv u => ?_⟩
  obtain ⟨s,hm,hs⟩ := exists_between hv
  have ht := (Rate.hat (L:=L) (G:=G)).mul_left 2
  have hr := Rate.const (G:=G) (L:=L) P.top.paths
  have hp : 4*ε < P.top.width := by linarith
  have H := Rate.const (G:=G) (L:=L) (1:ℝ)
  filter_upwards [(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1,hn L hL (s-3/5) (r-u) (by linarith), atoms_meet G L 3 l he ha hp ht hr (r:=s) (by push_cast; linarith),
    atoms_meet G L 4 l he ha hp ht hr (r := s-1/2) (by push_cast; linarith),
    atoms_meet G L 2 l he ha hp H (loopBill_rate G L) (r:=s-1/2) (by push_cast; linarith),
    tails_meet G L L 1 l (s:=P.top.clip) (C:=P.top.paths) he (by decide) ha hy ht (s-u),
    tails_meet G L scaleOne L.val l (s:=P.below.clip) (C:=P.below.paths) he L.property ha hz ht (s-u),
    ((Rate.power (G:=G) (L:=L) (a:=s)).mul_left 6) r hs] with x hA hb hc hq hK hU hD h
  intro c f S T R hS hR
  let p := S.ratio
  have hl : p.count = L := hS
  obtain ⟨w,b,H1,H2,H3,H4⟩ := hb S T R hS hR
  let θ := -orientation*R.beta
  have ho : |-orientation|≤1 := by rw [abs_neg,abs_of_nonneg orientation_range.1.le]; exact orientation_range.2
  obtain ⟨hlh,hy'⟩ := hR.window
  have hθ : |θ| ≤ 2*betaF G x L := by
    rw [← hS]; unfold θ; rw [abs_mul, abs_of_nonneg hR.positive.le]
    exact le_trans (mul_le_of_le_one_left hR.positive.le ho) hy'
  have hpaths := hR.cap.paths
  have hF : R.p.threshold = fiery G x L := by rw [hR.received.temp,hS]
  obtain ⟨w₁,e₁,B₁⟩ := hc c f p hl R.path.cubic hpaths.three θ hθ R.p hF
  obtain ⟨w₂,e₂,B₂⟩ := hq c f p hl R.path.quartic hpaths.four θ hθ R.p hF
  rw [hS] at hpaths
  obtain ⟨w₀,e₀,B₀⟩ := hK c f p hl R.path.loop hpaths.two (-orientation) ho R.p hF
  have hu : R.clip = P.top.clip := hR.received.clip.trans hR.ready.high
  rw [hu] at hpaths
  obtain ⟨w₃,e₃,B₃⟩ := hU c f p hl R.path _ hpaths θ hθ
  obtain ⟨_,_,_,hk⟩ := hR.ready.feeds
  obtain ⟨w₄,e₄,B₄⟩ := hD c c (atOne _) rfl T.down _ hk (-θ) (by simpa only [abs_neg] using hθ)
  let z := Sum.elim w (Sum.elim w₁ (Sum.elim w₂ (Sum.elim w₀ (Sum.elim w₃ w₄))))
  let X:= betaF G x L; have hX (u':ℝ): 0≤X^u':=(Real.rpow_pos_of_pos (zero_lt_one.trans_le hA) _).le
  have hHg:= (Sales.together ((boost_price H2 (hX (3/5))).raise (adjust hA).le) (B₁.together (((boost_price B₂ (hX (1/2))).raise (adjust hA).le).together
    (((boost_price B₀ (hX (1/2))).raise (adjust hA).le).together (((boost_price B₃ (hX u)).raise (adjust hA).le).together ((boost_price B₄ (hX u)).raise (adjust hA).le))))))
  refine ⟨z,?_,?_,b,H3,(boost_price H4 (hX u)).raise (adjust hA).le⟩
  · intro U V i
    rcases i with i| (i | (i | (i | (i | i))))
    · dsimp only [z,expo,Sum.elim]; rw [abs_neg]; exact H1 i U
    · exact e₁ ..
    · exact e₂ ..
    · exact e₀ ..
    · dsimp only [expo,z,Sum.elim]; rw [hu]; exact e₃ ..
    dsimp only [expo,z,Sum.elim]
    rw [hR.ready.low,hS]; exact e₄ ..
  convert hHg.raise (hg:=show _ ≤ betaF G x L^r from ?_) using 1
  · rfl
  · funext i; rcases i with i|i|i|i|i|i <;> simp [z,X,leaseRaw]
  · rfl
  linarith only [h,le_abs_self (6*betaF G x L^s)]
end YM.LocalTaylorR2
