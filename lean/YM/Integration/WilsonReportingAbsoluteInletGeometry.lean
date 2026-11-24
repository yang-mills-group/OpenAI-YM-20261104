import YM.Integration.WilsonPhysicalExteriorMeshStops
import YM.Integration.WilsonAdmissionScale

/-! The original Nat.find, margin, geometric span and inlet proof extracted
together on the selected physical field. The source map records the four
historical proof bodies and the one internal namespace substitution. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonReportingAbsoluteInletGeometry
open Function Filter Finset Real Lattice RG Wilson RG16 RG16.Literal
open PhysicalNext.Repeat.Legato WilsonPhysicalExteriorMeshStops
open scoped Classical BigOperators Topology
variable {G:Gauge}

def width (p : ℕ) : ℝ := (5/2:ℝ)*(((p+1:ℕ):ℝ)/2+1)

theorem positive (p : ℕ) : 0<width p := by unfold width;positivity

theorem margins (R : Run G) (hG : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    {c γ : ℝ} (hc : 1<c) (hγ : 0<γ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∀ᶠ k : ℕ in atTop, let u := ultraviolet R.family c k
      k ≤ u ∧ t*G.slopeConstant ≤ γ*R.family.path.levels.clock.hatBeta k ∧
      (s+t)*log (R.family.path.levels.clock.hatBeta k) ≤ γ*(R.family.S.scale u-R.family.S.scale k) := by
  let C := R.family
  let L := Lambda C.path.levels
  have grow := ((tendsto_rpow_atTop (sub_pos.mpr hc)).comp (lambda_leads C hG)).eventually_ge_atTop ((s+t)/γ)
  filter_upwards [grow,(WardBin.bell C.path.levels hG).eventually_ge_atTop (t*G.slopeConstant/γ),
    ultraviolet_window C hG slow.2 c] with k hpow heat span
  have L0 : 0 < L k := lambda_pos C k
  have logL : log (C.path.levels.clock.hatBeta k) ≤ L k := by dsimp [L,Lambda]; linarith
  have exponent : (L k)^(c-1) * L k = (L k)^c := by
    calc
      _ = (L k)^(c-1)*(L k)^(1:ℝ) := by rw [rpow_one]
      _ = (L k)^((c-1)+1) := (rpow_add L0 _ _).symm
      _ = _ := by rw [sub_add_cancel]
  have spend : s+t ≤ (L k)^(c-1)*γ := (div_le_iff₀ hγ).mp hpow
  refine ⟨span.1.le,?_,?_⟩
  · simpa only [mul_comm] using (div_le_iff₀ hγ).mp heat
  calc
    _ ≤ (s+t)*L k := mul_le_mul_of_nonneg_left logL (add_nonneg hs ht)
    _ ≤ ((L k)^(c-1)*γ)*L k := mul_le_mul_of_nonneg_right spend L0.le
    _ = γ*(L k)^c := by rw [mul_comm ((L k)^(c-1)) γ,mul_assoc,exponent]
    _ ≤ _ := mul_le_mul_of_nonneg_left span.2.1 hγ.le

/-- The terminal stable debit is flat to every order in the actual coupling
    at the reporting level, uniformly in all physical cutoffs and periods. -/

def level (R : Run G) (p u : ℕ) :=
  R.family.S.scale u-width p*log (R.family.path.levels.clock.hatBeta u)

private theorem passes (R : Run G) (p u : ℕ) : ∃j,level R p u<R.family.S.scale (j+1) := by
  obtain ⟨j,hit⟩ := (R.family.S.divergent.eventually_gt_atTop (level R p u)).exists
  exact ⟨j,hit.trans_le ((OPE.scale_mono _).monotone j.le_succ)⟩

def inlet (R : Run G) (p u : ℕ) := Nat.find (passes R p u)

theorem located (R : Run G) (p : ℕ) {k u : ℕ} (early : R.family.S.scale k≤level R p u) :
    let t:=inlet R p u
    k≤t ∧ t<u ∧ R.family.S.scale t≤level R p u ∧ level R p u<R.family.S.scale (t+1) := by
  intro t
  have hit : level R p u<R.family.S.scale (t+1) := Nat.find_spec (passes R p u)
  have before : R.family.S.scale t≤level R p u := by
    cases ht:t with
    | zero =>
      rw [R.family.S.scale_zero]
      simpa only [R.family.S.scale_zero] using ((OPE.scale_mono R.family.S).monotone (Nat.zero_le k)).trans early
    | succ h =>
      exact le_of_not_gt (Nat.find_min (passes R p u) (show h<t by omega))
  have kt : k≤t := by
    by_contra! h
    exact (not_lt_of_ge early) (hit.trans_le ((OPE.scale_mono _).monotone h))
  have loss : 0<width p*log (R.family.path.levels.clock.hatBeta u) :=
    mul_pos (positive p) (log_pos (R.family.path.levels.fits.delayed u))
  have tu : t<u := by
    by_contra! h
    have earlier := (OPE.scale_mono R.family.S).monotone h
    unfold level at before
    linarith only [earlier,loss,before]
  exact ⟨kt,tu,before,hit⟩

theorem reachable (R : Run G) (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    {c : ℝ} (hc : 1<c) (p : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀u≥ultraviolet R.family c k,R.family.S.scale k≤level R p u := by
  let W:=width p
  let θ:=R.family.path.levels.clock.hatBeta
  have w0 : 0<W := positive p
  filter_upwards [margins R simple slow hc (γ:=1) zero_lt_one
    (s:=0) (t:=2*W) le_rfl (by positivity)] with k receipt
  intro u ub
  let Δ:=R.family.S.scale u-R.family.S.scale k
  have θpos (j) : 0<θ j := zero_lt_one.trans (R.family.path.levels.fits.delayed j)
  have kΔ : 0≤Δ := sub_nonneg.mpr ((OPE.scale_mono _).monotone (receipt.1.trans ub))
  have clock : θ u-θ k=G.slopeConstant*Δ := by change (_+_*(R.family.S.scale u))-(_+_*(R.family.S.scale k))=_;unfold Δ;ring
  have drift : log (θ u) - log (θ k)≤G.slopeConstant*Δ/θ k := by
    rw [←clock,←log_div (θpos u).ne' (θpos k).ne']
    apply (log_le_sub_one_of_pos (div_pos (θpos u) (θpos k))).trans_eq
    field_simp [(θpos k).ne']
  have rate : W*G.slopeConstant/θ k≤1/2 := by
    refine (div_le_iff₀ (θpos k)).mpr ?_
    linarith only [receipt.2.1]
  have rise : W*(log (θ u)-log (θ k))≤Δ/2 := calc
    _ ≤ W*(G.slopeConstant*Δ/θ k):=mul_le_mul_of_nonneg_left drift w0.le
    _ = (W*G.slopeConstant/θ k)*Δ := by ring
    _ ≤ (1/2:ℝ)*Δ := mul_le_mul_of_nonneg_right rate kΔ
    _ = _ := by ring
  have start : 2*W*log (θ k)≤Δ :=
    (show 2*W*log (θ k)≤R.family.S.scale (ultraviolet R.family c k)-R.family.S.scale k by
      simpa only [zero_add,one_mul] using receipt.2.2).trans (sub_le_sub_right ((OPE.scale_mono _).monotone ub) _)
  change _≤R.family.S.scale u-W*log (θ u)
  dsimp only [Δ] at start rise
  linarith only [start,rise]

variable (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)

include slow in
theorem block (i:ℕ):
    R.family.S.scale (i+1) ≤ R.family.S.scale i+log (R.family.path.levels.clock.hatBeta i):=by
  let b:=R.family.path.levels.clock.hatBeta i
  let t:=log b
  have b1:1 < b:=R.family.path.levels.fits.delayed i
  have b0:0 < b:=zero_lt_one.trans b1
  have t0:0 < t:=log_pos b1
  have cb:((R.family.S.block i).val:ℝ) ≤ log (2+t):=slow.2 i
  have spent:log (2+t) ≤ b:=by
    have hl:=log_le_sub_one_of_pos (show 0 < 2+t by linarith only [t0])
    have hb:t ≤ b-1:=log_le_sub_one_of_pos b0
    linarith only [hl,hb]
  have inc:log ((R.family.S.block i).val:ℝ) ≤ log b:=
    log_le_log (by exact_mod_cast (R.family.S.block i).property) (cb.trans spent)
  rw [R.family.S.scale_succ]
  exact add_le_add le_rfl inc

private theorem blocks (S:Schedule)(k n:ℕ):(n:ℝ)*log 3 ≤ S.scale (k+n)-S.scale k:=by
  induction n with
  | zero=>simp
  | succ n ih=>
    have b:log (3:ℝ) ≤ log ((S.block (k+n)).val:ℝ):=log_le_log (by norm_num) (by exact_mod_cast S.block_large (k+n))
    rw [←Nat.add_assoc,S.scale_succ,Nat.cast_succ,add_mul,one_mul]
    linarith only [b,ih]

include simple slow in
theorem original {c:ℝ}(hc:1 < c)(P:ℕ):∀ᶠ k:ℕ in atTop,∀u,ultraviolet R.family c k ≤ u →
    let t:=inlet R P u
    k ≤ t ∧ t < u ∧ ∀i,t ≤ i → i ≤ u+1 →
      u+1 ≤ ultraviolet R.family 2 i ∧
      (((u+1-i:ℕ):ℝ)*log 3 ≤ R.family.S.scale (u+1)-R.family.S.scale i) ∧
      R.family.S.scale (u+1)-R.family.S.scale i ≤ (width P+2)*log (R.family.path.levels.clock.hatBeta u):=by
  obtain ⟨a,crowd⟩:=eventually_atTop.mp (reachable R simple slow (c:=2) (by norm_num) (P+1))
  filter_upwards [eventually_ge_atTop a,reachable R simple slow hc P] with k ak paid u live t
  obtain ⟨kt,tu,_,hit⟩:=located R P (paid u live)
  have hit':R.family.S.scale u-width P*log (R.family.path.levels.clock.hatBeta u) < R.family.S.scale (t+1):=hit
  have step:=block R slow t
  have mono:log (R.family.path.levels.clock.hatBeta t) ≤ log (R.family.path.levels.clock.hatBeta u):=
    WilsonAdmissionScale.logarithm_monotone R.family.path.levels simple tu.le
  have bu:0 < log (R.family.path.levels.clock.hatBeta u):=log_pos (R.family.path.levels.fits.delayed u)
  have delta:width (P+1)=width P+5/4:=by unfold width;push_cast;ring
  have strict:level R (P+1) u < R.family.S.scale t:=by
    unfold level;rw [delta];linarith only [hit',step,mono,bu]
  refine ⟨kt,tu,?_⟩
  intro i ti iu
  have si:R.family.S.scale t ≤ R.family.S.scale i:=(OPE.scale_mono R.family.S).monotone ti
  have ahead:u < ultraviolet R.family 2 i:=by
    by_contra! h
    exact (not_lt_of_ge (crowd i ((ak.trans kt).trans ti) u h)) (strict.trans_le si)
  have count:=blocks R.family.S i (u+1-i)
  rw [show i+(u+1-i)=u+1 by omega] at count
  refine ⟨ahead,count,?_⟩
  linarith only [hit',step,mono,si,block R slow u]

end YM.Integration.WilsonReportingAbsoluteInletGeometry
