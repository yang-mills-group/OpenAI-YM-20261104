import YM.FVA1.SlotTests
import YM.Gaps1020.Local.Panel

/-!
# Addressed, unextracted regular/mixed log and force, on the existing Rep

Use a finite set of physical slots (including potentially replicated slots),
and smooth tests in a separately declared convention. Test footprints at a mesh
are the physical slot roots (e.g. when staying inside the native centered cell) plus
any further needed native stencils/halos; local rules producing Film can
prescribe those per slot. Charge differences in origins/support data, not just
size as functions of links.

The full unnormalized polynomial uses only the exact existing predicates and
actual unmarked Rep. There is no division by a K coefficient or sector.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVA1
open MeasureTheory Finset Function Filter Lattice Wilson RG RG05.Strand Extra.Trajectories
open Marker Overlay Overlay.GapsLocal Push.GridApprox.Nil MergeProof.Accent
open Push Push.AbsoluteSums
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {T I V:Type} [DecidableEq V]{Γ:Census V}
variable {G:Gauge}{n:Side}

/-- A balanced unit-test convention (lossy absorption is only needed for existence
of sums away from the unit-test calculation). -/
structure Controls (V T:Type) [SMul ℂ T] where
  available : V → T → Prop
  absorb (i : V) (t:T) : ∃ (c:ℂ)(y:T),t=c • y ∧ available i y

def Controls.Admits [SMul ℂ T] (C:Controls V T) (x:V→T) : Prop := ∀ i, C.available i (x i)

/-- Periodic support bookkeeping. No shape bound on the period and no
restriction to nonwrapping coefficients in these mixed estimates. The address stubs
must live on the torus already and Fit.inside/insideK will require them on
every charged coefficient carrying their mark. We do NOT derive any winding tail
from periodic evaluation alone. -/
structure Positions (V:Type)(n:Side) where
  origin : V → Site n
  stub : V → Support n
  mem (v) : origin v ∈ stub v

structure Film (I T:Type){V:Type}[DecidableEq V](Γ:Census V) {G:Gauge}{n:Side}(R:Rep G n) where
  tape : Positions V n
  surround : I → Support n
  header : V→(V→T)→ℂ
  soft : (V→T)→ I→Γ.Mode → Config G n→ℂ
  gas : (V→T)→ℕ → Config G n→Poly Γ

namespace Film
variable {R:Rep G n} (D:Film I T Γ R)

def glass (x:V→T)(i:I)(U:Config G n):Poly Γ :=
  Poly.inject fun j=> masked R.p.threshold (D.surround i) (D.soft x i j) U

def extra [Fintype V](x:V→T)(U:Config G n):Poly Γ :=
  Mach Γ (fun i=>D.header i x)+ ∑' i,D.glass x i U

def packet (x:V→T)(i:Finset ℕ)(U:Config G n): Poly Γ :=
  if R.activities.admissible R.p U i then ∏ k∈ i,D.gas x k U else 0

def density [Fintype V](x:V→T)(U:Config G n):Poly Γ := (Real.exp (R.exponent U):ℂ) •
  (Poly.pass (D.extra x U)*∑' i,D.packet x i U)

variable [AddCommGroup T][Module ℂ T]
local notation "p0" => R.p

/-- Tested format. Scalar dependence alone doesn't need a support on links.
`inside` and `insideK` see native root/stub data in one periodic presentation
(shared across all occurrences of a slot), not only evaluations. -/
structure Fit : Prop where
  nonvac (i:I) : (D.surround i).Nonempty
  lead (i:V) : SlotLinear ({i}:Finset V) (D.header i)
  smooth (x i z) : (p0).Regular (D.surround i) (D.soft x i z)
  beam (i z U) : SlotLinear z.val (fun x=>D.soft x i z U)
  mute (x i) : D.soft x i Γ.quiet = 0
  inside (x i z v) : v∈z.val → D.soft x i z ≠0 → D.tape.stub v ⊆ D.surround i
  beamK (i U z) : SlotLinear z.val (fun x=>(D.gas x i U).part z)
  native (x i U) : (D.gas x i U).part Γ.quiet=(R.activities.K i U:ℂ)
  flow (x i) : Flow D.tape.origin (MergeProof.barcode R.activities i) (D.gas x i) R.p.threshold
  insideK (x i U z v) : v∈z.val → (D.gas x i U).part z ≠0 → D.tape.stub v ⊆ (R.activities.forced i).support
  eligible (x i U) : D.gas x i U≠0 → (R.activities.forced i).eligible R.p.threshold U

set_option quotPrecheck false
local notation "K0" => fun i:ℕ=>(R.activities.forced i).support

/-- Complete stronger (all-site) hit norm with sup over independent smooth tests *inside*:
for every occurrence and every mode require common witnesses e/b irrespective of
admitted tests, with the indicated order, all anchors on that support, and the full
per-mode price also on K (including its actual quiet label). -/
structure Pays (C:Controls V T)(w:V→ℝ) (supportFee headerFee regularFee forceFee sqrtW:ℝ) : Prop where
  basis : ∀ i,0 < w i
  marker : 0<sqrtW
  extraSupport : (p0).supportExponent ≤ supportFee
  localU : ∀ i x, C.Admits x → w i * ‖D.header i x‖ ≤ headerFee
  bulk : ∃ e:I→Sheet Γ,
    (∀ i,0≤ e i) ∧
    Ac.Hit D.surround (p0).B (fun i=>wordsPrice w (e i)) supportFee regularFee ∧
    ∀ i x, C.Admits x → ∀ z a, a∈D.surround i → (p0).supBounds a (D.surround i) (D.soft x i z) (e i z)
  wind : ∃ b:ℕ→ Sheet Γ,
    (∀ i,0 ≤ b i) ∧
    Ac.Hit (K0) (p0).B (fun i=>wordsPrice w (b i)) supportFee (forceFee*sqrtW) ∧
    ∀ i x, C.Admits x → ∀ U z, ‖(D.gas x i U).part z‖ ≤ b i z

omit [AddCommGroup T] [Module ℂ T] in
lemma sum_words_pos (w:V→ℝ)(hw:∀ i,0<w i) (x:Sheet Γ)(h:0≤x): 0 ≤ wordsPrice w x:=
  Finset.sum_nonneg fun i _=> mul_nonneg (Poly.worth hw i).le (h _)

omit [AddCommGroup T] [Module ℂ T] [DecidableEq V] in
lemma shrink_hit (X:I→ Support n)(B:ℕ){f g:I→ℝ}{p q c:ℝ}(hp:∀ i,0≤g i)(hf:∀ i,g i ≤ f i)(h:Ac.Hit X B f p c)(he:q ≤ p): Ac.Hit X B g q c:=by
  intro v; refine budget_mono (h v) (fun i=> ?_) (fun i=> ?_)
  · split; exacts [mul_nonneg (hp _) (Real.exp_pos _).le,le_rfl]
  split; next h =>
    exact mul_le_mul (hf _) (Real.exp_monotone (mul_le_mul_of_nonneg_right he (by positivity))) (Real.exp_pos _).le ((hp i).trans (hf _))
  next _=> exact le_rfl

omit [AddCommGroup T] [Module ℂ T] [DecidableEq V] in
lemma hit_sum (X:I→Support n)(B:ℕ){p b:ℝ} {f:I→ℝ} (h:Ac.Hit X B f p b)(he:0≤p)(hf:∀ i,0≤f i)(hX:∀ i,(X i).Nonempty): Summable f:=by
  -- finite-volume use only to get existence
  let F (x:Site n)(i:I):=if x∈X i then f i * Real.exp (p*coverNumber B (X i)) else 0
  refine (summable_sum (s:=Finset.univ) (f:=F) (fun x _=>(h x).2.1)).of_nonneg_of_le hf (fun i=> ?_)
  obtain ⟨x,hx⟩:=hX i
  have hh:F x i≤∑ j,F j i:= Finset.single_le_sum (fun j _=> (h j).1 _) (Finset.mem_univ _)
  apply le_trans _ hh; unfold F; rw [if_pos hx]; exact le_mul_of_one_le_right (hf i) (Real.one_le_exp (mul_nonneg he (by positivity)))

-- Move from all-field to all-admissible unit tests, retaining explicit coordinates.
variable {D}
lemma needed {C:Controls V T}{w:V→ℝ}{p a b c k:ℝ}(h:D.Fit)(he:D.Pays C w p a b c k)(x:V→T)(hx:C.Admits x)(U:Config G n) : Summable (fun i=>D.glass x i U):=by
  obtain ⟨u,hu,hP,hF⟩:=he.bulk; let F i:= wordsPrice w (u i)
  have hQ(i):0≤ F i:= sum_words_pos w he.basis _ (hu i)
  have hv:0 ≤ p:=le_trans R.p.exponent_pos.le he.extraSupport
  have ht:= hit_sum D.surround R.p.B hP hv hQ h.nonvac
  refine (Poly.budgeted he.basis ht (f:=fun i=>D.glass x i U) ?_).1
  intro i; refine Finset.sum_le_sum fun j _=> mul_le_mul_of_nonneg_left ?_ (Poly.worth he.basis _).le
  change ‖masked R.p.threshold _ _ _‖≤ u i j; by_cases hh:Healthy R.p.threshold (D.surround i) U
  · obtain ⟨y,hy⟩:= h.nonvac i; rw [masked_eq _ _ _ _ hh]; exact ((hF i x hx j y hy).2 U hh [] (by simp) (by simp))
  rw [masked_ne _ _ _ _ hh, norm_zero]; exact hu _ _

lemma fit_surface [Nonempty V] [Countable I](h:D.Fit)(x:V→T): (surface R D.surround D.tape.origin (fun i=> D.header i x) (D.soft x) (D.gas x)).Active:=by
  refine displayed R _ _ _ _ _ ?_ (h.smooth x) ?_ (fun i=>(h.flow x i).toBorne)
  · intro i v hv; by_contra he
    exact hv fun k hk=> h.inside x i v.val k hk he (D.tape.mem _)
  intro i U h'; exact Decidable.not_not.mp (mt (h.eligible x i U) h')

lemma pay_surface [Nonempty V] [Countable I]{C:Controls V T}{w:V→ℝ}{p a b c k:ℝ}(h:D.Fit)(he:D.Pays C w p a b c k)(x:V→T)(hx:C.Admits x):
    (surface R D.surround D.tape.origin (fun i=> D.header i x) (D.soft x) (D.gas x)).Radial w a b c k:=by
  obtain ⟨u,hu,hP,hF⟩:=he.bulk
  obtain ⟨v,hv,hQ,hK⟩:=he.wind
  let f i:=wordsPrice w (v i)
  let S:= fun i=> (R.activities.forced i).support
  have hs(i):(S i).Nonempty:= (R.activities.forced i).inventory_ne.mono (R.activities.forced i).inventory_sup
  have hd (i):0 ≤ f i:= sum_words_pos w he.basis _ (hv i)
  have hb : Towed w S (D.gas x) R.p.B R.p.supportExponent (c*k):=
    ⟨f,hit_sum S R.p.B hQ (R.p.exponent_pos.le.trans he.extraSupport) hd hs,
      shrink_hit S _ hd (fun _=>le_rfl) hQ he.extraSupport,fun i=>⟨v i,hv i,hK i x hx,le_rfl⟩⟩
  exact Overlay.GapsLocal.funds R _ _ _ _ _ (fun i v hv=>by
    by_contra hy; exact hv fun j hj=> h.inside x i v.val j hj hy (D.tape.mem _)) (fun i=>(h.flow x i).toBorne) w he.basis a b c k hb (fun i=>he.localU i x hx) he.marker u (hu ·)
      (shrink_hit D.surround _ (fun i=>sum_words_pos w he.basis _ (hu i)) (fun _=>le_rfl) hP he.extraSupport)
      (fun i=> hF i x hx)

lemma evaluates_surface [Fintype V] [Nonempty V] [Countable I]{C:Controls V T}{w:V→ℝ}{p a b c k:ℝ}(h:D.Fit)(he:D.Pays C w p a b c k)(x:V→T)(hx:C.Admits x):
    (surface R D.surround D.tape.origin (fun i=>D.header i x) (D.soft x) (D.gas x)).density = D.density x:=by
  funext U; unfold Bands.density density
  let hp(i:I)(z:Said Γ) (hh:¬ pinned D.tape.origin (D.surround i) z) : D.soft x i z.val=0:=by
    by_contra H; exact hh (fun j hj=> h.inside x i z.val j hj H (D.tape.mem _))
  rw [atAll R _ _ _ _ _ hp w a b c k _ (fit_surface h x) (pay_surface h he x hx)] -- hp implicit?
  congr 2
  · unfold extra Mach; apply congrArg Poly.pass; apply congrArg (_+·); refine tsum_congr fun i=> ?_
    let f j:=Poly.send j (masked R.p.threshold (D.surround i) (D.soft x i j) U)
    let L:=univ.filter (fun z:Γ.Mode=> z.val.Nonempty); let ψ:=D.glass x i U
    change (∑ j:Said Γ,f j.val)=ψ
    rw [← Finset.sum_subtype L (by simp [L]) f, Finset.sum_subset (f:=f) (Finset.subset_univ L) ?_]
    · exact Poly.studs ψ
    intro j _ hj; have hz:j=Γ.quiet:=Subtype.ext (not_nonempty_iff_eq_empty.mp (fun hh=>hj (by simp [L,hh])))
    rw [hz]; unfold f; rw [h.mute x i]; simp [masked]
  unfold Bands.cluster
  refine tsum_congr fun i=> ?_; unfold Bands.packet packet; split
  · exact prod_congr rfl fun j _=>everyK R _ _ _ _ _ (h.native x) U j
  rfl
end Film
end YM.FVA1
