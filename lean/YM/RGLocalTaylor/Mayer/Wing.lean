import YM.RGLocalTaylor.Mayer.Ingot

/-!
# Analytic bills, including the supported exceptional decisions

Comparison of the actual integrated log releases to any order in the specified
effective interaction. Keep an exceptional decision at every actual component
meeting a coarse-sector, fine flag/required or alarm head, BEFORE fusing
external errors. Uses all logarithmic heads: in particular it is *not* throwing
out the Gaussian chains, long quadratic pairs or any other log occurrences,
even if some of those can themselves be shown to be coupling-flat; we use their
full prescribed path/field/profile data as input with prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}

open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
namespace Mayer
variable {ρ discount θ K α uJ vJ e : ℝ} {M : ℕ} {p : Molecule S}

/-- The Taylor prescription does not discard bulk logarithmic output on any
mask. On the regular part it keeps all the log kernels without another path
localization. Forced-head (Pack or K) or even regular Head that is a Warning:
charge nothing to the Taylor portion. Important even if the logarithmic label
containing that head is a regular label and the coarse field is at Healthy. -/
def Start (p : Molecule S) := ∀ i∈ p, Exponential i

private lemma noForce {p : Molecule S} (ht:troupe T R Q.halo (radiusB s) p) (hz: p.toLeft=∅) : own p=∅ := by
  refine Finset.not_nonempty_iff_eq_empty.mp ?_
  rintro ⟨i,hp⟩; obtain ⟨v,h⟩:= (R.activities.forced i).inventory_ne
  obtain ⟨z,h,hZ⟩:= ht.2.2 _ hp _ h
  unfold roster Packets.store at h; rw [hz] at h; simp at h

/-- Failed criterion in any true (nonzero-capable) unforced component gets
 either a fine-seed cost or a fine-warning cost. Empty coarse flags don't matter. -/
lemma warns {p : Molecule S} (ht:authorized H p) (he : ¬Start p) : 1≤Cash.numP p ∨ 1≤ (blaze p).card := by
  by_cases hp : p.toLeft.Nonempty
  · obtain ⟨i,hi⟩:= hp
    have hr : 1≤ i.shares:= by rw [← Packets.seeds_card]; exact Finset.card_pos.mpr (ht.2.1.checkpoints _ hi).1
    left; exact hr.trans (show i.shares ≤ Cash.numP p from single_le_sum (f:=Mixed.shares S) (fun _ _=> Nat.zero_le _) (mem_toLeft.mp hi))
  right
  have hV:= not_nonempty_iff_eq_empty.mp hp
  apply card_pos.mpr
  unfold Start at he; push Not at he
  obtain ⟨j,hj,h⟩:= he
  rcases j with j|j|j|j
  · exact (hp ⟨j,mem_toLeft.mpr hj⟩).elim
  · exact (not_nonempty_iff_eq_empty.mpr (noForce ht.2 hV) ⟨j,(Matter.literal p j).mpr hj⟩).elim
  · exact (h ⟨j,rfl⟩).elim
  exact ⟨j,mem_toRight.mpr (mem_toRight.mpr (mem_toRight.mpr hj))⟩

/-- Terms use only the original kernels and the posted (single) sector path.
No analytic continuation beyond the earned agenda. Terms prior to summing
use SAME supports as the labels in the expansion of the true output. -/
def atLeaf (H : Cash W s μ L Q o C T R) (p : Molecule S) (χ: Chi) (M m : ℕ) :=
  if Start p then coefficient p p H (leg H (own p)) χ M m else 0

def excess (H : Cash W s μ L Q o C T R) (p : Molecule S) (χ: Chi) (M : ℕ) : Config G c→ℝ :=
    (native H p).onLog H χ p - ∑ d:Fin (M+1), atLeaf H p χ M d.val

lemma atLeaf0 (hp:p.Nonempty) : atLeaf H p χ M 0=0:= by
  unfold atLeaf; split
  next ht=>
    funext i; unfold coefficient; refine sum_eq_zero ?_
    intro j hj; obtain ⟨v,hv⟩:= hp
    have hu : ∀ i:↥p, 1 ≤ decorOrder j:= fun i=> le_trans (show 1≤ (j i).val+1 from by omega) (single_le_sum (f:=fun i : ↥p=> (j i).val+1) (fun _ _=> Nat.zero_le _) (mem_univ i))
    have h₁:=hu ⟨v,hv⟩; have hf : decorOrder j=0:= (mem_filter.mp hj).2; omega
  rfl

/-- Denominative extra width for summing occupations over all orders. -/
def spreadRate (M : ℕ) (u v : ℝ) := (M+1:ℝ)*(u*v)
lemma spread_pos (h : 1≤ρ) (ht:1≤θ) : 1 ≤ spreadRate M θ ρ :=
  one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_left (Nat.cast_nonneg _)) (one_le_mul_of_one_le_of_one_le ht h)

def marking (_H : Cash W s μ L Q o C T R) (p : Molecule S) := Real.exp (Q.mark L μ s * (Cash.numP p))
lemma marking_ge (H : Cash W s μ L Q o C T R) (p : Molecule S) : 1 ≤ marking H p:=
  Real.one_le_exp (mul_nonneg H.laws.acquired.marked (Nat.cast_nonneg _))

abbrev prenex (Ξ : Utopia H j v d r C' χ) (l M : ℕ) (e uJ θ ρ α : ℝ) (p : Molecule S) :=
  speedBill e uJ α j * Ξ.meant p (l+j) * marking H p * spreadRate M θ ρ ^ p.card

variable {N : Captain H j C' d v Y A b r B q n χ} (h : Awning H N.conduit A b discount e uJ vJ k l)
    (he : Approved K θ j M) (ht : Q.goal L s ≤ K) (hr:ρ*Q.goal L s≤1)
    (ha: 1≤α) (hz : (M+4:ℝ)*r≤α) (hρ: 1≤ρ)
local notation "p₀" => prenex N.conduit l M e uJ θ ρ α p
include h he ha hρ

lemma pn_check : 0≤ p₀:= mul_nonneg (mul_nonneg (mul_nonneg
  (speed_le_check h.earn h.bSc ha) (N.conduit.meant_nonneg ..)) (zero_le_one.trans (marking_ge H p)))
  (pow_nonneg (zero_le_one.trans (spread_pos hρ he.nonneg)) _) where
  speed_le_check {e uJ α:ℝ} (he:0≤e)(hu:0≤uJ)(ha:1≤α):0 ≤ speedBill e uJ α j:=by unfold speedBill; positivity

lemma valuesCarry (hp:authorized H p) : stipend N.conduit p p α uJ e discount (((M+1:ℕ):ℝ)*(θ*ρ)) l N.conduit.tag ≤ p₀:= by
  let D:=(blaze p).card; let t:= marking H p; have hM :1≤t:=marking_ge H p
  have hx: 0 ≤ spreadRate M θ ρ:= zero_le_one.trans (spread_pos hρ he.nonneg)
  have ht:0 ≤ speedBill e uJ α j:= by unfold speedBill; have h':= h.earn; have hy:= h.bSc; positivity
  let X:= N.conduit.meant p (l+j); have hφ:0 ≤ X:= (N.conduit.meant_nonneg ..)
  unfold stipend; push_cast; apply mul_le_mul_of_nonneg_right _ (pow_nonneg hx _)
  calc
    _ = speedBill e uJ α j * X * discount^D:=by unfold X hitFace; rw [Utopia.meant,if_pos ((H.attends p).2 hp.1), N.conduit.remixes,sdiff_self, Finset.bot_eq_empty, Finset.prod_empty]; unfold D; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ((pow_le_one₀ h.nonneg h.small).trans hM) (mul_nonneg ht hφ)
include hr ht hz

lemma leafFunds (U : Config G c) (h' : (roster p).flags=∅)
    (hy:Healthy (Pressure.temp s) (H.unionP p) U) (m:ℕ) :
    Ore U (atLeaf H p χ M m) v ((ρ^m)⁻¹ * p₀) j := by
  let d':= (ρ^m)⁻¹ * p₀; have hD : 0 ≤ d' := mul_nonneg (by positivity) (pn_check h he ha hρ)
  unfold atLeaf; split
  swap; · intro E _ _ _ V x hx hv; exact Brush.zi EventuallyEq.rfl hD zero_le_one
  next hF=>
  intro E _ _ _ V x hx hv
  by_cases hX : authorized H p
  · exact (coeff_cost h he ht hr (z:=p) (f':=leg H (own p)) (w:=N.conduit.tag) (by simp) (by simp) (by simp)
      (Finset.Subset.refl _) hF hz rfl hρ ha h' hy m E V x hx hv).climb (mul_le_mul_of_nonneg_left
      (valuesCarry h he ha hρ hX) (by positivity)) le_rfl
  exact Brush.zi (Eventually.of_forall (fun q=> Finset.sum_eq_zero fun u _=> Insert.onLog_of_forbidden hX ..)) hD zero_le_one

variable (hA : discount ≤ (ρ^(M+1))⁻¹) (hE : Real.exp (- Q.mark L μ s) ≤ (ρ^(M+1))⁻¹)
include hA hE
omit he ht hr ha hz in
private lemma receipt_edge (ht' : ¬Start p) (h' : authorized H p) :
    discount^(blaze p).card ≤ (ρ^(M+1))⁻¹ * marking H p:= by
  have hm := marking_ge H p
  rcases warns h' ht' with hz|hv
  · have hh := Real.exp_le_exp.mpr (show Q.mark L μ s ≤ Q.mark L μ s*(Cash.numP p:ℝ) from le_mul_of_one_le_right H.laws.acquired.marked (by exact_mod_cast hz)); rw [Real.exp_neg] at hE
    exact (pow_le_one₀ h.nonneg h.small).trans (le_trans (Eq.le (by rw [inv_mul_cancel₀ (Real.exp_pos _|>.ne')] : 1=(Real.exp (Q.mark L μ s))⁻¹*Real.exp (Q.mark L μ s))) (mul_le_mul hE hh (Real.exp_pos _).le (by positivity)))
  exact (show discount^(blaze p).card ≤ discount by simpa only [pow_one] using pow_le_pow_of_le_one h.nonneg h.small hv).trans (hA.trans (le_mul_of_one_le_right (by positivity) hm))

lemma excessFunds (U : Config G c) (h': (roster p).flags=∅)
    (hy:Healthy (Pressure.temp s) (H.unionP p) U) :
    Ore U (excess H p χ M) v ((ρ^(M+1))⁻¹ * p₀) j := by
  let X:=N.conduit; let q:=(ρ^(M+1))⁻¹
  have hq:0≤q:=by unfold q; positivity
  have hM : 0≤ q*p₀ := mul_nonneg hq (pn_check h he ha hρ)
  intro E _ _ _ V x hx hv
  by_cases hp : authorized H p
  swap
  · have hh(W:Config G c)(n:Fin (M+1)):atLeaf H p χ M n W=0:=by unfold atLeaf; split; exact Finset.sum_eq_zero fun _ _=> Insert.onLog_of_forbidden hp ..; rfl
    refine Brush.zi (Eventually.of_forall fun i=>?_ ) hM zero_le_one
    dsimp only [Function.comp_apply, excess,Pi.sub_apply]; simp only [Insert.onLog_of_forbidden hp,Finset.sum_apply,hh,sum_const_zero,sub_zero]
  unfold excess atLeaf
  by_cases he' : Start p
  · have hF := remainder_cost h he ht hr (z:=p) (f':=leg H (own p)) (w:=N.conduit.tag) (by simp) (by simp) (by simp)
      (Finset.Subset.refl _) he' hz rfl hρ ha h' hy E V x hx hv; rw [dad (leg H (own p)) H p] at hF
    simpa only [if_pos he'] using hF.climb (mul_le_mul_of_nonneg_left (valuesCarry h he ha hρ hp) hq) le_rfl
  simp_rw [if_neg he',sum_const_zero,sub_zero]
  apply (h.ordinarySlice h' U hy E V x hx hv).climb _ le_rfl
  have hα: r ≤ α:= (le_mul_of_one_le_left (zero_le_one.trans X.active) (show 1 ≤ (M:ℝ)+4 by linarith only [Nat.cast_nonneg (α:=ℝ) M])).trans hz
  have hF:0 ≤ speedBill e uJ r j:=by unfold speedBill; have hh:=h.bSc; have hc:=h.earn; have hf:=X.active; positivity
  have hu : speedBill e uJ r j ≤ speedBill e uJ α j:= by
    unfold speedBill; have hv:=X.active; have hb:=h.bSc; have hK:=h.earn; gcongr
  have ht := receipt_edge h hρ hA hE he' hp
  let u:= X.meant p (l+j); have hx:0≤u:=X.meant_nonneg ..
  let v':= marking H p; have hw :1≤v':= marking_ge H p; let A:=speedBill e uJ α j; have hA:0≤A:= hF.trans hu
  let b:= spreadRate M θ ρ
  calc
    _ ≤ A*u*(q*v'):=mul_le_mul (mul_le_mul_of_nonneg_right hu hx) ht (pow_nonneg h.nonneg _) (mul_nonneg hA hx)
    _ ≤ A*u*(q*v')*b^p.card:= le_mul_of_one_le_right (by positivity) (one_le_pow₀ (spread_pos hρ he.nonneg))
    _ = _:= by change _=q*(A*u*v'*b^p.card); ring
end Mayer
end YM.RGLocalTaylor
