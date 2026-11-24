import YM.FormalOPE.RG10.Ward.TopContact
import YM.FormalOPE.RG10.Balance

/-! Preserve the *representative* equation Wilson coefficients at g[g^-² force − div].

As in kframe, there can be further negative g powers on a proposed X from its stencil slots.
Again ask for actual clearing of such powers (`Approved` below, in the SAME chart prescription).
No restriction for the basic unscaled lift at d=0. `replyCoeff` and the `lower` formula export
already the contact term for RG14 (still finite inversion regulator; RG14 needs further genuine
multicontact continuum limits/estimates; never infer it from a separated observable alone).
Contacts sourced by one previously chosen oriented positive edge. Finite sums can add all the
link components of X. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.InversionWard
open Gauge Lattice RG Wilson MeasureTheory Metric Finset
open PertExtension PertExtension.Orb Function Filter InversionTop PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Radial YM.PertExtension.Series.Tested
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {n : Side} (hn : Even n.val) {b : Edge (Site n)}
    {f : Config G n → ℝ} {Z : Config G n → G.Color} (h : Direction b Z) {d : ℕ}

abbrev pencil (f : Config G n → ℝ) := raw (restrictedO f)
local notation "F" => feed (G:=G) hn
local notation "W" => vertices G n

def unweighted (b : Edge (Site n)) (Z : Config G n → G.Color) :=
  pencil (effort b Z) - delay 2 (pencil (fallout b Z))

def equationMark (d : ℕ) (b : Edge (Site n)) (Z : Config G n → G.Color) : Kernel (Unit × Dir G n) :=
    fun x => lower (d+1) (unweighted b Z x)

def Approved (b : Edge (Site n)) (Z : Config G n → G.Color) (d : ℕ) : Prop :=
    ∀ k ≤ d, row k (unweighted b Z) = 0
lemma approved_identity (p : Approved b Z d) : delay (d + 1) (equationMark d b Z) = unweighted b Z := by
  funext x; apply PowerSeries.ext; intro k; unfold delay
  rw [coeff_X_pow_mul']; unfold equationMark lower; split
  next he => rw [coeff_mk, Nat.add_sub_of_le he]
  next he => exact (congr_fun (p k (by omega)) x).symm

include hn in
lemma approved_zero : Approved b Z 0 := by
  intro i hi; rw [show i=0 from by omega]; funext x
  unfold unweighted row delay pencil raw
  rw [Pi.sub_apply, map_sub, coeff_X_pow_mul', if_neg, sub_zero]
  · have hu : Chart.expLinks G (Cotree n) 0=1 := by funext; simp [PertExtension.Chart.expLinks]
    have hv : restrictedO (effort b Z) (Chart.expLinks G (Cotree n) 0)=0 := by
      change effort b Z (representative 0)=0
      rw [representative_zero, flat_effort hn]
    simp [InversionTop.lift, hv] -- hu issue
  omega

private lemma product_delay {X : Type*} (f v : Kernel X) (d : ℕ) : delay d f * v = delay d (f * v) := by
  funext x; simp [delay, mul_assoc]

section Reply
include hn
lemma product_reply {u : Config G n→ℝ} (p : PreTest u) (hf : PreTest f) :
    (F).Funded ((W).weight * (pencil u * pencil f)) ∧
    (F).step W (pencil u * pencil f) = replyCoeff (u*f) := by
  have hx : pencil (u*f)=pencil u * pencil f:= raw_mul p.curved hf.curved
  rw [← hx]; exact ⟨InversionTop.funded hn (Uses.pre_mul p hf).curved,(expectation_witness hn (Uses.pre_mul p hf)).symm⟩

variable {A : Kernel (Unit × Dir G n)}
include h
/-- Use when stamping one more mark whose representative is an EOM row, *even if the others
overlap it*. Do not compute its value only by the Ward identity. This pays the Laurent/order
conversion of the contact expression before matching rows. -/
theorem keeps_debt {w : ℕ} (p : Approved b Z d) (hf : PreTest f) (hy : Proxy f)
    (hm : Uses.AtCoupling f w A) :
    let K := equationMark d b Z * A
    (F).Funded ((W).weight * K) ∧
    X^(d+1+w) * (F).step W K = X^2 * replyCoeff (coupled b Z f) := by
  intro K; unfold Uses.AtCoupling at hm
  obtain ⟨he₁,he⟩ := product_reply hn h.effort hf
  obtain ⟨hd₁,hd⟩ := product_reply hn h.fallout hf
  have hx := FlatFeed.delayable 2 hd₁
  let A1 := pencil (effort b Z)*pencil f
  let A2 := pencil (fallout b Z)*pencil f
  have hk : delay (d+1+w) K = A1-delay 2 A2 := by
    unfold K; rw [delay_mul, approved_identity p, hm]; unfold unweighted; rw [sub_mul,product_delay]
  refine ⟨FlatFeed.inSpite (d+1+w) ?_,?_⟩
  · rw [hk]; exact FlatFeed.both_sub he₁ hx
  rw [← FlatFeed.step_delay, hk, FlatFeed.step_sub (f:=A1) (b:=delay 2 A2) he₁ hx, FlatFeed.step_delay]
  unfold A1 A2; rw [he, hd, reply_relation hn b h hy hf.gauge]; ring
end Reply

lemma certified_native {V : Type*} {A : V → Stamp G n} {v : Finset V}
    (ha : ∀ i∈v, Proxy (A i).stencil) : Proxy (Stamp.shafts A v) := Proxy.prod v ha

section Words
variable {V : Type*} [DecidableEq V] {A : V → Stamp G n} (v : Finset V)
variable (b Z)
-- auxiliary using erase. payload includes the original auxiliary stamps.
def hitsAt (A : V → Stamp G n) (v : Finset V) (i : V) (b : Edge (Site n)) (Z : Config G n → G.Color) :=
    coupled b Z (A i).stencil * Stamp.shafts A (v.erase i)
private lemma coupled_const : coupled b Z (fun _ => (1:ℝ))=0 := by
  funext U; unfold coupled vary; simp

lemma multiLeibniz (h : ∀ i∈v,Proxy (A i).stencil) :
    coupled b Z (Stamp.shafts A v) = ∑ i∈v, hitsAt A v i b Z := by
  induction v using Finset.induction_on with
  | empty =>
    simp only [Stamp.shafts, prod_empty,sum_empty]; exact coupled_const b Z
  | insert i v hi ih =>
    have hp := fun k hk => h k (mem_insert_of_mem hk)
    have hg:=ih hp
    have hs : Stamp.shafts A (insert i v)=(A i).stencil * Stamp.shafts A v := Finset.prod_insert hi
    rw [hs, show coupled b Z ((A i).stencil*Stamp.shafts A v)= _ from funext (fun U => leibniz b (h i (by simp)) (certified_native hp) U Z)]
    -- std representation
    change coupled b Z (A i).stencil * Stamp.shafts A v + (A i).stencil * coupled b Z (Stamp.shafts A v) = _
    rw [sum_insert hi, hitsAt, erase_insert hi,hg,Finset.mul_sum]
    congr 1
    apply sum_congr rfl; intro j hj
    have he:j≠i:=ne_of_mem_of_not_mem hj hi
    unfold hitsAt Stamp.shafts; rw [erase_insert_of_ne (Ne.symm he), Finset.prod_insert (show i∉v.erase j from fun hh => hi (Finset.mem_of_mem_erase hh))]; ring

variable {b Z} (p : Approved b Z d) (hv : ∀ i∈v, Proxy (A i).stencil)

include hn p h hv
/-- Exact finite-regulator PT coefficient of the equation mark, before any assertion about
separated observational equality. In particular use the **outside** representatives and all
inversion clearance requirements to drop these terms by `excluded` below. -/
theorem chartContact :
    let K := equationMark d b Z * ∏ i∈v, (A i).couplingMark
    (F).Funded ((W).weight * K) ∧
    X^(d+1+Stamp.degrees A v) * (F).step W K = X^2 * ∑ i∈v, replyCoeff (hitsAt A v i b Z) := by
  intro K; obtain ⟨hy,H⟩:= keeps_debt hn h p (Stamp.pre_all A v) (certified_native hv) (Stamp.uses_all A v)

  have hc i (hi:i∈v) : Proxy (hitsAt A v i b Z) := (h.acts.couple b (hv i hi)).mul
    (certified_native (A:=A) (v:=v.erase i) (fun j hj => hv j (Finset.mem_of_mem_erase hj)))
  have hh i (hi:i∈v) : PreTest (hitsAt A v i b Z) := Uses.pre_mul (Direction.contact h (hv i hi) (A i).test.gauge) (Stamp.pre_all A (v.erase i))
  constructor
  · change (F).Funded ((W).weight * (equationMark d b Z * ∏ i∈v, Stamp.factors A i))
    exact hy
  change X^(d+1+Stamp.degrees A v) * (F).step W (equationMark d b Z * ∏ i∈v, Stamp.factors A i) = _
  rw [H, multiLeibniz b Z v hv, reply_sum hn v (fun i : V=>hitsAt A v i b Z) hh hc]

omit hn p h hv in
lemma isolated_hit {i : V} {s : Set (Site n)} (hf : LocalOn s (A i).stencil) (hb : off b s) :
    hitsAt A v i b Z = 0 := by rw [hitsAt, isolated b hf hb, zero_mul]

/-- Equation done ONLY after retaining exact lifts. Assumes disjoint both at variation head and
its inversion partner, on the same period. -/
theorem excluded (s : V → Set (Site n)) (hl : ∀ i∈v, LocalOn (s i) (A i).stencil)
    (hj : ∀ i∈v, off b (s i)) :
    (F).step W (equationMark d b Z * ∏ i∈v, (A i).couplingMark) = 0 := by
  have H := (chartContact hn h v p hv).2; rw [show ∑ i∈v, replyCoeff (hitsAt A v i b Z)=_ from sum_eq_zero (fun i hi => by rw [isolated_hit v (Z:=Z) (hl i hi) (hj i hi), reply_nil hn]), mul_zero] at H
  exact (mul_eq_zero.mp H).resolve_left (pow_ne_zero _ (PowerSeries.X_ne_zero))
end Words
end YM.FormalOPE.RG10.InversionWard
