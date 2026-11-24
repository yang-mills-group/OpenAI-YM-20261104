import YM.Qlocal.Moonset.Arise
/-!
Analytic / REAL cost interface after transferring a model layout: on any currency by same
stencil cost, preserves the masks using any chosen momentum cut. This identifies the series
printed through order positions (*not* perturbed series around actual fields after rendering).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Moonset
open Function Filter Wilson Lattice RG Gauge Push.AbsoluteSums Finset Marker
open AllOrder AllOrder.Floe AllOrder.Floe.Pace
open Quipu Quipu.Sonnet Quipu.Sonnet.Tern Quipu.Eluder
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {V:Type} [Fintype V][DecidableEq V] {R:Marker.Census V} {G:Gauge}
variable {g:V→ℕ}{p N i k L:ℕ}(Y : Stanza R G g p)
variable {t a C : ℝ}
open Dialect
variable (s:Senses R) {n: Side} (o:V → Site n) (Z : ℕ → Prop) (N:ℕ)
set_option quotPrecheck false
local notation "C'" => Lagger.dues g s.val
local notation "T" => Stanza.son Y N
local notation "K" => p+C'+1
local notation "D" => Stack.selector (T) Z
local notation "f" => draw Y s
variable (x : Config G n)(t:ℝ)
lemma enumerate : (T).markℓ (D) o s t x = ∑ i∈range (p+1), ∑ k∈range (p+C'+1), t^(i+C'-k) * (draw Y s i k Z o N x) := by
  let g i k:= t^(i+C'-k)*f i k Z o N x
  unfold Tale.markℓ
  rw [← Fin.sum_univ_eq_sum_range]; change ∑ i:Fin (p+1), _ = _
  refine Finset.sum_congr rfl fun i hi=> ?_
  rw [← Finset.sum_subset (s₁:=range (i.val+C'+1)) (Finset.range_mono (by omega)) ?_]; swap
  · intro k _ h; rw [below Y s o Z N (hx:=by intro hi; exact h (mem_range.mpr (Nat.lt_succ_of_le hi.2)))]; simp
  rw [← Fin.sum_univ_eq_sum_range]; change (∑ k:Fin (i.val+C'+1),_)=_
  refine Finset.sum_congr rfl fun k _ => ?_; rw [treaty]; rfl
noncomputable def worth (g:ℝ)(e r:ℕ):ℝ:= g^e / g^r
lemma exchange (i k : ℕ) (hk : k  ≤  i+C') (ht:0<t) : t^(i+C'-k)/t^C' = worth t i k := by
  unfold worth; have h₁ : i+C'-k+k=i+C':= by omega
  have h : t^(i+C'-k)*t^k=t^i*t^C':=by rw [← pow_add,h₁,pow_add]
  field_simp; exact h.trans (mul_comm ..)
lemma price_recovered (ht:0<t) : Tale.wake s (T) (D) o t x = ∑ i∈range (p+1), ∑ k∈range (p+C'+1), worth t i k * (draw Y s i k Z o N x) := by
  rw [Tale.notationW, enumerate]; simp_rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun i hi=> Finset.sum_congr rfl (fun k _=> ?_))
  by_cases hk:k  ≤  i+C'
  · rw [← Moonset.exchange (g:=g) s t i k hk ht]; ring_nf; rfl
  rw [below Y s o Z N (hx:=fun h=> hk h.2)]; simp

open Precision Exterior PertExtension.Series
open Incline Bookworm Primitives.TwoWave Primitives.TwoWave.RealSlice AllOrder.Ker
open Comparison.RG02 Comparison.RG02.Assembly
local notation "X" => fieldDir G n 1
local notation "Π" => rule (Coarse G) n
noncomputable abbrev art (Y:Stanza R G g p) (s:Senses R)(o:V→Site n)(Z:ℕ→Prop)(N i k:ℕ) := draw Y s i k Z o N ∘ Precision.represent
local notation "φ" => art Y s o Z N
-- use the norm horizon & Contact at truly any order.
variable (hp:(Stanza.son Y N).Allows a C)(ha:0<a)
include hp ha
lemma contact (i k : ℕ) : GradeAt k (art Y s o Z N i k) :=
 Album.rank (x:=o (Sonnet.root s)) (p:=fun t=> Stack.history Z (book Y s i k) t ∧ Bay.Hears ((book Y s i k t).stage) o) (book Y s i k) N (Precision.represent) (Precision.link_one) (padded_pay Y C hp s i k) ha (fun _=> (Work.F03.represent_smooth _).contDiffAt)
variable (v:fieldDir G n 1)(w:rule (Coarse G) n)
-- use all k ranks in an order, and extend j<<e with ZERO-padded LAYOUT
lemma precise (i j k:ℕ) : Radial.jet (fun t:ℝ×X=> t.1^(i+C'-k)*φ i k t.2) (j+C') (1,v)= if i  ≤  j then Radial.jet (φ i k) (j-i+k) v else 0:= by
  have h:= contact Y s o Z N hp ha i k
  by_cases hk : i ≤ p∧ Accept (g:=g) s i k
  · have hg:k  ≤  i+C':= hk.2; rw [Floe.favor_exp (φ i k) h.smooth]; split
    next he=>
      simp only [one_pow,one_mul]; split
      next he'=> congr 2; omega
      next he'=> exact h.jet_z _ (by omega)
    next he=> rw [if_neg (by omega)]
  rw [show φ i k = 0 from (show art Y s o Z N _ _=0 by unfold art; rw [below Y s o Z N hk]; rfl)]
  simp only [Pi.zero_apply,mul_zero]; change Radial.jet (fun _ : ℝ×X=>0) _ _ = _; split <;> simp [Radial.jet]
-- calculate `grasp0`. port root external
local notation "I" => ports G n
lemma book_identity (j:ℕ)(hj:j  ≤  p) : Anthem.grasp0 (T) o s j w=∑ i∈range (j+1),∑ k∈range (p+C'+1),Radial.jet (art Y s o (fun _=>True) N i k) (j-i+k) (ports G n w):= by
  let v : X:= ports G n w; let U: ℕ→Prop:= fun _=>True; let s' := Stanza.son Y N; let F (i k:ℕ) (x:ℝ×X):= x.1^(i+C'-k) * art Y s o U N i k x.2
  let W i := ∑ k∈range (p+C'+1),F i k
  have hn i k : ContDiffAt ℝ ω (F i k) 0:= (contDiffAt_fst.pow _).mul ((contact Y s o U N hp ha i k).smooth.comp («f»:=Prod.snd) (0:ℝ×X) contDiffAt_snd)
  change Radial.jet (fun x:ℝ×X=> (T).markℓ (Stack.selector (T) U) o s x.1 (Precision.represent x.2)) _ (1,v)=_
  rw [show (fun x:ℝ×X=> (T).markℓ (Stack.selector (T) U) o s x.1 (Precision.represent x.2)) = ∑ i∈range (p+1), W i from ?_] ; swap
  · ext ⟨t,z⟩; simp_rw [W,Finset.sum_apply]; exact enumerate Y s o U N _ _
  let G (i k:ℕ):= Radial.jet (art Y s o U N i k) (j-i+k) v; have hx i:Radial.jet (W i) (j+C') (1,v)=if i  ≤  j then ∑ k∈range (p+C'+1),G i k else 0:= by
    unfold W; rw [Floe.goth (fun k _=> hn i k)]; have he k: Radial.jet (F i k) (j+C') (1,v) = if i  ≤  j then G i k else 0:= precise Y s o U N hp ha v i j k
    simp_rw [he, Finset.sum_ite_irrel,sum_const_zero]
  rw [Floe.goth (fun i _=>?_ )]
  · change (∑ i∈range (p+1), Radial.jet (W i) (j+C') (1,v))=_
    simp_rw [hx]; rw [← Finset.sum_filter, show ((range (p+1)).filter (fun i=> i  ≤  j))=range (j+1) from (by ext; simp only [mem_filter,mem_range]; omega)]
  · rw [show W i=(fun x=>∑ k∈range (p+C'+1),F i k x) from funext (fun x=> Finset.sum_apply ..)]; exact ContDiffAt.sum fun k _=> hn i k

include hp ha
-- also clients can use for identities excluding some sectors in regression frames
lemma jet_retains (L:Ladder)(i j k:ℕ)(hi:i  ≤  p):
  Radial.jet (art (stencil L Y) s o Z N i k) j v = ∑ e∈range (i+1), L e k (i-e)*Radial.jet (art Y s o Z N e k) j v:= by
  let F e:= L e k (i-e) • art Y s o Z N e k
  have hn e : ContDiffAt ℝ ω (F e) 0:= (contact Y s o Z N hp ha e k).smooth.const_smul (L e k (i-e))
  rw [show art (stencil L Y) s o Z N i k=∑ e∈range (i+1),F e from (by funext x; simp_rw [Finset.sum_apply]; exact retention Y s L o Z (Precision.represent x) N i k hi hp ha), Floe.goth (fun e _=> hn e)]; refine Finset.sum_congr rfl fun e _ => ?_; let δ := L e k (i-e) • ContinuousLinearMap.id ℝ ℝ; exact (Assembly.jet_apply_left δ (art Y s o Z N e k) j ((contact Y s o Z N hp ha e k).smooth.of_le le_top) v).symm
end YM.Qlocal.Moonset
