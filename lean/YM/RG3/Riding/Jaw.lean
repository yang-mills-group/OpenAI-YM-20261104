import YM.RG3.Riding.Picket
import YM.RG3.Script.Picnic.Cadre

/-!
# Escrow actual box canvas to temporary P, before mask editing

Keeps ALL alternatives & Thumb stakes even for Ω lists. Canopy buyer
at ANY proved exponent S creates one Ω input of this form with Marked
receipts. Supports/ranking lenses in D itself (“unmasked common ν
underneath measured slices”) require verification by analytic workers;
Canopy.Burns proves only part. `select` doesn't require torsion on Ω,
but return a common t spokes function for applying manually. Preserves
same kernel/environment and κ, any stage B≥P.p supplied by Towed. Use
 B=P.p code for terminal Glaze oneShot.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Riding
open RG Wilson Lattice Function Marker Overlay RG3.Script RG3.Held
 RG3.Forms RG3.Ink Extra.Trajectories Extra.Iteration Extra.Multi Ac Push.Local Press
 Push.AbsoluteSums Push.Corrected MergeProof Accent Finset Script.Picnic Script.Reserve
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {n : Side}{V:Type*}[DecidableEq V]{R:Census V}{G:Gauge}
  (P : Rep G n)(ζ:V→Site n){w:V→ℝ}(hw:∀v,0<w v)
variable {S e t τ B :ℝ}
variable {Ω:Type*}[Nonempty Ω] (f : Ω→ Box n→ Config G n→Poly R)
  (hF:∀ x i, Flow ζ i (f x i) P.p.threshold)
  (f0: Box n→R.Mode→ℝ)

def unitPrice (R:Census V)(w:V→ℝ)(c:R.Mode→ℝ):ℝ:=∑ i:R.Mode,Poly.toll w i*c i

variable (hh:P.activities.Valid P.p e t)
  (he : ∀ x i U,(f x i U).part R.quiet=bass P i U)
structure Review (S τ:ℝ) : Prop where
  pos i j: 0≤ f0 i j
  cost x i U j : ‖(f x i U).part j‖ ≤ f0 i j
  hits: Hit Prod.fst P.p.B (fun j=> unitPrice R w (f0 j)) S τ
-- w explicit?
def grade (i:mortar n):Poly R:=Poly.inject (fun j=> (f0 i.val j:ℂ))

include hF hw hh he
variable (hs: Review P (w:=w) f f0 S τ)
include hs
omit [Nonempty Ω] hw hF he hh in
lemma assure x i U:Width.Covered ((pick P ζ (f x)).flow i U) (grade f0 i):= fun j=> ⟨hs.cost x i.val U j,rfl⟩
omit [Nonempty Ω] hw hF hh he in
 set_option pp.deepTerms true in
lemma graded : Hit (fun i:mortar n=>i.val.1) P.p.B (fun i=>Poly.price w (grade f0 i)) S τ := by
  intro x
  have ht:= Script.Edition.minor_subtype {i| Sure i} (hs.hits x)
  change SumBudget (fun i:mortar n=>if x ∈ i.val.1 then unitPrice R w (f0 i.val)*_ else _) τ at ht
  convert ht using 1; ext1 i; split; congr 1; unfold Poly.price unitPrice; exact sum_congr rfl (fun j _=> congrArg _ ((Complex.norm_real _).trans (Real.norm_of_nonneg (hs.pos i.val j))))
  rfl
omit hF hh in
lemma housed (δ:ℝ)(hv:δ ≤ S):
    let a:=fun j:mortar n=> f0 j.val R.quiet
    Slate P δ τ a:= by
  intro a
  refine ⟨fun i=>hs.pos ..,fun i U=> (he (Classical.arbitrary Ω) i.val U) ▸ hs.cost (Classical.arbitrary Ω) ..,fun x=>budget_mono (graded P f f0 hs x) (fun i=>?_ ) (fun (i:mortar n)=>?_ )⟩ -- .. ambiguity
  · split; exact mul_nonneg (hs.pos ..) (Real.exp_pos _).le;rfl
  split
  · have hi : a i ≤ Poly.price w (grade f0 i):=by -- underscores
      have hx j:= Poly.member hw R.quiet (grade f0 j)
      specialize hx i; rw [Poly.quiet_toll,one_mul] at hx
      change ‖(f0 i.val R.quiet:ℂ)‖ ≤ _ at hx
      rwa [Complex.norm_real, Real.norm_of_nonneg (hs.pos _ _)] at hx
    exact mul_le_mul hi (Real.exp_monotone (mul_le_mul_of_nonneg_right hv (by positivity))) (Real.exp_pos _).le ((hs.pos ..).trans hi)
  rfl

variable [Nonempty V]
-- cannot rewrite P from Sale if P.activities not satisfying stronger reserve individually;
-- base log bookstore b locally on *P* before, preserved on virtual exactly.

def escrow (b:Taste Ω ζ P R):Taste Ω ζ (virtual R G P ζ) R where
  menu := {
    origins:= b.menu.origins
    branch:= b.menu.branch
    regular:= b.menu.regular
    global:= b.menu.global
    rays:= b.menu.rays
    marks _:= unpin (fun j: Article.Key (mortar n) R=>j.2.val) (R.fire (Classical.arbitrary V))
    force x i:=unpin ((pick P ζ (f x)).scored pin i) 0 }
  root := b.root
  tag:= b.tag
  site:= b.site
  score:= b.score

variable (b:Taste Ω ζ P R)
-- clone held view log before imprint
private def turn : View Ω V G n (virtual R G P ζ) R:= ⟨b.menu.origins,b.menu.rays,b.menu.branch,b.menu.marks,b.menu.global,b.menu.regular,b.menu.force⟩
omit [Nonempty Ω] hF hh he hs hw in
lemma postage (x:Ω) : (escrow P ζ f b).menu.terms x=(pick P ζ (f x)).impression ((turn P ζ b).terms x) pin:=rfl
-- lint includes

variable (hA:S ≥ P.p.supportExponent)
  {q k r δ yK:ℝ}(h:b.Store w q k yK) (ht:τ≤r*δ)(hd:0<δ)
include h ht hd hA
set_option maxHeartbeats 200000 in
theorem payClerk [Fintype V]: let Z:=escrow P ζ f b
    let _new:=virtual R G P ζ
    Nonempty (Z.Snacks w q k r δ yK) ∧
    (∀ x U,(Z.leaf x).density U=play P R (f x) ((b.leaf x).log) U) ∧
    ∃ a:ℕ×ℕ→ℝ,Coffer Z w S τ a:=by -- Coffer exponent S, .where unaffected
  intro Z Q
  have hi x:= conditioned P (f x) (hF x) (he x) hh
  let Y:=turn P ζ b
  let W i:=pick P ζ (f i)
  let pay:=grade f0
  have hsP:Hit (fun i:mortar n=>i.val.1) P.p.B (fun i=>Poly.price w (pay i)) S τ:=graded P f f0 hs
  have h' : Hit (fun i:mortar n=>i.val.1) P.p.B (fun i=>Poly.price w (pay i)) P.p.supportExponent τ := Script.Reserve.hit_down hsP (fun i=>Poly.nonnegative hw _) hA
  have hH (x:Ω) : Hit (fun i:mortar n=> (Q.activities.forced (pin i)).support) Q.p.B (fun i=> Poly.price w (pay i)) P.p.supportExponent τ:= by
    have h i:= (pick_host (f:=f x) P (ζ:=ζ)).equal_span i
    have hX : (fun i:mortar n=>(Q.activities.forced (pin i)).support)=(fun i=>i.val.1):=funext fun i=>(h i).symm
    rw [hX]; exact h'
  let i₀:=Classical.arbitrary Ω
  obtain ⟨HA⟩:= Y.issued W pin b.root hi (fun i=>pick_host ..) pay w (fun i x=>assure P ζ f f0 hs x i) (hH i₀) ht hd hw (fun x=>⟨(h.fit x).rays,(h.fit x).home,(h.fit x).regular⟩) h.white h.globe (fun i=>⟨(h.present i).1,fun x s he=>b.root.symm ▸ ((h.present i).2 x s he)⟩) h.warrant
  have hS:Nonempty (Z.Snacks w q k r δ yK):= ⟨HA,h.sound,h.gold,h.given,h.ticket⟩
  have hT x:(W x).Budget w τ:= ⟨pay,fun i=>assure P ζ f f0 hs x _,h'⟩
  refine ⟨hS,fun x U=> ?_,?_⟩
  · -- expand just the density not path expression
    have hh' : (Z.leaf x).density U= play P R (f x) ((b.leaf x).log) U:= by
      unfold Deck.density; change ((Real.exp (Q.exponent U):ℝ):ℂ) • (Poly.pass ((b.leaf x).log U)* ((Z.menu.terms x).cluster U))=play P R (f x) ((b.leaf x).log) U
      unfold Z; rw [postage (f:=f),Article.same_cluster (p:=P.p) _ _ _ hw (pick_host P _) (hT x) (cooking P _ (he x) hh),clustering (f:=f x) P (hF x)]
      rfl
    exact hh'
  let m:= Article.voucher (R:=R) pin ζ (fun i:mortar n=> i.val.1) pay
  let X(j:ℕ×ℕ):=(Q.activities.forced j.1).support
  let l(j:ℕ×ℕ):=Z.menu.marks j.1 j.2
  have hv x : (∀ i j,0 ≤ m (i,j) ∧ ∀ U, ‖((Z.menu.terms x).entries i j U)‖ ≤ m (i,j)∧ (0 < m (i,j) →∀ v∈ (l (i,j)).val,ζ v∈X (i,j))) ∧
    Hit X Q.p.B (fun i=>Poly.toll w (l i)*m i) S τ ∧ ∀ v,SumBudget (Script.per Q.p.B S w l X m v) τ:=
    Script.Reserve.supplier (W x) (Y.terms x) pin (pick_host P _) (hi x) hw (fun i=>assure P ζ f f0 hs x _) hA hsP
  refine ⟨m,fun i=>((hv i₀).1 i.1 i.2).1,fun i j x U=> (((hv x).1 i j).2 U).1,(hv i₀).2.1,(hv i₀).2.2,fun i he=>?_⟩
  rw [Z.root]; exact (((hv i₀).1 i.1 i.2).2 1).2 he
end YM.RG3.Riding
