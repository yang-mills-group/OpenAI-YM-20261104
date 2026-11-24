import YM.Qlocal.Parabola.Center
/-!
# Single-mode paper ledger. Preparing the reconciliation via `Parabola` on ALL markers simultaneously

The marker algebra will later be specialized with chosen charges/erasures/new period orientation.
First carry all log rows assigned to complete itinerary tags. Those rows may
 carry genuine (exponent) signs; `total` means read everywhere (an external caption reported with its tag).
Never require summability at infinite orders, but true countably many rows at each step.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Reckoner
open Function RG Lattice Wilson Pert.Attach MeasureTheory Filter Progress.DirectedRecipe Finset
open Marker RG03.Gather Push.AbsoluteSums
open scoped Topology ContDiff BigOperators Classical
open Publishing Parabola Integration.RiderTastePresentation Integration.LocalComparison
variable {V Ω J J' J₀:Type}[DecidableEq V]{G:Gauge}{n:Side}{R:Census V}
variable {X: RG.Rep G n}{o:V→Site n}{s:V→ Support n}{q:Ray R}{A B t:ℝ}
-- Paper.Ex.Body MUST know same markers pre measured, one row per Tag; no counter accounting aggregate. Ink quiet requires true zero even off germ (script).
structure Scribe (Ω J:Type)(G:Gauge)(n:Lattice.Side)(R:Census V) where
  tag : J → R.Mode
  region : J → Support n
  total : J → Prop
  score : Ω→ J→ Config G n→ℂ

namespace Scribe
variable (S:Scribe Ω J G n R) (Q:BudgetPoint) (K:Ω→Policy G R n)
noncomputable def render (x:Ω)(j:J) (v:Config G n):ℂ:= if S.total j then S.score x j v else masked Q.threshold (S.region j) (S.score x j) v
noncomputable def enters (x:Ω)(v:Config G n)(j:J):Poly R:= Poly.send (S.tag j) (S.render Q x j v)
noncomputable def send (x:Ω)(v:Config G n):Poly R:= ∑' j,S.enters Q x v j
structure Proper (s:V→Support n) : Prop where
 length j : (S.region j).Nonempty
 sight x j : Q.Regular (S.region j) (S.score x j)
 owns i v x U : S.score x i U ≠0→ v∈(S.tag i).val → s v⊆S.region i
 quiet i : S.tag i=R.quiet →∀ x,S.score x i=0
 total i x U : S.total i → S.score x i U=S.score x i 1

open PhysicalNext.Repeat Merge
-- variant witness for sup inside cost.
structure Earned (f:J→ℝ) : Prop where
 nonneg i : 0 ≤ f i
 bound x i j (hj:j∈S.region i): Q.supBounds j (S.region i) (S.score x i) (f i)

def Spend (q:Ray R)(t A:ℝ) : Prop:= ∃ f:J→ℝ,Earned S Q f ∧ Ac.Hit S.region Q.B (fun i=> q (S.tag i) * f i) t A

noncomputable def printP : Ledger Ω J G n R where
 region := S.region
 total := S.total
 raw := fun x i v=> Poly.send (S.tag i) (S.score x i v)
 forced:= K
@[simp] lemma painted {X: RG.Rep G n}(x:Ω)(i:J)(v:Config G n): Ledger.painted (S.printP K) X x v i=S.enters X.p x v i:= by
 unfold Ledger.painted enters render printP; dsimp only; split; rfl
 next hx=> by_cases ht: Healthy X.p.threshold (S.region i) v; rw [masked_eq _ _ _ _ ht, masked_eq _ _ _ _ ht]; rw [masked_ne _ _ _ _ ht, masked_ne _ _ _ _ ht,Poly.send_zero]
@[simp] lemma marked {X: RG.Rep G n}(x:Ω)(U:Config G n): markRead (r:=X) (S.printP K) x U=S.send X.p x U := tsum_congr (fun i=> S.painted K (X:=X) x i U)

variable (h:Proper S X.p s) (p:Rental q)

variable {K}
include h
lemma authentic (hs:∀ i,o i∈s i)(hK:∀ x,Authority X.p X.activities s (K x)): Ethics X o s (S.printP K):=by
 refine ⟨hs,h.length, ?_, ?_,fun x i j U hp v hv=>?_,fun x i j=>?_,fun x i U j ht=>?_,fun x=>?_ ⟩  -- edit
 · intro x i U hi; change Poly.send _ _=Poly.send _ _; rw [h.total i x U hi]
 · intro x i U; unfold printP; dsimp only; rw [Poly.part_send]; split; next he=> rw [h.quiet i he.symm x,Pi.zero_apply]
   next=>rfl
 · change (Poly.send _ _).part _≠0 at hp; rw [Poly.part_send] at hp; split at hp; next ht=> exact h.owns i v x U hp (ht ▸ hv)
   next=>simp at hp
 · let f:ℕ→ Config G n→Poly R:=K x; have ht:=(hK x).align i; exact ⟨fun U V h h₁=>congr_arg (Poly.part · j) (ht.travel U V h h₁),ht.visible j,fun g V=>congr_arg (Poly.part · j) (ht.worth g V),fun U hv=> (hK x).beacon i U (fun he=>hv (by unfold printP; dsimp only; rw [he]; rfl))⟩
 · exact (hK x|>.align i|>.owns U) j ht
 exact (hK x).quiet

open PhysicalNext.Repeat
include p
lemma bulk (hS:S.Spend X.p q t A) {b:ℕ→Ray R} (hB:Haze (fun i=>(X.activities.forced i).support) X.p.B t b q B) (hm:∀ i x U,CoverP (b i) (K x i U)) (hK:∀ x,Authority X.p X.activities s (K x)): Bulk X s (S.printP K) q t A B:= by
 constructor
 · obtain ⟨g,hg,hG⟩:= hS; let f(i:J)(x:R.Mode):= if x=S.tag i then g i else 0; have hf i x: 0≤f i x:= by unfold f; split; exact hg.nonneg _; rfl
   let y (i:J)(x:Ω)(v:R.Mode)(U:Config G n):= ((S.printP K).raw x i U).part v; have hi i(i':V) x v U: y i x v U=if v=S.tag i then S.score x i U else 0:= Poly.part_send .. -- nonempty type?! i' unused
   refine ⟨fun i=>f i.1 i.2,fun i=> hf ..,fun i j x=>?_, ?_⟩
   · intro F'; have hw: F'=fun v:Config G n=> if j=S.tag i then S.score x i v else 0:= funext fun v=> Poly.part_send ..
     by_cases hy:j=S.tag i
     · rw [hw]; simp only [hy,if_true,f]; exact ⟨h.sight x i,fun j hj=>hg.bound x i j hj⟩
     rw [hw]; simp only [if_neg hy,f]; exact ⟨(Extra.Histories.regular0 X.p (S.region i) 0).1,fun j _=> (Extra.Histories.regular0 ..).2⟩
   convert! hG using 1; ext i; unfold Tons f; simp
 obtain ⟨u,hU,hu,hv,h'⟩:= trimP p hB (g:=K) (fun x i U=>(hK x|>.align i).owns _) hm; exact ⟨u,hU,hu,fun x i=>hv i x,h'⟩
 -- issue using p argument? not included. include p
variable {Q} {S} -- infer
omit h p
lemma Earned.visible {f:J→ℝ}{S:Scribe Ω J G n R}(hp:Proper S Q s)(hf:Earned S Q f)(x i U): ‖S.render Q x i U‖ ≤ f i := by
 let g:=S.score x i; obtain ⟨j,hj⟩:=hp.length i
 have ht U (hU : Healthy Q.threshold (S.region i) U):‖S.score x i U‖ ≤ f i:= (hf.bound x i j hj).2 U hU [] (Nat.zero_le _) (by simp)
 unfold render; split
 next a=> rw [hp.total i x U a]; exact ht 1 (by unfold Healthy; rw [UVNext.CouplingReset.flags_one]; simp)
 next a=> by_cases hU : Healthy Q.threshold (S.region i) U; rw [masked_eq _ _ _ _ hU]; exact ht _ hU; rw [masked_ne _ _ _ _ hU,norm_zero]; exact hf.nonneg _
lemma delivered (hp:Proper S Q s)(x:Ω)(i:J): Payload.Thin Q (S.region i) (S.render Q x i):= by
 by_cases he: S.total i
 · have h:S.render Q x i=fun _=> S.score x i 1:= funext fun U=> by rw [render, if_pos he, hp.total i x U he]
   rw [h]; exact ⟨measurable_const,fun _ _=>rfl,fun _ _ _ _=>rfl⟩
 rw [show S.render Q x i = masked Q.threshold (S.region i) (S.score x i) from (funext fun j=> if_neg he)]; let ht:= hp.sight x i; refine ⟨masked_measurable _ _ _ ht.borel,fun T V=>?_,fun U V hu hv=>?_⟩
 · by_cases h:Healthy Q.threshold (S.region i) V; rw [masked_eq _ _ _ _ h, masked_eq _ _ _ _ (show Healthy _ _ (Lattice.gauge T V) from (by unfold Healthy; rw [gauge_flags]; exact h))]; exact ht.symmetry T V
   rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ (show ¬Healthy _ _ (Lattice.gauge T V) from (by unfold Healthy; rw [gauge_flags]; exact h))]
 have h : Healthy Q.threshold (S.region i) U ↔ Healthy Q.threshold (S.region i) V:=by unfold Healthy; rw [Finset.disjoint_iff_inter_eq_empty,Finset.disjoint_iff_inter_eq_empty,hv]
 by_cases hz:Healthy Q.threshold (S.region i) U; rw [masked_eq _ _ _ _ hz,masked_eq _ _ _ _ (h.1 hz)]; exact ht.sites _ _ hu
 rw [masked_ne _ _ _ _ hz,masked_ne _ _ _ _ (mt h.2 hz)]
lemma Proper.holistic (hp:Proper S Q s)(x:Ω)(i:J)(U:Config G n)(he:S.render Q x i U≠0)(v:V)(hu:v∈(S.tag i).val): s v⊆ S.region i:=by
 unfold render at he; split at he; exact hp.owns i v x U he hu
 by_cases hz:Healthy Q.threshold (S.region i) U; rw [masked_eq _ _ _ _ hz] at he; exact hp.owns i v x U he hu
 exact (he (masked_ne _ _ _ _ hz)).elim
lemma Proper.looks (hp:Proper S Q s)(x:Ω)(i:J): Parabola.Articles (S.region i) (fun U=> S.enters Q x U i) s Q.threshold:= by
 let g:= S.render Q x i; have h:=delivered hp x i; refine ⟨fun U V h₀ h₁=> congr_arg (Poly.send (S.tag i)) (h.reads _ _ h₀ h₁), fun j=>?_,fun k U=>congr_arg (Poly.send (S.tag i)) (h.invariant k U),fun U j hj=>?_⟩
 · unfold enters; simp_rw [Poly.part_send]; split; exact h.measurable; exact measurable_const
 unfold enters at hj; rw [Poly.part_send] at hj; split at hj; next hv=> exact fun i hi=> hp.holistic x _ _ hj i (hv ▸ hi)
 next=> simp at hj
-- no quiet costs
lemma Proper.silent (hp:Proper S Q s)(x:Ω)(i:J)(v:Config G n): (S.enters Q x v i).part R.quiet=0:=by
 unfold enters render; rw [Poly.part_send]; split
 next h=>rw [hp.quiet i h.symm]; split; exact rfl; simp [masked]
 next=>rfl
lemma cost_read (h:S.Spend Q q t A) (p:Rental q) (hp:Proper S Q s)(ht:0≤t) (x:Ω)(v:Config G n):Summable (S.enters Q x v):= by
 obtain ⟨f,hf,hΩ⟩:=h; have hx:Summable f:= Payload.receives (L:=S.region) (V:=V) (p:=Q) hf.nonneg p.pos ht hp.length hΩ -- namespace? 
 exact (Payload.ghost (f:=fun i=> S.render Q x i v) (hx.of_norm_bounded (fun i=> hf.visible hp _ i _))).2
lemma calm_send (h:S.Spend Q q t A)(p:Rental q)(hp:Proper S Q s)(ht:0≤t)(x:Ω)(v:Config G n): (S.send Q x v).part R.quiet=0:= by unfold send; rw [Poly.share (cost_read h p hp ht x v)]; exact Eq.trans (tsum_congr (fun i=> hp.silent x i v)) tsum_zero
end Scribe
end YM.Qlocal.Reckoner
