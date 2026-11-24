import YM.WilsonCoeffUV.Marked.Paths.Posts
/-!
# Budget in deterministic passive marks & full ancestry
 For any output j≤order & given unmasked label family. Not absorbing field independent globally.
 -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Rolls
open Gauge Power PowerSeries Matrix Filter Lattice Laurent Exterior Precision Wilson RG Tree Bloch Stationary
open Function Blue Bank Fountain Soil Source Source.Drops Labels Cosmos Planned.PrimaryIntegral295 Place Carrier Bank.Carp Bank.Mosaic Bank.Mosaic.Near
open scoped Topology ContDiff BigOperators Classical
open Wheel Wheel.Mark Wheel.Express Embroider Address
open MeasureTheory
variable {G:Gauge}{n:Side}{k r i j l e m b:ℕ}{s v u A B:ℝ}
variable {V W I α β ι:Type}[NormedAddCommGroup V][NormedSpace ℝ V]{S J: Finset I}{c:I}{o:Cover}{D:I→ℕ}
variable [DecidableEq I]

-- concrete connector output mass x rooted family
abbrev Frill (S: Finset I)(o:I):= ↥(S.erase o)→ Cover
abbrev PoseH {S:Finset I} (P:(I→ Cover)→Era G V)(o:I)(q:Cover)(i:Frill S o):= P (toe S o q i)
def packetH (S:Finset I)(P:(I→ Cover) →Era G V)(k i:ℕ)(o:I)(q:Cover)(r:Frill S o): Robes G V k:= sphere (PoseH P o q r) k i o (toe S o q r)
lemma rolled_sum (p:Stigmata G b k e s u v)(q:(I→Cover) → Era G (Pen D S))(z:c ∈ S)(h:l ≤ k)(t:S.card≤ b)(x:i ≤ e)(g:0≤ A)(f:∀ i,Auth l (q i))(w:∀ i,∀ j< e, ∀ r,Wig Bank.terrain i s A S ((q i).2 j r)) (o:Cover) (j')(v':j'< i)(r:Fin (l+j'+1)):
    let P:= packetH S q l i c o
    let Z:= fun a: Frill S c=> P a j' r
    ∃ X : (u:Frill S c × RadP G r.val)→ Stationary.Ink G r.val→ Measure (Sky D), (∀ u, Barn (Z u.1 u.2) (X u)) ∧ SumBudget (fun y:Frill S c × RadP G r.val=> Real.exp (u*feeH (toe S c o y.1) c S) *lease (Z y.1 y.2) (X y) u) (glacier G l i*v*A*sprigs S c s):=by
   intro P Z; let F (i':Frill S c):= Real.exp (-s/4*realmSize S (toe S c o i')); let U:=v*A; have hU:0≤ U:=mul_nonneg (zero_le_one.trans p.tag) g
   choose M hm hz using fun y:Frill S c=>sparkle (P y) (toe S c o y) c (p.bursts I S (toe S c o y) c l (PoseH (S:=S) q c o y) A t z h (f _) g (w _) i x|>.2.1) (mul_nonneg hU (Real.exp_pos _).le) j' v' r
   let K:=glacier G l i*v*A; let L (x: Frill S c × RadP G r.val):=Real.exp (u*feeH (toe S c o x.1) c S)* lease (Z x.1 x.2) (M x.1 x.2) u
   have he i: SumBudget (fun j=>L (i,j)) (K * F i):=by unfold K F; rw [mul_assoc,mul_assoc]; convert! hz i using 1; ring
   have ha:0≤K:=by rw [show K=glacier G l i * U from mul_assoc ..]; exact mul_nonneg (gentle ..) hU
   have hh : SumBudget (fun i:Frill S c=> K * F i) (K * sprigs S c s):= cap_scale (sprigsPay z o p.original) ha
   have hL j:0≤L j:= (he j.1).1 j.2
   have hb:Summable L:= (summable_prod_of_nonneg hL).mpr ⟨fun i=> (he i).2.1, Summable.of_nonneg_of_le (fun i=> tsum_nonneg fun j=>(he i).1 j) (fun i=>(he i).2.2) hh.2.1⟩
   refine ⟨fun x=> M x.1 x.2,fun j' => hm _ _,hL,hb,?_⟩; change tsum L ≤ _; rw [hb.tsum_prod]; exact (Summable.tsum_le_tsum (fun i=>(he i).2.2) hb.prod hh.2.1).trans hh.2.2
-- pre-root earning controls post-FJoint. ancestor halo belongs to L commitments.
omit [DecidableEq I] in
lemma posting (p:Stigmata G b k e s u v)(z:I→ Cover)(q: Era G V)(a:c ∈ S)(h:l≤ k)(x:S.card≤ b)(A:ℝ)(g:0≤A)(f:Auth l q)(w:∀ j< e,∀ r,Wig Bank.terrain z s A S (q.2 j r))[CompleteSpace V](y:i≤e) :
    let P:=sphere q l i c z
    Rains P i u (v*A*Real.exp (-s/2*realmSize S z)) ∧ tenure P S z c i u (v*A*Real.exp (-s/4*realmSize S z)) ∧ ∀ j< i,
    let t:= shifted (baton P i) (z c)
    Auth l t ∧ t.2 j=q.2 j ∧ ∀ n r,t.1 n j r = Carp.plume (q.2 j r) n :=by
    intro R; obtain ⟨r,v,t⟩:= p.bursts _ _ _ _ l q A x a h f g w _ y
    exact ⟨r,v, fun j h' => ⟨(root_robe R r p.affordable _).1, shineZ q z r p.affordable t j h'⟩⟩
end YM.WilsonCoeffUV.Mer.Rolls
