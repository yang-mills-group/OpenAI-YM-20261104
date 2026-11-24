import YM.Integration.WilsonOlderFreshSoftCoverScalar
import YM.WilsonCoeffUV.Root.UV.RawSemi

/-! A scalar planting series follows every dated reversion on the same normalized N-quiet Wilson transfer. The covered reading follows from the actual finite receipts on every side. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketHistory
open Function Finset Filter Lattice Wilson RG Laurent Bloch Precision PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Blue
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Power WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Fountain WilsonCoeffUV.Soil
open Work.F08 AnalyticNext.QuarticMatch.Sheets MultiNext.SignedSource Tree
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped Classical BigOperators Topology

variable {G:Gauge}(A:Levels G)(O:ChartRatio G)(simple:G.Simple)(localO:LocalRatio O)

include simple localO in
theorem step (N i k:ℕ)(live:i<N)(P Q:Era G ℝ)(C:Cost)(paid:Auth k Q)
    (filed:∀n,P.1 n=affix C (Q.1 n))(n:Side):
    (verseI A O i N k P).1 n=affix (reel (ratioHigh A O N i) C) ((verseI A O i N k Q).1 n):=by
  let t:=ll A i
  let S:=stepAt t A.clock.kernel n
  let F:=xree t A.clock.kernel n
  let Y:=(story A O N (i+1)).1 (n*t.L)
  let inc:=Q.1 (n*t.L)
  let get:=fun (Z:Pal ℝ (Woods G (n*t.L)))=>reed S F (freeForms A N (i+1)) (roam A N i n) O Y k Z
  let coin:=ratioHigh A O N i
  have quiet:=(old A O simple localO N (i+1) live).basis (n*t.L)
  change Blue.mix coin (get (P.1 (n*t.L)))=affix (reel coin C) (Blue.mix coin (get inc))
  rw [filed]
  have lin:get (affix C inc)=affix C (get inc):=reedDear _ _ _ _ _ _ _ _ _ localO
    (A.blocks i 0).branches (age_sym A ..) (paid.span _) (paid.pale _) quiet.lamp quiet.shape
  rw [lin]
  exact mixedAff coin C _ (reed_band _ _ _ _ k quiet.lamp localO (paid.span _))
    (fun h=>reed_smooth _ _ _ _ k O _ (paid.pale _) h)

include simple localO in
theorem finite (N k b v:ℕ)(vb:v≤b)(bn:b≤N)(P Q:Era G ℝ)(C:Cost)(paid:Auth k Q)
    (filed:∀n,P.1 n=affix C (Q.1 n)):
    ∀n,(cruises A O N k b v P).1 n=
      affix (clock A O N b v C) ((cruises A O N k b v Q).1 n):=by
  induction vb using Nat.decreasingInduction with
  | self=>
    intro n
    rw [cruises_top,cruises_top,clock,dif_neg (lt_irrefl b)]
    exact filed n
  | of_succ i hi ih=>
    intro n
    rw [cruises_sub _ _ _ _ _ hi,cruises_sub _ _ _ _ _ hi,clock,dif_pos hi]
    exact step A O simple localO N i k (hi.trans_le bn) _ _ _ (cruising A simple localO hi bn paid) ih n

theorem cover {k:ℕ}(P Q:Era G ℝ)(C:Cost)(high:Auth k P)(low:Auth k Q)
    (filed:∀n,P.1 n=affix C (Q.1 n)):P.2=affix C Q.2:=by
  funext i r x
  have ships:Bends 0 (fun n=>affix C (Q.1 n) i r) (affix C Q.2 i r):=by
    simp_rw [affix,Finset.sum_apply]
    exact anzas (P:=fun (p:ℕ×ℕ) (n:Side)=>coeff p.1 C • (Q.1 n p.2 r)) _
      (fun p _=>(low.wing p.2 r).μ _)
  apply tendsto_nhds_unique ((high.wing i r).point x)
  exact (ships.point x).congr' (.of_forall fun n=>by
    change _=P.1 n i r (slideC n x)
    rw [filed n])

include simple localO in
theorem original (N k b v:ℕ)(vb:v≤b)(bn:b≤N)(P Q:Era G ℝ)(C:Cost)(p:Auth k P)(q:Auth k Q)
    (filed:∀n,P.1 n=affix C (Q.1 n)):
    (cruises A O N k b v P).2=affix (clock A O N b v C) ((cruises A O N k b v Q).2):=
  cover _ _ _ (cruising A simple localO vb bn p) (cruising A simple localO vb bn q)
    (finite A O simple localO N k b v vb bn P Q C q filed)

end YM.Integration.WilsonOlderFreshSoftSocketHistory
end
