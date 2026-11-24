import YM.LocalLTE.Concourse.Core
/-!
# Shell charges without units

Expenditure at centered reader. Does not hide sums of integrations in the unit port.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Concourse
open Function Filter Lattice Wilson RG Source Labels Extra.Histories Motion
open LocalLTE.Vinca LocalLTE.FrameBox AnalyticBridge VerifiedReset Collection Price PhysicalNext.Repeat Blush
open Push Local Planned.GuardedAtom LocalLTE.River YM.MergeProof
open Finset MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{H:History G}{N m p:ℕ}{F:Labels.Frame G 0}
local notation "O" => H.rep N p m
local notation "P'" => H.rep N p (m+1)
local notation "κ" => Real.sqrt (H.levels.clock.forcedAllowance m)
local notation "κ'" => Real.sqrt (H.levels.clock.forcedAllowance (m+1))
open LocalLTE.Drift Planned.GuardedAtom.Guard Lotus
variable (D:SectionData F)(A:Hol G)(W₀:Gateway F A (H.rep N p (m+1)) (H.S.side m p))
    (Z:Keeper (H.rep N p (m+1)).p (H.rep N p (m+1)).activities) (P : Coefficient F (H.S.side (m+1) p))
variable {t:ℝ} (U:Syllabus H N p m A (rack Z (memo F.e0 P)) t)
noncomputable abbrev ticketP: Coefficient F (H.S.side m p) := issue H N p m A W₀ (rack Z (memo F.e0 P)) U 0
local notation "I"=> ticketP A W₀ Z P U -- order
noncomputable abbrev honour := memo ((I).x-F.e0+P.x) I
local notation "M'"=> honour A W₀ Z P U
-- projection and TE ledger. true epoch contacts unclipped
variable (h:H.Selected)(hm:m<N)
    (hq:P.Format 0 A (H.rep N p (m+1)))(hX:P.remBound 0 (H.rep N p (m+1)) (Real.sqrt (H.levels.clock.forcedAllowance (m+1))) t)
    (X:Set Wing)(Q:GaugeDoor (H.rep N p (m+1)) (H.rep N p m))
    (hQ:SoundDoor (H.levels.clock.op m p) Q)
    {η C w:ℝ} (he:0≤η)
    (T:Heading F)(hw:LocalLTE.Vinca.Key D H N p m A Q W₀ C η w T X)
    (hv:0≤w)(hK:Real.sqrt (H.levels.clock.forcedAllowance (m+1))≤1)
    (hp:∀ i,X (.gasKey (cart Z i)))
set_option quotPrecheck false
local notation "Δ"=> F.e0
local notation "v"=> (F)
include h hm hq hX hQ hv hK hp he hw
lemma acclaim : (M').Format 0 A (H.rep N p m) ∧ (M').density 0 D (H.rep N p m)=(H.levels.clock.op m p).push ((P'|>.beta)) (P.density 0 D P') ∧ (M').remBound 0 (H.rep N p m) κ (η*t) ∧ F.coeffSize ((I).x-F.e0) ≤ η*t:=by
   let P₀:= memo F.e0 P; let Y:= I; let Q₀:=m
   have ht:= Vinca.centre D H N p m A Z P₀ X Q 0 h hm (memo_format F.e0 hq) (memo_cost F.e0 hX) (rfl) hQ he W₀ U hw hv hK hp
   have ht:= ht.cost; rw [show P₀.x=F.e0 from rfl,solo_lead,Concourse.removes,show Bid.vowel F (H.S.block m) 0=0 from funext (fun i=>by simp [Bid.vowel])] at ht
   simp_rw [show F.coeffSize 0=0 from (by simp [Frame.coeffSize]),mul_zero,zero_add] at ht
   refine ⟨memo_format _ ht.format,?_,memo_cost _ ht.bound, (le_mul_of_one_le_left (Work.G08.size_nonneg ..) (orbitCost_one_le F)).trans ht.leadP⟩
   let op:= H.levels.clock.op m p; let p1 := P.density 0 D P'; let α:= (P.x - F.e0) 0
   let o':= liftVac H N p (m+1); have hj : liftVac H N p m=op.push (P').beta o':=by have hz := blast_vac H N p m 0 h hm; simpa [blast] using hz.symm -- arguments m,d order
   let Q1:=P₀.density 0 D P'; have hx : p1=Q1+α • o':=by
      funext vi; exact (memo_density P.x P₀ D _ (H.rep N p (m+1)) vi)
   have hz:= ht.agrees; change Y.density 0 D O=blast H N p m 0 Q1 at hz; simp only [blast,pow_zero,one_smul] at hz
   have hs:= play_integrable H N h hm (memo_format F.e0 hq) (memo_cost F.e0 hX) (B:=D)
   have heI:MeasureTheory.Integrable o' (prior G (H.S.side (m+1) p)):=by
       exact vac_integrable H N p (m+1) h hm
   funext u
   rw [show (M').density 0 D (H.rep N p m) u=_ from memo_density (Y.x-F.e0+P.x) Y D (0:Site _) O u, hz]
   change _+(_*(_):ℂ)= op.push _ p1 u
   rw [hx, StepData.push_add (H.levels.transition_mass m p _) _ _ hs (heI.smul α), StepData.push_smul _ _ _ _ heI]
   rw [show _-F.e0+P.x - Y.x = P.x-F.e0 from (by abel), ← hj]; change _+α*_=_; rfl
end YM.LocalLTE.Concourse
