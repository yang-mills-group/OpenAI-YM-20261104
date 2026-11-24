import YM.LocalLTE.XPre.Paces
import YM.LocalLTE.XPre.Gallery
/-!
# Each input ticket.E.Data -> compressed life authority. Keep uncompressed stamp too.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.XPre
open Function Finset Filter Set MeasureTheory Lattice Wilson RG
open Extra.Histories Push Local Motion Extra.Multi
open LocalLTE.Fan LocalLTE.River LocalLTE.Vinca Ticket
open PhysicalNext.Repeat Lotus Blush Progress.DirectedRecipe
open YM.MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {ι: Type}{G:Gauge}{c f:Side}{S:StepData c f} {R : Rep G f} {C: Rep G c}
    {κ κ' K ν t u q r s b:ℝ} {A:Activities G f} {d t₀ p m l:ℕ} {o:Site f}{o':Site c}
open AbsoluteSums Animals Next.Foundations Source Planned.GuardedAtom
variable {v w:ℂ}{X Y:Wing→Prop}{M:ι→ Leaf R}{g:ι→ℂ}{φ:MergeProof.Response G c}{L:GaugeDoor R C}
variable {E:Config G f→ℂ} {Z: Res G f}{W : Res G c}
set_option quotPrecheck false
local notation "B'"=> localSection G d
local notation "F"=> ((Labels.frames G).level d)
local notation "φB"=> hol G
open Extra.Histories.InputColumn
variable {H:History G} {N n:ℕ} {L:GaugeDoor (H.rep N n (m+1)) (H.rep N n m)}
local notation "s'"=> H.S.side m n
local notation "s"=> H.S.side (m+1) n
local notation "R1"=> H.rep N n (m+1)
local notation "R0"=> H.rep N n m
variable (d) (K: Guard.Keeper ((H.rep N n (m+1)).p) ((H.rep N n (m+1)).activities)) (U: Vinca.Gateway ((Labels.frames G).level d) (hol G) (H.rep N n (m+1)) (H.S.side m n)) (A: Prices)
variable (P:Coefficient ((Labels.frames G).level d) (H.S.side (m+1) n))
local notation "X!'"=> Source.Coefficient F s
local notation "iY"=> (fun i: (F).Index=> Extra.Histories.primary (0:Site s) (Size.axis F i))
local notation "κZ"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
local notation "κI"=> Real.sqrt (H.levels.clock.forcedAllowance m)
local notation "HX"=> H.S.block m
local notation "v"=> (((HX|>.val):ℂ)^d)
variable (T:Syllabus H N n m (hol G) (rack K P) t) (X' : Coefficient ((Labels.frames G).level d) (H.S.side (m+1) n))
-- needles. D ensure Nonempty.Use with ANY booked Permit. Vinca Key lemma
variable {B: Heading ((Labels.frames G).level d)} {π c' d' w:ℝ}(hD: Vinca.Key (localSection G d) H N n m (hol G) L U c' π w B X)
include hD
variable (i:( (Labels.frames G).level d).Index)(hx:P.x=Size.axis ((Labels.frames G).level d) i)(ha: ∀ i,Y (.gasKey (cart (R:=H.rep N n (m+1)) K i)))(ht:∀ i,X (.gasKey (cart (R:=H.rep N n (m+1)) K i)))(hq:0≤π)
-- old.sens need `Seats`. does not imply revisions but for ∑. discard he.C post.
local notation "Q"=> rack K P
local notation "PF"=> Vinca.coins H N n m φB U Q T i
set_option linter.unusedVariables true
include ht hq
variable (h:H.Selected)(hm:m<N)
local notation "YX"=> issue H N n m φB U (rack K P) T i
-- output cont. supply with budget uL True & arbitrary Q.In.Yτ
variable (A':Inlet («H»:=H) (N:=N) (p:=n) (m:=m) (localSection G d) (hol G) κ p l X' ν)
variable (hg:(rack K P).support=X'.support)
variable (hf:∃ q:ℕ→ℝ, SumBudget (fun i=> ((H.rep N n (m+1)).p).mass ((rack K P).support i) (q i)) r ∧ ∀ i, (H.rep N n (m+1)).p.supBounds 0 ((rack K P).support i) (((rack K P).regular-X'.regular) i) (q i)) (hK : Local.ForceCost ((H.rep N n (m+1)).p) ((H.rep N n (m+1)).activities) ((rack K P).forced) (Real.sqrt (H.levels.clock.forcedAllowance (m+1))*(r+r)))
variable (hr:P.remBound 0 (H.rep N n (m+1)) (Real.sqrt (H.levels.clock.forcedAllowance (m+1))) t)
include hf hK hD hq ht hr hx hg ha A'
-- earned per existence.V.
local notation "pZ"=> κZ*(r+r)
local notation "fee"=> A.beam+2*(ν+r+pZ)
local notation "gn"=> A.grant + A.canopy*(b+pZ)
local notation "zeroq"=> 2*(r+pZ)
set_option quotPrecheck false
set_option maxHeartbeats 900000 in
lemma sanctioned (hP : Permits R1 R0 Y L d v U A κ p l)(hb: SumBudget (fun i=> (R1|>.p).mass ((rack K P).support i) (T.a i)) b) (hV:SoundDoor (H.levels.clock.op m n) L) : Circuit Y L d κ p l 0 0 v (P.exponentialEntry 0 (localSection G d) (R1)) (profile (R1).activities P.forced) (profile (R0).activities (YX).forced) ((Size.axis F i) 0) fee gn zeroq := by
   obtain ⟨mH,hmH,hH⟩:= XPre.recognized d K U P T hD i ht hq -- order?
   let I':= InputColumn.Listing; let Off i:= (R1).p.mass ((Q).support i); let F':=(R0); let E':=(R1)
   let zh:= Size.axis F i; let J:= Extra.Histories.primary (0:Site s) zh; have hx':P.x=zh :=hx
   obtain ⟨b',hq1,h'⟩:=hf; obtain ⟨a,hT,hq'⟩:=hK
   let e(i):= Off i (T.a i); let error(i):= Off i (b' i); let flag(i):=(R1).p.mass ((R1).activities.forced i).support (a i)
   let model(i):=(R1).p.mass (X'.support i) (A'.prices i)
   let t':Listing→ℝ:=consist A.beam (fun i=>2*(model i+error i)) (fun i=>2*flag i)
   let u':Listing→ℝ:=consist A.grant (fun i=> A.canopy*e i) (fun i=> A.canopy*flag i)
   let tau:Listing→ℝ:=consist 0 (fun i=> 2*error i) (fun i=>2*flag i)
   let F0 : Listing→ Config G s →ℂ := consist (J.exponentialEntry 0 (localSection G d) (R1)) (fun i=> masked (R1).p.threshold ((Q).support i) ((Q).regular i)) (fun _=>0)
   let Q1:Listing→ Res G s:= consist 0 (fun _=>0) (fun i=> exactGas (R1).activities i ((Q).forced i))
   let P1 :Listing→ℂ:= consist (zh 0) 0 0
   have hs(i'): Circuit Y L d κ p l (0:Site s) 0 v (F0 i') (Q1 i') (profile (R0).activities (PF i'|>.forced)) (P1 i') (t' i') (u' i') (tau i'):=by
     rcases i' with j|j|j
     · unfold Vinca.coins consist; simp only [Sum.elim_inl]; by_cases hi:i=0; swap
       · rw [if_neg hi]; change Circuit _ _ _ _ _ _ _ _ _ _ _ _ ((Size.axis F i) 0) _ _ _; rw [show Size.axis F i 0 =0 from Pi.single_eq_of_ne (Ne.symm hi) _]; exact hP.reserves i hi
       rw [if_pos hi]; have hp: F0 (.inl j) = (fun _=>1) := by
          subst i; funext V; have hJ t:J.maskedTerm (R1) t V=0:= congr_fun (map_zero (Local.maskLinear _ _)) V
          change (F).e0 0+maskLinear _ _ (presented B' 0 _ ((F).core (F).e0)) V + ∑' i,J.maskedTerm E' i V=1; rw [Size.unit_core]; simp only [map_zero,Pi.zero_apply,add_zero,Labels.Frame.e0,Pi.single_eq_same]; simp_rw [show ∀ i,J.maskedTerm E' i V=0 from hJ]; simp only [tsum_zero,add_zero]
       have hu: P1 (.inl j)=1:= by unfold P1; rw [show zh= (F).e0 from (by unfold zh; rw [hi]; rfl)];change (F).e0 0=1; simp [Labels.Frame.e0]
       rw [hp,hu]; simp_rw [show profile (R0).activities (Vinca.unitP F H n m).forced=0 from (by funext i V; simp [profile,Vinca.unitP,Extra.Histories.primary,cram])]; exact zero_can A.future le_rfl A.pole _
     · let f:= (Q).regular j; let g:=X'.regular j; let X:=X'.support j; let Z:=(Q).support j
       have hg: X=Z:=congr_fun hg.symm j
       have hp:RegFit (R1) 0 d φB X g:= ⟨A'.format.smooth _,A'.format.origin j,A'.format.identity_null j,A'.format.projects j⟩
       change Circuit _ L d κ p l _ _ _ _ _ _ _ (2*((E').p.mass X _+_)) _ _; let q:= T.a j; let u:=A'.prices j
       rw [hg]; exact hP.regular f g Z _ _ _ ⟨T.outfit.smooth _, T.outfit.origin j,T.outfit.identity_null j,T.outfit.projects j⟩ (hg ▸ hp) (T.fields j) (hg ▸ A'.truth j) (h' j)
     by_cases hi:(Q|>.forced j)=0
     · unfold Vinca.coins consist; simp only [Sum.elim_inr]; rw [if_pos hi,show Q1 (.inr (.inr j))=0 from (by change exactGas _ _ _=0; rw [hi]; simp [exactGas]),show profile (R0).activities (Extra.Histories.primary (0:Site s') (0:(F).Coeff)|>.forced)=0 from (by funext i V; simp [profile,Extra.Histories.primary,cram])]; exact zero_can (mul_nonneg zero_le_two (hT.1 _)) (mul_nonneg zero_le_two (hT.1 _)) (mul_nonneg A.crown (hT.1 _)) 0
     have heY:Y (.gasKey j):=by
          have h : j∈Set.range (cart K):= not_not.mp (fun h=> hi (pit K P h)); obtain ⟨p,rfl⟩:=h; exact ha _
     unfold Vinca.coins consist; simp only [Sum.elim_inr]; rw [if_neg hi]; exact hP.forced _ _ _ _ hi heY ⟨T.outfit.invariant _,T.outfit.borel _,T.outfit.supported _,T.outfit.carried _,T.outfit.forcing _⟩ (T.force _|>.2) (hq' _|>.2)
   -- revenues
   have hS : SumBudget t' fee ∧ SumBudget u' gn ∧ SumBudget tau zeroq:=by
      have h0(j): 0≤ t' j ∧ 0 ≤ u' j∧ 0≤ tau j:=by obtain ⟨I,hI,M,g,f,b,hL,hY⟩:=(hs j).lamps; exact ⟨sumBudget_credit hL.purchase,sumBudget_credit hL.cost.toll.choose_spec.1,sumBudget_credit hY.1⟩
      have ht0 : HasSum t' (A.beam +(2*((∑' i,model i)+∑' i,error i)+2*∑' i,flag i)):= added (((A'.vow.2.1.hasSum).add hq1.2.1.hasSum).mul_left _) (hT.2.1.hasSum.mul_left _)
      have hU: HasSum u' (A.grant+(A.canopy*(∑' i,e i)+ A.canopy*∑' i,flag i)):= added (hb.2.1.hasSum.mul_left _) (hT.2.1.hasSum.mul_left _); have hh: HasSum tau (0+(2* (∑' i,error i)+2*∑' i,flag i)):= added (hq1.2.1.hasSum.mul_left _) (hT.2.1.hasSum.mul_left _)
      refine ⟨⟨fun i=> h0 i|>.1,ht0.summable,?_⟩,⟨fun i=> (h0 i).2.1,hU.summable,?_⟩,fun i=>(h0 i).2.2,hh.summable,?_⟩
      · rw [ht0.tsum_eq,←mul_add]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add (add_le_add A'.vow.2.2 hq1.2.2) hT.2.2) zero_le_two)
      · rw [hU.tsum_eq,←mul_add]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add hb.2.2 hT.2.2) A.crown)
      rw [hh.tsum_eq,←mul_add,zero_add]; exact mul_le_mul_of_nonneg_left (add_le_add hq1.2.2 hT.2.2) zero_le_two
   have hu : (Q).remBound 0 (R1) κZ t:= keeps K P hr
   refine bandR hV hs ?_ ?_ (fun i V=> profile_merge (code _) (PF) (Real.sqrt_pos.mpr (forcedPos ..)) (fun i=> (hmH i).2) hH i V ) ?_ hS.1 hS.2.1 hS.2.2
   · intro U; have hJ j:J.maskedTerm E' j U=0:= congr_fun (map_zero (Push.Local.maskLinear _ _)) U
     have Hx(i:Coefficient (F) (H.S.side (m+1) n)):i.exponentialEntry 0 B' E' U= part B' 0 E' U (Coefficient.x i)+∑' j,i.maskedTerm E' j U:=rfl
     rw [Hx]; convert added (f:=fun j=> F0 j U) ((P.regular_series hr).summable U |>.hasSum) (hasSum_zero) using 1; change _= J.exponentialEntry _ _ _ U+(_+0);rw [Hx]; simp_rw [hJ,tsum_zero,add_zero];rw [hx']; rfl -- syntax issue add `_`
   · intro i V;rw [← show profile E'.activities ((Q).forced)=_ from stows K P]; convert added (f:=fun j=>Q1 j i V) hasSum_zero (profiled E'.activities _ (rem_dominated hu) V i) using 1; change _=(0:ℂ)+(0+_); rw [zero_add,zero_add]
   simpa only [P1,consist,add_zero, Sum.elim_inl] using added (f:=P1) hasSum_zero hasSum_zero
end YM.LocalLTE.XPre
