import YM.LocalLTE.XPre.Lead
import YM.LocalLTE.XPre.Tones
import YM.LocalLTE.Ticket.Prize
/-!
# Consuming all symbolizations issued by H at one label position
No φ equality across horizons. Repainting orbit uses true incoming evaluations.
Sum.Invariant.Same lamps.
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
variable {v w:ℂ}{X Y:Set Wing}{M:ι→ Leaf R}{g:ι→ℂ}{φ:MergeProof.Response G c}{L:GaugeDoor R C}
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
local notation "κZ"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
local notation "κI"=> Real.sqrt (H.levels.clock.forcedAllowance m)
local notation "HX"=> H.S.block m
local notation "v'"=> (((HX|>.val):ℂ)^d)
variable (d) (K: Guard.Keeper ((H.rep N n (m+1)).p) ((H.rep N n (m+1)).activities)) (U: Vinca.Gateway ((Labels.frames G).level d) (hol G) (H.rep N n (m+1)) (H.S.side m n)) (A: Prices)
variable {B: Heading ((Labels.frames G).level d)} {π c' d' w:ℝ}(hD: Vinca.Key (localSection G d) H N n m (hol G) L U c' π w B X)
include hD
variable (ha: ∀ i,Y (.gasKey (cart (R:=H.rep N n (m+1)) K i)))(ht:∀ i,X (.gasKey (cart (R:=H.rep N n (m+1)) K i)))(hq:0≤π)
variable (V:Voice ((Labels.frames G).level d) H n (m+1)) (T:Employ H N n (hol G) m V K)
variable (hV:SoundDoor (H.levels.clock.op m n) L) (hP : XPre.Permits (H.rep N n (m+1)) (H.rep N n m) Y L d ((((H.S.block m).val:ℂ)^d)) U A κ p l) (hb:Heard (localSection G d) H N n (hol G) (m+1) V)
local notation "pZ"=> κZ*(r+r)
local notation "feeE"=> A.beam+2*(ν+r+pZ)
local notation "x0"=> (H.levels.params (m+1)).columns
local notation "gnE"=> A.grant+A.canopy*(x0+pZ)
local notation "baseq"=> 2*(r+pZ)
-- stamina all X'. supply any Funds with properties. not altering calculator via proofs.
variable (Z': ((Labels.frames G).level d).Coeff→ Coefficient ((Labels.frames G).level d) (H.S.side (m+1) n))
variable (hs:Funds (m:=m+1) κ (hol G) p l (localSection G d) (H.rep N n (m+1)) V Z' (Real.sqrt (H.levels.clock.forcedAllowance (m+1))) r ν)
local notation "CP"=> parcelP H N n φB m V K U T
local notation "F0" i=> (V.plays (V.index.symm (Size.axis F i)))
include hP ha ht hq hb hs hV
variable (h:H.Selected)(hm:m<N)(hc:Chorus H N n (m+1) V) (hY:Y.Finite)(hr:ConnectedActivityE6.Reliable G κ κ')(hs0:Menu.Tunes L)
local notation "A1"=> R1
local notation "A0"=> R0
local notation "lx"=> ((H.levels.budget (m+1)))
local notation "tax"=> rotationP F ((R1).p.order) ((R1).p.power)
local notation "total"=> (fun v=> orbitCost F*(F).coeffSize (V.index v))
local notation "ZX"=> marksP H N n φB m V K U T
-- dimension Root lookup Hart. preserve Mood. scalar action EXACT unit counter.
local notation "Xξ"=> rotationP F (A1|>.p.order) (A1|>.p.power)
include h hm hc hY hs0 hr
set_option maxHeartbeats 620000 in
lemma reprisePX (v:(F).Coeff) : let Vq:= V.plays v; let z:= ZX v;∃ Q:Set Wing,Q.Finite ∧ Circuit Q L d κ p l 0 0 v' (Vq.exponentialEntry 0 B' (A1)) (profile (A1).activities Vq.forced) (profile (A0).activities z.forced) ((V.index v) 0) ((total v)*(Xξ*feeE)) ((total v)*gnE) ((total v)*(Xξ*baseq)):=by
    intro A1' Z; let a:= A1; let c:= A0
    let Fm (m':Motion) : (a).activities.Moves m'.1 ((H.levels.clock.op _ n).ratio.embed 0):=(h.represents N n (m+1) hm).good.labels.moves _ _ |>.some
    let X': Set Wing:= ⋃ i:Motion,(Wing.labelRoute (Fm i)) '' Y; let α(z:Tally F):= Motion.patch F z.1 (Size.axis F z.2); let j i:= V.index.symm (Size.axis F i); let f z:= V.plays (V.index.symm (α z)); let P(i):= (CP i)
    let t:= (chips F).comp V.index.toLinearMap
    let u₀ (m':Motion): (c).activities.Moves m'.1 0:= T.turns m'; let O (j:Tally F):= audition (u₀ j.1) (P j.2); let e' z:= Extra.Histories.stretch (t v z) (O z)
    have hrZ i:= XPre.marl d K U A hD ha ht hq V T hV hP hb Z' hs i -- argument+
    have hv':(Y⊆Y):=fun _ h=>h
    have hhQ(z:Tally F): let Ti':= V.index.symm (Motion.patch F z.1 (Size.axis F z.2)); let U0:=V.plays Ti'; Circuit X' L d κ p l 0 0 v' (U0.exponentialEntry 0 B' a) (profile a.activities U0.forced) (profile c.activities (O z).forced) ((Motion.patch F z.1 (Size.axis F z.2)) 0) (tax*feeE) gnE (tax*baseq):=by
       intro Ti' U0; let i:=z.2; let m':=z.1; let V':Site (H.S.side (m+1) n):= (H.levels.clock.op m n).ratio.embed 0
       have he: V'=0:= Motion.embed_origin _; have hAA:X'≥ (Wing.labelRoute (Fm z.1)) '' Y:=subset_iUnion (fun i:Motion=> (Wing.labelRoute (Fm i)) '' Y) z.1
       have hmV:Ti'=Motion.patch F z.1 (j z.2):= V.index.injective (by rw [← hb.moves];change V.index (V.index.symm _)=_;simp [j])
       have hp:= XPre.turning (hrZ i) z.1 0 (Fm z.1) hV hs0 hr (show scalar z.1 _= v' from (by unfold Motion.scalar;split<;>simp)) -- hr shadow.Type. 
       have hp:= XPre.widened hp le_rfl le_rfl hAA le_rfl -- inferred hp.order
       rw [show U0= V.plays (Motion.patch F z.1 (j z.2)) from congr_arg _ hmV]
       rw [← hc.pages, show profile c.activities (O z).forced= _ from MergeProof.foyer z.1 0 (u₀ z.1) (P z.2), ← chanting B' H N n _ φB V (sound G d) hb hc h hm (fun U=>?_) ]
       · rw [show (H.levels.clock.op _ n).ratio.embed 0=0 from he] at hp; simp only [affine,Signed.act_zero,zero_add] at hp
         rw [show Motion.patch F z.1 (Size.axis F z.2) 0=scalar z.1 (Size.axis F i 0) from ?_]; exact hp
         unfold Motion.patch scalar; split<;>simp only [Pi.star_apply,Push.Local.act_at_zero] <;> rfl
       exact (Tour.bright H h N n _ hm U).ne' -- ns
    have hM₀ (z:Tally F): Circuit X' L d κ p l 0 0 v' ((t v z) • (f z).exponentialEntry 0 B' a) (t v z • profile a.activities (f z).forced) (profile c.activities (e' z).forced) (t v z*α z 0) (‖t v z‖*(tax*feeE)) (‖t v z‖*gnE) (‖t v z‖*(tax*baseq)):=by
       rw [show (e' z).forced= t v z • (O z).forced from rfl, profile_scale]; exact XPre.scalar_t (hhQ z) _
    let φ i:= Vinca.coins H N n m φB U (rack K (F0 i)) (T.fullP i) i
    have hy : 0 < κI:= Real.sqrt_pos.mpr (forcedPos ..)
    have hu(z:Tally F):∃ sx:ℝ,(e' z).remBound 0 c (Real.sqrt (H.levels.clock.forcedAllowance m)) sx:=by
       obtain ⟨v₀,hV,hW⟩:= XPre.recognized d K U (F0 z.2) (T.fullP z.2) hD z.2 ht hq
       have hx: (P z.2).Format 0 φB c:= merge_format (code _) (φ z.2) (fun i=> (hV i).1); have hp:=(merge_budget (code _) (φ z.2) hy (fun i=>(hV i).2) hW).1
       have he := Planned.GuardedAtom.audition_receipt z.1 (u₀ z.1) ((by decide : 2 ≤ 4).trans (Next.Foundations.actual_side_ge H.S m n)) (sound G d) hx (rem_tabs.mp hp).choose_spec.choose_spec.1 -- actual rem to Tab. order
       exact ⟨_,stretch_rem _ (he.2.2.1.bound le_rfl)⟩
    choose v₀ hV₀ using hu
    have h0 := hrZ 0
    have hhR : 0 ≤ (tax:ℝ):= zero_le_one.trans (River.rotation_one ..)
    obtain ⟨IX,hIX,Gx,aIX,OIX,xv,hx,hu⟩:= h0.lamps -- parser.
    have hfee:0≤ tax*feeE:= mul_nonneg hhR (sumBudget_credit hx.purchase)
    have hG:0≤ gnE:= sumBudget_credit hx.cost.toll.choose_spec.1
    have hi:0≤ tax*baseq := mul_nonneg hhR (budget_nonneg hu.1)
    have hv (M:ℝ)(ht:0≤M):SumBudget (fun i=> ‖t v i‖*M) ((total v)*M):= by
       refine ⟨fun i=> mul_nonneg (norm_nonneg _) ht,Summable.of_finite,?_⟩
       rw [tsum_fintype,← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (MergeProof.rip ..) ht
    refine ⟨X', Set.finite_iUnion (fun p=> hY.image _),?_⟩
    apply bandR hV hM₀ _ _ (fun x V=> profile_merge (code _) e' hy hV₀ Summable.of_finite x V) _ (hv _ hfee) (hv _ hG) (hv _ hi)
    · let g' := (IsLinearMap.mk' _ (expoLinear (T:=B') _ _ hb.book (fun i=> (hb.earns i).2))).comp V.index.symm.toLinearMap
      intro Ux; let v₀:= V.index v
      have hyx : A1'.exponentialEntry 0 B' a Ux= (g' v₀) Ux:=by unfold A1'; change _=(V.plays (V.index.symm v₀)).exponentialEntry 0 B' a Ux; rw [show V.index.symm v₀=v from V.index.symm_apply_apply _]
      rw [hyx, ← fixing F g' v₀]; simp only [Finset.sum_apply]; exact hasSum_fintype _
    · let g'(v) := profile a.activities (V.plays v).forced;intro i Ux
      let S:=(IsLinearMap.mk' g' (inkL V.plays V.charge hb.book (fun i=> (hb.earns i).2))).comp V.index.symm.toLinearMap
      let x':=V.index v
      have hyx: profile a.activities A1'.forced i Ux = S x' i Ux:=by change _=g' (V.index.symm x') i Ux; rw [show V.index.symm x'=v from V.index.symm_apply_apply _]
      rw [hyx,← fixing F S x']; simp only [Finset.sum_apply]; exact hasSum_fintype _
    let Y':= V.index v; have hx: (∑ z:Tally F,t v z* α z 0)= Y' 0:= by
       have he : ∑ z:Tally F,t v z • α z=Y' := fixing F LinearMap.id (Y'); rw [← he,Finset.sum_apply]; rfl
    convert hasSum_fintype _ using 1; exact hx.symm
end YM.LocalLTE.XPre
