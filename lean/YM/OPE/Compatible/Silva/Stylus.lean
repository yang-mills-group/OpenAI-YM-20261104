import YM.OPE.Compatible.Silva.Lote
/-! # Rebased chart cover. walking roots project all q
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n c f:Side}
variable (S:StepData c f)(he:Odd S.ratio.count.val)(H:Even c.val) (X: Plot H)
local notation "μ"=> even_both S.ratio H
local notation "X!"=> forest S.ratio he
section cast
omit S X
variable {D V:Type}{T:Score D V}{R P:Set V}
private lemma castB (p:T.Stand R)(h:R=P)(i:D): (h ▸ p:T.Stand P).Branch i↔p.Branch i:= by subst P;rfl
end cast
def stroll : Stir S H:= by
      change (stageScore _ _).Stand _; exact berths S.ratio H ▸ standWith S.ratio H he X
lemma strollD (i:Limb μ): (stroll S he H X).Branch (.inl i)↔(tripS S he H).Branch i:= (castB (standWith S.ratio H he X) (berths S.ratio H) (.inl i)).trans ((spinD S.ratio H he X i).trans (branch_rep ..).symm)
lemma strollR (i:Limb H): (stroll S he H X).Branch (.inr i)↔X.Branch i:= (castB (standWith S.ratio H he X) (berths S.ratio H) _).trans (spinW S.ratio H he X i)
private def ticketS : X.Free ⊕ (Blocx S he H) → (stroll S he H X).Free:= Sum.elim (fun i=> ⟨.inr i.val,mt (strollR S he H X _).mp i.property⟩) (fun i=>⟨.inl i.val, mt (strollD S he H X _).mp i.property⟩)
private lemma stove_s : Bijective (ticketS S he H X):=by
    constructor
    · intro a b h; rcases a with a|a <;> rcases b with b|b
      · exact congr_arg Sum.inl (Subtype.ext (Sum.inr.inj (congr_arg Subtype.val h))) -- inference
      · exact False.elim (Sum.inl_ne_inr (show Sum.inl b.val=Sum.inr a.val from congr_arg Subtype.val h.symm))
      · exact False.elim (Sum.inl_ne_inr (show Sum.inl a.val=Sum.inr b.val from congr_arg Subtype.val h))
      exact congr_arg Sum.inr (Subtype.ext (Sum.inl.inj (congr_arg Subtype.val h)))
    rintro ⟨i|i,h⟩
    · exact ⟨Sum.inr ⟨i,mt (strollD S he H X _).mpr h⟩, rfl⟩
    exact ⟨Sum.inl ⟨i,mt (strollR S he H X _).mpr h⟩, rfl⟩
def valley : (stroll S he H X).Free≃ X.Free⊕ Blocx S he H:= (Equiv.ofBijective _ (stove_s S he H X)).symm
open Pilot
local notation "J!" => stroll S he H X
local notation "V!" => valley S he H X
local notation "K!" => tripS S he H
lemma shineLow (x: Keys G (stroll S he H X).Free): lo_right S H G ((stroll S he H X).rollX x)=X.rollX (prL V! G x):=by
      ext1 i; by_cases h:X.Branch i
      · exact ( (stroll S he H X).keptZ 0 x (⟨.inr i,(strollR ..).mpr h⟩ : (stroll S he H X).Stable) ).trans (X.keptZ 0 _ (⟨i,h⟩:X.Stable)).symm -- zeros defeq
      let a:X.Free:=⟨i,h⟩; exact ((stroll S he H X).kept 0 x (Pilot.lead V! a)).trans (X.kept 0 (prL V! G x) a).symm
lemma shineHigh (x: Keys G (stroll S he H X).Free): lo_left S H G ((stroll S he H X).rollX x)=(tripS S he H).rollX (prR V! G x):=by
      ext1 i; by_cases h:(tripS S he H).Branch i
      · exact ((stroll S he H X).keptZ 0 x (⟨.inl i,(strollD ..).mpr h⟩ : (stroll S he H X).Stable)).trans ((tripS S he H).keptZ 0 _ (⟨i,h⟩:(tripS S he H).Stable)).symm
      let a:(tripS S he H).Free:=⟨i,h⟩; exact ((stroll S he H X).kept 0 x (Pilot.secondC V! a)).trans ((tripS S he H).kept 0 (prR V! G x) a).symm
abbrev rayS (G:Gauge): Keys G X.Free→L[ℝ] Bid.Dir G c:= cloak H ∘L LinearMap.toContinuousLinearMap X.rollX
def lamps (G:Gauge): Keys G (stroll S he H X).Free→L[ℝ] (Bid.Dir G c × AxisChart G X!):= ((rayS H X G)∘L prL V! G).prod ((EchoV S he H G) ∘L prR V! G)
lemma shines (u: Keys G (stroll S he H X).Free): lamps S he H X G u=(rayS H X G (prL V! G u), EchoV S he H G (prR V! G u)):=rfl
variable {d:ℕ}{K:Sponsor G}{Q:Seasons K}{v:ℝ}
variable (A:Alps K Q d v)(t:S.Choices)
set_option maxHeartbeats 200000 in
lemma loves (u: Keys G (stroll S he H X).Free): worldF S H t A ((stroll S he H X).rollX u)= (pane X! t A.clip A.live (lamps S he H X G u))/4 - mural μ A 0:=by
     unfold worldF noiseC; rw [shineHigh,shineLow]; unfold mural swornV; dsimp only [Function.comp_apply]; rw [← cloak_e,←cloak_e,echoRoll]; rw [shines]; unfold pane uncurry score; ring_nf; rfl
lemma tints (b:ℝ)(u: Keys G (stroll S he H X).Free):
    let z:= lamps S he H X G u
    worldW S H t b A ((stroll S he H X).rollX u)=Real.exp (-b*(pane X! t A.clip A.live z)/4-(springF X! A.live z.2)/4):=by
        intro z; unfold worldW tintT; rw [← Real.exp_add]; have ht:= loves S he H X A t u; unfold worldF at ht
        congr 1; rw [show gilt μ A (lo_left S H G ((stroll S he H X).rollX u)) =springF X! A.live z.2/4 from ?_]; unfold z; rw [show noiseC S H t _ = _ from eq_sub_of_add_eq (add_comm .. |>.trans ht)] ; ring
        unfold gilt swornY; dsimp only [Function.comp_apply]; rw [shineHigh, echoRoll];rfl -- comp
end YM.OPE.Cascade.Rill
