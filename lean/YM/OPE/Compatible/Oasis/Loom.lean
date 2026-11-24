import YM.OPE.Compatible.Oasis.Crypt
/-! # Instant calibration check. Support cover chosen jointly for a family of coefficients
prior to making comparisons at any scales. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.CardinalQ
open Function Filter Set Finset Lattice Laurent RG Wilson
open scoped Topology BigOperators Classical
open Drift Stroke Yolk Pill Spells
open Next.Scheduling Clock
open Lass Lass.Zest
open Source Labels
variable {G:Gauge}{X E I:Type}{t s z V:ℝ}{k k' m:ℕ}{T:Stage}
-- Pace mark tree certificate
structure Tag (A:Stage)(x:ℝ)(P:RG.BudgetPoint)(b:ℝ):Prop where
       order :P.order=A.order
       epoch :P.B=coverJ x
       tax :P.threshold=θj x
       width :P.supportExponent=A.supportExponent
       scale:P.power=A.power
       beta :x/2 ≤ b ∧ b ≤ 2*x
variable {n:Side}{A:Labels.Frame G k}{Q:Rep G n}{P:A.Coeff → Coefficient A n}{H:Hol G}{S:SectionData A}
noncomputable def rectangle (S:SectionData A):= S.stencil.sup (fun x=> Finset.univ.sup (fun i:Axis=> (x i).natAbs))
lemma payK (U:SectionData A)(h:rectangle U≤ k'): U.stencil⊆ Lattice.box k':=by
       intro i hi; have he(a:Axis): (i a).natAbs ≤ k':= le_trans ((le_sup (f:=fun a:Axis=>(i a).natAbs) (mem_univ a)).trans (Finset.le_sup (s:=U.stencil) (f:=fun x:Cover=>Finset.univ.sup fun i=> (x i).natAbs) hi)) h; refine Lattice.box_test.mpr ⟨?_,?_⟩ <;> intro a <;> specialize he a<;> omega
noncomputable def fieldQ (X:SectionData A)(x:ℝ):= rectangle X+ budgetK (coverJ x)
structure Registered (v:ℝ) (T:Stage)(H:Hol G)(Q:Rep G n)(S:SectionData A) (P:A.Coeff→ Coefficient A n):Prop where
       TagQ : Tag T v Q.p Q.beta
       budget : Cache S 0 P T.columns T.columns (salary v) (h:=H) (R:=Q)
structure Grant (P₁:Torch S H 0 Q P m (salary z)) (T:Stage):Prop where
       a : P₁.a=T.columns
       c : P₁.c=T.columns
       hue: P₁.B=fieldQ S z
abbrev Θsize (k:ℕ):= 10*k+8*k+3
lemma pointR {t:ℝ}(h:Registered t T H Q S P)(hp:S.Sound H)(ht:Widen Q.p (fieldQ S t))(hi:Θsize (fieldQ S t)≤ n.val)(hy:m+6 ≤T.order):∃ P₁:Torch S H 0 Q P m (salary t),Grant (z:=t) P₁ T:=by
       obtain ⟨Z,H⟩:= giftQ h.budget hp (payK S (Nat.le_add_right ..) (k':=fieldQ S t)) (by rw [h.TagQ.epoch]; exact Nat.le_add_left ..); unfold Θsize at hi; exact ⟨⟨_,_,0,h.budget,fieldQ S t,Z,(by omega),(by omega),H,h.TagQ.order.symm ▸ hy,ht⟩,⟨rfl,rfl,rfl⟩⟩ -- u field implicit
variable {β v:I→ℝ}{l:Filter I}(h:Tendsto β l atTop)
lemma fieldReading (A:Labels.Frame G k)(U:SectionData A)(hp:Tendsto β l atTop): Receipt β l (fun i=> (fieldQ U (β i):ℝ)):=by
        unfold fieldQ budgetK;push_cast; let x:=carth hp; have hb(c:ℝ): Receipt β l (fun _=>c):= Score.steady c x; let f:= coverPs hp; exact (hb _).plus (((((hb 4).product f).plus (hb _) x).product f).plus ((hb 2).product f) x) x
variable (W:I→BudgetPoint)(ht:∀ᶠ i in l,Tag T (β i) (W i) (v i))
include h ht
lemma flowers : TuneUp β l W (fun i=> gap (v i)):=by
       have he:=boothP (ht.mono fun _ hi=>hi.beta); have hp:=he.track h; exact ⟨(hp.eventually_gt_atTop 0).mono fun i hi=> Clock.gp hi,h,(ht.and (h.eventually_gt_atTop 0)|>.mono fun i hi=> hi.1.tax.trans (peony hi.2.le).symm),⟨v,he,(hp.eventually_ge_atTop 0).mono fun i hi=>(seedθ hi).symm⟩⟩
lemma widenS (S:SectionData A) : ∀ᶠ i in l,Widen (W i) (fieldQ S (β i)):=by
        have he:= flowers h W ht; let t(i:I):ℝ:= fieldQ S (β i); have hg:= (Score.steady (1:ℝ) (carth h)|>.plus (fieldReading A S h) (carth h)).power T.power (carth h); have hx:= ((Spells.boltP he).pays (carth h) |>.mul (waitG h hg)).tends (by norm_num) (carth h); filter_upwards [ht,hx.eventually (ge_mem_nhds zero_lt_one)] with i hi hp; unfold Widen; rw [hi.scale]; exact hp
end YM.OPE.CardinalQ
