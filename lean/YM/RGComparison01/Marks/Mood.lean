import YM.RGComparison01.Marks.Crystal
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Haul
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Mood
open Function Filter Set Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Work.H03
open Pressure Progress.DirectedRecipe Rack ConnectedActivityE6 Finset Push Push.AbsoluteSums
open PhysicalNext.Repeat Mallow Daisy Merge Switch
open AnalyticBridge VerifiedReset Collection Quotes Song Refrain
open Extra.Iteration Animals
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {ι:Type} [Fintype ι] {U:Type} {G : Gauge}{n : Side} {r c δ A B κ γ w v a:ℝ}
open Merge Motion GridRenewal.Rain
variable (X:Pipes G n)(d:Tap G n)(P:BudgetPoint)(b:ℕ) (x:Site n)
variable {v:ℝ}
local notation "TT" => Tap G n
abbrev slate (n:Side):= ℕ ⊕ Site n
def trade (n:Side):ℕ≃slate n:= numbering (ℕ⊕ Site n)
-- blank distinguishing site masks on SAME step before reset
abbrev Events := Site n → Config G n→ℝ
def counsel : slate n→Support n:=Sum.elim X.softer (neighbors b)
lemma latent (i:slate n): (counsel X b i).Nonempty:= by
   rcases i with i|i; exact X.sites i; exact ⟨i,(neighbors_mem ..).2 (by simp)⟩
def Loft : Pipes G n:= { X with softer:= counsel X b ∘ trade n,sites:= fun _=> latent X b _ }
def quip (Z: Events (G:=G) (n:=n)): slate n→ Config G n → ℝ:= Sum.elim d.logarithm Z
abbrev blank : Tap G n:= { d with logarithm:= quip d 0 ∘ trade n }
-- copy pays.Preserved
local notation "ℙ"=> Marlin.raiser P
section vapor
variable (a d0:ℝ)
abbrev Frigate {X : Pipes G n} (Q : BudgetPoint)(W:ℕ→ℝ)(a:ℝ) := Payments.softCost Q X W a
omit [Fintype ι] in
lemma feather (hs : Vapor X d (Marlin.raiser P) a): Vapor (Loft X b) (blank d) (Marlin.raiser P) a:= by
   obtain ⟨hv,h,hB⟩:=hs.funds; let p i:= Sum.elim hv 0 (trade n i); let f:=Sum.elim d.logarithm (0: Events (G:=G) (n:=n)); let e:=trade n; let c:=counsel X b; let q:=P.threshold
   have hb:∀ i:slate n, UsesFinal q (c i) (f i) ∧ GaugeInvariant (f i)∧ Measurable (f i)∧(∀ V, Healthy q (c i) V→ f i V=0)∧∀ V,‖f i V‖ ≤ Sum.elim hv 0 i:=by
     rintro (i|i); exact ⟨hs.texts i,hs.travels i,hs.tails i,hs.visits i,hB i⟩; exact ⟨fun _ _ _ _=>rfl,fun _ _=>rfl,measurable_const,fun _ _=>rfl,fun _=>(norm_zero (E:=ℝ)).le⟩
   refine ⟨fun i=>(hb (e i)).1,fun i=> (hb (e i)).2.2.2.1,fun i=>(hb (e i)).2.1,fun i=>(hb (e i)).2.2.1,p,?_,fun i=> (hb (e i)).2.2.2.2⟩
   refine ⟨fun i=> ?_,fun i=> ?_⟩
   · unfold p; cases trade n i; exact h.1 _; rfl
   let t (j:slate n):= if i∈ c j then Sum.elim hv (0:Site n→ℝ) j*Real.exp ((P.supportExponent+1+1)*coverNumber P.B (c j)) else 0
   refine Cost.equiv e (show SumBudget t a from ?_); rw [← add_zero a]; exact Cost.sum (h.2 i) (by simp [t,SumBudget] : SumBudget (fun i=>t (.inr i)) 0)
-- gander.Real.Reflection of supports
abbrev Cirr := ∀ (s:Signed) (z:Site n),∃ u:Equiv.Perm ℕ,(∀ i, X.softer (u i)=(X.softer i).image (Lattice.affine s z)) ∧ ∀ V i,d.logarithm (u i) V=d.logarithm i (Lattice.pull s z V)
omit [Fintype ι] in
lemma gander (h:Cirr X d): Cirr (Loft X b) (blank d):=by
   intro s z; obtain ⟨u,he,ht⟩:= h s z; let p:= Push.Local.turnSites s z; let k:= Equiv.sumCongr u p; let q:= trade n
   have hp i:q ((congo q k) i)=k (q i):=Refrain.perch _ _ _
   refine ⟨congo q k,fun i=>?_,fun U i=>?_⟩
   · change counsel X b (q _)=_; rw [hp]
     suffices hh:∀ i:slate n,counsel X b (k i)= (counsel X b i).image (Lattice.affine s z) from hh _
     rintro (j|j); · exact he _
     change neighbors b (p j)= (neighbors b j).image p; ext x; obtain ⟨x,rfl⟩:= p.surjective x; constructor
     · intro h; have hy:separation j x≤ b:=by rw [← Push.Local.turn_sep s z]; exact (neighbors_mem ..).1 h
       exact mem_image_of_mem p ((neighbors_mem ..).2 hy)
     intro h; obtain ⟨k,hk,h⟩:=mem_image.mp h; obtain rfl:k=x:= p.injective h; exact (neighbors_mem ..).2 ((Push.Local.turn_sep ..).trans_le ((neighbors_mem ..).1 hk))
   change quip d 0 (q _) U=_; rw [hp]
   suffices hh:∀ i:slate n,quip d 0 (k i) U=quip d 0 i (Lattice.pull s z U) from hh _
   rintro (j|j); exact ht U j; rfl
-- old marlin voucher, strengthened to produce same.Local.*
structure Clay (p : BudgetPoint)(Z : Pipes G n)(D : Tap G n)(d h : ℝ) : Prop where
   kitchen : Vapor Z D (Marlin.raiser p) d
   lamp : ∃ a f κ, Payments.hardCost (Marlin.raiser p) Z f a ∧ (∀ i U,‖D.forced i U‖≤ f i) ∧ Payments.Rates p.B h a d κ
   prior : (Z.pours D).ForcedFamily p
   rotation s b : Nonempty ((Z.pours D).Moves s b)
   soft : Cirr Z D
variable {X d P}
omit [Fintype ι] in
lemma hand (hc:Clay P X d v w) (b:ℕ): Ingredients (Loft X b) (Marlin.dummy (blank d)) (Marlin.raiser P) 0 w:=by
   have hp:= feather X d P b v hc.kitchen
   obtain ⟨p,h,hp'⟩:= hp.funds
   obtain ⟨a,f,κ,hF,hf,hv⟩:=hc.lamp
   exact Marlin.cannon hc.prior hc.rotation (fun i=>⟨hp.texts i,hp.tails i,hp.travels i⟩) (fun i U hx he=> hx (hp.visits i U he)) (gander X d b hc.soft) (show Payments.rooted (blank d) _ _ from fun i U=> ⟨hf i U,hp' i U⟩) (hp:=hF) (hq:=h) hv
end vapor
-- soft duel.fintype
abbrev rite (A: Site n → Config G n→ Ways ι) (x:ℝ)(j:Finset ι): Code G n := quip d (fun o U=> A o U x j) ∘ trade n
variable (Y: Site n → Config G n→ Ways ι) (u:ℝ)
structure Vaporous (p:BudgetPoint)(X:Site n→ Config G n → Ways ι)(b:ℕ)(α t:ℝ) : Prop where
   off i y j:X i y 0 j=0
   tidy x (ht:x∈Icc (0:ℝ) 1) i j: Trio.Tidy p (neighbors b i) (fun V=> X i V x j)
   idle t (ht:t∈ Icc (0:ℝ) 1) i j V: Healthy p.threshold (neighbors b i) V→X i V t j=0
   billed : ∃ u:Site n→ℝ,(∀ i,Paid (X i) (u i)) ∧ Ac.Hit (neighbors b) p.B u α t
include X P
lemma Frost.meets (h : Vapor X d P a) (hp:Vaporous P Y b (P.supportExponent+1) u): Frost (Loft X b) (blank d) P (rite d Y) (P.supportExponent+1) (a+u):= by
   obtain ⟨v,hv,hf⟩:=h.funds; obtain ⟨q,hq,hQ⟩:=hp.billed
   let e:=trade n; let X' x t:=quip d (fun o U=>Y o U x t); let c:=counsel X b; let p:=Sum.elim v q
   have ht : ∀ i:slate n, Paid (fun U x j=> X' x j i U) (p i):= by
     rintro (i|i); exact Switch.constant _ (hv.1 i) (hf i); exact hq i
   have hh: ∀ (x:ℝ)(hx:x∈ Icc (0:ℝ) 1)(i:slate n)(j), Trio.Tidy P (c i) (X' x j i) ∧ ∀ V, Healthy P.threshold (c i) V→ X' x j i V=0:= by
     rintro x hx (i|i) j; exact ⟨⟨h.texts i,h.tails i,h.travels i⟩,h.visits i⟩; exact ⟨hp.tidy _ hx _ _,hp.idle _ hx _ _⟩
   refine ⟨fun j=> ?_,fun x hx i j=>(hh x hx (e i) j).1.uses,fun x hx i j=>(hh x hx (e i) j).2,fun x hx i j=>(hh x hx (e i) j).1.invariant,fun x hx i j=>(hh x hx (e i) j).1.borel,p∘ e,fun i=>ht _,fun i=>?_⟩
   · ext a V; change X' 0 j (e a) _= quip d 0 (e a) V; cases e a; rfl; exact hp.off _ _ _
   let f (j:slate n):= if i∈ c j then p j*Real.exp ((P.supportExponent+1)*coverNumber P.B (c j)) else 0
   exact Cost.equiv e (show SumBudget f (a+u) from Cost.sum (hv.2 i) (hQ i))
omit [Fintype ι] in
lemma vapored (h:Vapor X d P a)(x:ℝ)(i:Finset ι)(V:Config G n): ∑' p,rite d Y x i p V=(∑' p,d.logarithm p V)+ ∑ o:Site n,Y o V x i:= by
   obtain ⟨f,hv,hF⟩:=h.funds
   have hh := (Activities.summable_charge X.sites hv.1 (Payments.drop_reserve P _ hv.1 hv.2)); have hp:Dominated d.logarithm:= ⟨f,hh,hF⟩
   let p (j:slate n):= quip d (fun o U=> Y o U x i) j V
   change ∑' j,p (trade n j)= _; rw [Equiv.tsum_eq (trade n), Summable.tsum_sum (f:=p) (hp.summable V) Summable.of_finite,tsum_fintype (f:=fun i:Site n=>p (.inr i))]; rfl -- maybe unnecessary
end YM.RGComparison01.Mood
