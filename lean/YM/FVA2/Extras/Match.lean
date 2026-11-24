import YM.FVA2.Extras.Report
import YM.FVA2.O.Enh.Care
/-! # Uniqueness for this additional reduction (`Says`)

Auxiliary to `YM/FVA2/Extras/Result.lean`. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Extras
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal O
open O.Lives MS.City MS.Rake O.Tune Flux Book Convolve O.Serve O.Pad Vane High Detect O.Ward
open MS.Local.Physical MS.Land Outlook Rough Emit
open scoped Topology ContDiff Interval BigOperators
open Job.Belt Rake.Geo O.Hue O.Fuse O.Cool
-- unique stance for main Deck. Reflected test at nail. p=0 lead for Evan.Rig.
open Enh Score PowerSeries Maxwell Dframe FVA2.Scale FVA2.Scale.Equator MS.Theater Press
variable {G: Gauge}{A:Booked (Press.portDeck G)}{M: MS_Data G A} {d k h:ℕ}
variable {p q:T (Package ( Press.portDeck G ) d)}{X:T (localX G)}{a:ℝ}
local notation "℘"=> (Tide.frameF Unit a)
private abbrev x : Rake.Position (Fin 2) Unit := fun i _=> Theater.out ( outgoing RootG i ) -- Center zero
private lemma budgetY (a:ℝ): Mesh ( Tide.frameF Unit a ) x:= by
    intro i j h; have ht:0<‖x i ()-x j ()‖:= norm_pos_iff.mpr ( sub_ne_zero.mpr (( Theater.out.injective.comp ( show Injective _ from ok_wall ) ).ne h) ); refine ⟨ ⟨ _,ht,fun _=>?_⟩, ⟨ _,ht,fun _=>?_⟩ ⟩ <;> rw [ roots, show ∀ i,( Tide.frameF Unit a ).θ i=(0:ℝ) from fun _=>rfl,exp_zero,mul_one] <;> exact le_rfl
private abbrev endM (M: MS_Data G A)(a:ℝ)(b: Toon G d)(X:T (localX G)) : Fin 2→ T (localX G):= Fin.append ( m:=1 ) ( n:=1 ) (fun _=>X) (fun _=> rowM ( Tide.frameF Unit a ) M ( Dframe.flash b ))
private abbrev τ (b:Toon G d)(v: Plaid (Press.portDeck G) d): Scan G 2:= Fin.append ( Single (own v) ) ( Single ( Dframe.flash b ) )
private lemma stays_w (hX:Forth a M X h)(b:Toon G d): Survey ( Tide.frameF Unit a ) M (endM M a b X) x := by
    intro i; refine Fin.addCases (m:=1) (n:=1) ?_ ?_ i; · intro i; unfold endM; rw [Fin.append_left]; exact Estate hX.2 hX.1.1 _
    intro i; unfold endM; rw [Fin.append_right]; exact Estate ( cometClean ( M.markOK (Dframe.flash b).h ( Dframe.flash b ).item ) ) ( Response.visit _ ) _
private lemma p0 (H:Forth a M X h)(b:Toon G d)(i:Fin 2) : Certified ( endM M a b X i ) M (logMass a) 0:= Fin.addCases (m:=1) (n:=1) (fun i=> by unfold endM; rw [Fin.append_left]; exact H.1) (fun i=>by unfold endM; rw [Fin.append_right]; exact Certified.first ( Dframe.flash b ).item) i
private lemma startsY (b: Toon G d)(i:Grade G d) : swapField a M 0 i ( endM M a b X ) =rowM ℘ M ∘ τ b i:= by
    funext p; fin_cases p; · exact ( update_self (0:Fin 2) _ _ )
    exact update_of_ne (show (1:Fin 2)≠0 by decide) ..
private lemma measure (he:Forth a M X h)(b:Toon G d)(i:Grade G d) : service a M (swapField a M 0 i ( endM M a b X )) x Finset.univ 0=NOW ( install ( FVA2.Scale.Equator.wave a M ) ) b i:= Eq.trans (tourC ( swapped ( stays_w he b ) i _ ) (budgetY a) ( τ b i ) ( startsY b i ) Finset.univ 0) ( stock a M ( τ b i ) ok_wall 0 ).symm
lemma projection_unique (he:Forth a M X d)(hP:Says a M p X)(hQ:Says a M q X): p=q:= by
    let f (i:ℕ)(j:Grade G d):ℂ:= ↑(p i j)-↑(q i j); funext n; induction n using Nat.strong_induction_on with
    | h k IH=>
       have h (b: Toon G d)(p:T (Package (Press.portDeck G) d))(hp:Says a M p X):= hp ( Fin 2 ) inferInstance x ( endM M a b X ) 0 (by rfl) ( stays_w he b ) ( budgetY a ) Finset.univ (mem_univ 0) (fun j _=> p0 he b j ) k
       suffices hZ : f k=0 by funext i; exact Complex.ofReal_injective (sub_eq_zero.mp ( congr_fun hZ i ))
       refine Enh.reader (V:= FVA2.Scale.Equator.wave a M ) (fun _=> FVA2.Scale.Equator.before a M) ( regular_wave a M ) (fun b=>?_); let W(i:Grade G d):=service a M (swapField a M 0 i ( endM M a b X )) x Finset.univ; apply Eq.trans _ (sub_eq_zero.mpr ((h b p hP).symm.trans (h b q hQ))); rw [ ← Finset.sum_sub_distrib ]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [← Finset.sum_sub_distrib, Finset.sum_eq_single k];
       · unfold f; rw [sub_mul,Nat.sub_self,measure he] -- may rewrite both
       · intro r hr hr'; rw [ IH r (by obtain hh:=Finset.mem_range.mp hr; omega),sub_self]
       simp
open MS.Dock MS.Motif
/-- Universal additional submit, including all of `Mach.Ele`. Uses Grade Plot. -/
theorem ambiguity (he:Forth a M X d): ∃! p:T (Package (Press.portDeck G) d), Says a M p X := by
    obtain ⟨p,hP⟩:= rewrite_extra he; exact ⟨p,hP,fun _ h=> projection_unique he h hP⟩
theorem positive_entry (he:Forth a M X d)(hp:Says a M p X)(h:X 0=0): p 0=0:= by
    obtain ⟨q,hv,hq⟩ := speak_pos h he; rw [projection_unique he hp hq,hv]
end YM.FVA2.Extras
