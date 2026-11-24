import YM.OPE.Compatible.Gems.Glib
/-! # Terrain factor witnesses. Cov price exponentially dec -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*} {i k m:ℕ}{t C s u z ℓ v a c e r R:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown
variable {K:Sponsor G}{T:Seasons K}
section
variable (L:Host K T)(Y:Studio L)(J:Finset (Rubric G Y.X))
local notation "Fθ"=> L.ForestQ
set_option quotPrecheck false
local notation "μ"=>Y.μφ
noncomputable abbrev mirror := Amalg (Hκ L Y) (νMom L Y)
private lemma genericP {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X](A:Law X)(M:Measure X)[M.IsAddHaarMeasure] : IsProbabilityMeasure (Amalg A M):=inferInstanceAs (IsProbabilityMeasure (quart (united A A) (M.prod M)))
instance : IsProbabilityMeasure (mirror L Y):=by
        exact (genericP (Hκ L Y) (νMom L Y))
local notation "Vθ!"=>mirror L Y
abbrev overT (p:Y.St→ℝ):Prop:=∃ f:((↥J)→ℝ) →ℝ, p=f ∘ (Pip L Y J) -- parentheses
variable {q p: Y.St →ℝ}
lemma overT.divorce (h:overT L Y J p)(hp:overT L Y J q): overT L Y J (p*q):=by obtain ⟨f,hf⟩:=h; obtain ⟨g,hg⟩:=hp; refine ⟨f*g,?_⟩; rw [hf,hg]; rfl
def Hst (i:Drive L):Prop:=match i with | Sum.inl _=>True| Sum.inr i=> ∀ h:i.1∈Y.X,(⟨i.1,h⟩,i.2) ∈ J
lemma Visa (i: Drive L)(h:Hst L Y J i): overT L Y J (PulseP L Y i):=by
       rcases i with i|i
       · rw [funext (azWorld L Y i)]; exact ⟨fun _=>_,rfl⟩
       let u:= PulseP L Y (Sum.inr i); by_cases hR:i.1∈Y.X
       · let p:Rubric G Y.X:= (⟨_,hR⟩,i.2); have hv: p∈ J:=h hR; refine ⟨fun y=>u 0+y ⟨_,hv⟩, funext fun x=>?_⟩; rw[tagT L Y i x,dif_pos hR]; rfl
       exact ⟨fun _=>u 0,funext (fun i'=>by rw [tagT L Y i i',dif_neg hR,add_zero];rfl)⟩
lemma yieldX {S:Seats Fθ} {q:Sender L}(hp:Funded L S q a k)(h:∀ i:Key Fθ G,i.1∈ S → Hst L Y J (Sum.inr i))(j:Phase) : overT L Y J (fun x=> (q (Vtone L Y x)).seq j.val) :=by
       obtain ⟨f,hT,hf⟩:=hp.net; let P:= Pip L Y J; let U:= Boat L Y J; let z (x:Y.St):=(q (Vtone L Y x)).seq j.val; let s:=rip L.Z L.H G S; refine ⟨z ∘ U,funext fun x=>?_⟩; change z x=z (U (P x)); unfold z; simp_rw[hf,Function.comp_apply]; have he:s (Vtone L Y x)=s (Vtone L Y (U (P x))):=by
            funext i; let v:= Vtone L Y; ext l; let j: Key Fθ G:=(i.val,l); obtain ⟨p,hp⟩:= Visa L Y J (Sum.inr j) (h j i.property); have ht(y:Y.St): p (P y)=(s (v y) i) l:= by rw [← Function.comp_apply (f:=p),← hp,PulseP,breezeY,Tip_ψ]; rfl
            exact (ht x).symm.trans ((congr_arg p (drapeB _ _ (pros L Y J) (P x))).symm.trans (ht _)) -- patch
       rw [he]
abbrev remote (i:Drive L)(t:ℝ):Prop:=∀ j:(J:Type), t≤ separation (δV L.Z Fθ i) (pointK L.Z Fθ (shout G Y.X j.val))
abbrev ΤΙ (G:Gauge)(s c C u t:ℝ) (n:ℝ) (k:ℕ):=2*(((n*Real.sqrt (limbC G s c))*(C*Real.exp (-(u*t))))*ampleP k)
variable {L Y J}
variable (h:L.Rich s c e v u C)(ht:0<s)(hc:0≤c)(he:0<e)
include h ht hc he
lemma journey (i: Drive L)(hx:remote L Y J i t)(hn:(J.card:ℝ)≤z): Cane Vθ! (((PulseP L Y i) ∘ Prod.fst)- (PulseP L Y i ∘ Pier L Y J)) (ΤΙ G s c C u t z):=by
       have ht'(k:ℕ):0 ≤ ΤΙ G s c C u t z k:=by unfold ΤΙ; have he: 0 ≤z:= (by exact (Nat.cast_nonneg _).trans hn); have hz := h.vein.broad; have hc:0≤ ampleP k:=le_trans zero_le_one (le_max_left ..); positivity

       rcases i with i|i
       · rw [funext (azWorld L Y i)]; change Cane _ ((fun (_:Y.St×Y.St)=>cash (JetB G L.c) Y.w i)-(fun _=>cash (JetB G L.c) Y.w i)) _; rw[sub_self]; exact Cane.nil _ fun i _=>ht' _
       let p:= PulseP L Y (Sum.inr i); by_cases hA:i.1∈Y.X
       · let j:Rubric G Y.X:=(⟨_,hA⟩,i.2); intro k hk; have hY:= LapK L Y J h ht hc he j hx k hk; let f:= axY L Y j; have hz(y):p y=p 0+f y:=by rw[show p y= _ from tagT L Y i y,dif_pos hA]
         change Fault _ k (p ∘ Prod.fst - p ∘ Pier L Y J) _; rw [show p ∘ Prod.fst- p ∘ Pier L Y J= (f∘Prod.fst)-(f ∘ Pier L Y J) from funext fun i=>by change p i.1-p _=_ ; rw [hz i.1,hz (Pier L Y J i),add_sub_add_left_eq_sub];rfl]
         apply hY.mono le_rfl; unfold ΤΙ; rw [←two_mul,Fintype.card_coe]; have he:= h.vein.broad; have hp:0 ≤ ampleP k:= le_trans zero_le_one (le_max_left ..); gcongr
       rw [show PulseP L Y (Sum.inr i)=(fun _=>p 0) from funext fun y=>by rw [tagT L Y i y,dif_neg hA,add_zero]]; change Cane _ ((fun (_:Y.St×Y.St)=>p 0) - fun _=>p 0) _; rw[sub_self]; exact Cane.nil _ fun i _=> ht' _
end
end YM.OPE.Borealis.Galea
