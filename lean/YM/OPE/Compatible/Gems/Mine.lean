import YM.OPE.Compatible.Gems.Equip
/-! # epoch proximity activated.Arity⁄weights -/
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
variable (L:Host K T)(Y:Studio L)(w: Bid.Dir G L.c)
set_option quotPrecheck false
local notation "Fθ"=> L.ForestQ
local notation "L!"=> majr L
abbrev Rebound (ℓ:ℝ)(i:Drive L):Prop:= match i with | Sum.inl i=> cash (JetB G L.c) Y.w i=cash (JetB G L.c) w i| Sum.inr i=>∃ j: Rubric G Y.X,i= shout G Y.X j ∧ quiet L Y w j ℓ ∧ Stanza Y.X j ℓ
noncomputable abbrev Zσ(X:Seats Fθ):= Hσ L Y X ∘ ViewS L Y
noncomputable abbrev Sig(q:Sender L):=fun x=>q (Vtone L Y (ViewS L Y x))
lemma ύT (X:Seats Fθ) : Continuous (Zσ L Y X):= (HσC _ _ X).comp (ViewS L Y).continuous
lemma MarkX (q:Sender L)(X:Seats Fθ)(hp:Funded L X q a k)(i:Phase): Continuous (fun x=> (Sig L Y q x).seq i.val):=by obtain ⟨f,hf,hF⟩:=hp.net; rw[hF]; exact (hf.spikes _).comp (ύT L Y X)
variable {L Y w}
variable (h:L.Rich s c e v u C)(ht:0<s)(hc:0≤c)(he:0<e)(hv:Scale Y t)(hw:‖w‖≤ t)
include h ht hc he hv
lemma ZBill (X:Seats Fθ)(hx:(X.card:ℝ)≤ z): Cane L! (fun x=>‖Zσ L Y X x‖) (hueCost (FWind G s c u C t) z G):= y_cost L Y (Crew h ht hc he hv X hx|>.normVal)
include hw
omit hw in lemma lust (i:ℕ):0 ≤Cσ G s c u C t i:=by
       have he':= ht; have hz:= h.vein.broad; have hh:0≤ flowerC G s u c C:=(bulk_F h ht hc he).pos; have heT:0 ≤ t:= (norm_nonneg _).trans hv.w; have hp:0≤ Soil G u s c C:=(h.PourA ht hc he Y.X).pos
       have hρ:0≤ Fξ G s c u C t:=by unfold Fξ crestPrice; positivity
       have hi:0 ≤ ampleP i:= le_trans zero_le_one (le_max_left ..); unfold Cσ; dsimp only; positivity
lemma PulseR (i:Drive L)(hk:Rebound L Y w ℓ i): Cane L! (TagK L Y i-TagK L (worldA L w) i) (oer u ℓ • Cσ G s c u C t):=by
        rcases i with i|i
        · rw [TagK,TagK, funext (azWorld L Y i), funext (azWorld L (worldA L w) i)]; change Cane _ ((fun _=>cash (JetB G L.c) Y.w i)-(fun _=>cash (JetB G L.c) w i)) _; rw [show cash (JetB G L.c) Y.w i=_ from (show cash (JetB G L.c) Y.w i=cash (JetB G L.c) w i from hk),sub_self]; exact Cane.nil _ fun i _=> mul_nonneg (Real.exp_nonneg _) (lust h ht hc he hv i)
        obtain ⟨i,rfl,hP,hx⟩:= hk; exact Relay h ht hc he hv hw _ hP hx
lemma Zclose (X:Seats Fθ)(hx:(X.card:ℝ)≤ z)(hq:∀ i:Rubric G X, Rebound L Y w ℓ (Sum.inr (shout G X i))) : Cane L! (fun x=> ‖Zσ L Y X x-Zσ L (worldA L w) X x‖) (oer u ℓ • hueCost (Cσ G s c u C t) z G):=by
         let f:=Zσ L Y X; let g:=Zσ L (worldA L w) X; let i:=oer u ℓ; let D:= hueCost (Cσ G s c u C t) z G
         have ht'(j:Rubric G X): Hue (f-g) j = TagK L Y (.inr (shout G X j))-TagK L (worldA L w) (.inr (shout G X j)):= by funext i; change castAt _ _ (f i-g i)= _; rw [_root_.map_sub,show castAt _ _ (f i)=_ from (show _ from HN L Y X j _),show castAt _ _ (g i)=_ from (show _ from HN L (worldA L w) X j _)];rfl
         have hZ: Cane L! (f-g) (hueCost (oer u ℓ • Cσ G s c u C t) z G):= by
               apply hueEarn _ _ (by rwa [Fintype.card_coe]) (fun i _=> mul_nonneg (Real.exp_nonneg _) (lust h ht hc he hv i)) ((show Continuous (f-g) from (ύT L Y X).sub (ύT L (worldA L w) X)).aestronglyMeasurable); intro j;rw [ht']; exact PulseR h ht hc he hv hw _ (hq j)
         apply hZ.normVal.grow; intro j _; unfold hueCost; simp only [Pi.smul_apply,smul_eq_mul]; exact le_of_eq (by ring)
end
end YM.OPE.Borealis.Galea
