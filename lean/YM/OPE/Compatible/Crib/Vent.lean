import YM.OPE.Compatible.Crib.Beret
/-! # stencil prescription adaptation.Axis-clock -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Crown
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type} {b i k r m:ℕ}{t C s u z ℓ B v ε:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph
open Spells
open Raucous Raucous.Host Votive Stationary -- verify
variable {K:Sponsor G}{T:Seasons K}
section
variable (L:Host K T) (S:Seats L.ForestQ)
abbrev Sender (L:Host K T):= AxisChart G L.ForestQ → Token
structure Funded (q:Sender L)(C:ℝ)(k:ℕ):Prop where
       net : ∃ f:Libra.Keys G (S:Type)→Token, RubricT f C k ∧ q=f ∘ rip L.Z L.H G S
variable {q:Sender L}
lemma Funq {p:Scoop G b→ℝ}(o:Site L.f)(h:Velvet p C k): Funded L (crux L.Z L.H o b) (fun x=> Autum p (ath L.Z L.H o x)) (Ufee G b k C) (Xs k):=by
         refine ⟨_,Safe L.Z L.H o h, funext fun x=>?_⟩; change Autum _ _ = Autum _ _; unfold Autum; rw [gam,offX]
lemma Funded.norm (h:Funded L S q C k)(x:AxisChart G L.ForestQ)(hx:‖x‖≤ t): scope (q x) (C*(1+t)^k):=by
         obtain ⟨_,hr,hf⟩:=h.net; rw [hf]; exact hr.earn ((norm_nonneg _).trans hx) _ ((veil ..).trans hx)
lemma Funded.strong (h:Funded L S q C k)(i:Phase):Continuous (fun x=>(q x).seq i.val):=by obtain ⟨_,hh,h⟩:= h.net; rw [h]; exact (hh.spikes _).comp (rip L.Z L.H G S).continuous
end
section
variable {I:Type*}{V:I→ℝ}{l:Filter I}{w F:I→ℝ}
open Cinders
lemma largeM (b:I→ℕ)(h:RateLE l V (fun i=>(b i:ℝ)) 0)(G:Gauge)(he:Tendsto V l atTop):RateLE l V (fun i=> LargeK G (b i)) 0:=by
        have hx(x:ℝ):=RateLE.const x he; have hP: RateLE l V (fun i=> RoadK (b i)) 0:= ((((hx 2).mul ((hx 4).mul h)|>.mono (by norm_num)).add (hx 2) he).add (hx 1) he); have hp(j:ℕ): RateLE l V (fun i=> Mā G j (b i) 0) 0 := (((hx _).mul (hP.pow j he)).mul (hx _)).mono (by simp); exact ((((hx _).add ((((hp 1).add (hp 2) he|>.add (hp 3) he).mul (hx _)).mono (by norm_num)) he).mul (hx _)).mono (by norm_num))
lemma segue (b:I→ℕ)(h:RateLE l V (fun i=>(b i:ℝ)) 0)(G:Gauge)(he:Tendsto V l atTop)(hp:RateLE l V w 0)(k:ℕ):RateLE l V (fun i=> Ufee G (b i) k (w i)) 0:=by
        have hx:=largeM b h G he; have hv(x:ℝ):=RateLE.const x he; exact (((hv _).mul (hp.mul (((hv _).mul hx).pow k he))).mul (hx.pow 3 he)).mono (by norm_num)
lemma krant (b:I→ℕ)(G:Gauge)(he:Tendsto V l atTop)(h:RateLE l V (fun i=>(b i:ℝ)) 0)(hp:RateLE l V w 0)(hy:RateLE l V F 0): RateLE l V (fun i=> FeintG G (b i) (w i) (F i)) 0:=by
        have hx(x:ℝ):=RateLE.const x he; have hP: RateLE l V (fun i=> RoadK (b i)) 0:= ((((hx 2).mul ((hx 4).mul h)|>.mono (by norm_num)).add (hx 2) he).add (hx 1) he); have hh(j:ℕ): RateLE l V (fun i=> Mā G j (b i) (w i)) 0:= (((hx _).mul (hP.pow j he)).mul (((hx 1).add hp he).pow j he)).mono (by simp); have ht:RateLE l V (fun i=> RedG G (b i) (w i)) 0:= (hx 1).add (((hh 1).add (hh 2) he).add (hh 3) he) he; exact ((hy.mul (hh 4)).mono (by norm_num)).add ((((hx _).mul hy).mul (((hx _).mul ht).pow 3 he)).mono (by norm_num)) he
end
end YM.OPE.Crown
