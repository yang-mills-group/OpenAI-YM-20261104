import YM.OPE.Compatible.Juniper.Sleep
/-!
# Polarity Ribbon
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}{K:KernelChoices}
open Finset
noncomputable def Packer (G:Gauge)(b:ℕ) : Scoop G (4*b)→L[ℝ] Scoop G b := (strideG G b).toContinuousLinearMap ∘L (socket b ∘L ((strideG G (4*b)).symm).toContinuousLinearMap)
noncomputable def Soul (p: Pole (Scoop G b) k):= p.compContinuousLinearMap fun _=>Packer G b
noncomputable abbrev ShapeX (p:Song (Scoop G b)):Curtain (Shade G):=fun j=>Honey (Soul (p j))
noncomputable abbrev budHue (p:Pole (Scoop G b) k):Prop:=∀ (x:Fin k→ Scoop G b)(u:G.El), p (fun i=>rotaryB G b u (x i))=p x
structure ReadyP (p:Song (Scoop G b))(d:ℕ):Prop where
       finance : p∈harmon (Scoop G b) d
       Hue : ∀ i:ℕ,budHue (p i)
lemma Fort (b:ℕ)(v: fieldX (Shade G)): Packer G b (Exposure (4*b) v)= strideG G b (liftP b v):=by
       change strideG G b (socket b ((strideG G _).symm (_))) = _ -- timeout
       rw [Exposure,ContinuousLinearEquiv.symm_apply_apply, homeB]
lemma Fort2 (b:ℕ)(v:fieldX G.ColorIndex):Packer G b (Exposure _ (mountain v))=0:=by
       rw [Fort]; have he : liftP b (mountain v)=0:= by rw[← homeB]; exact blown b v
       rw [he,map_zero]
lemma FortQ (b:ℕ)(v:fieldX (Shade G))(u:G.El): Packer G b (Exposure _ (plumeX u v))=rotaryB G b u (Packer G b (Exposure _ v)):=by
       rw [Fort,Fort,wharfB]; rw [rotaryB]; simp only [ContinuousLinearMap.comp_apply]; change strideG G b _= strideG G b (crevy u ((strideG G _).symm (strideG G _ _))); rw [ContinuousLinearEquiv.symm_apply_apply]
lemma upl_Cl (o: Site n)(p: Site n × G.ColorIndex → ℝ): upl o (cliff p)=mountain (upl o p):=by
       funext i; unfold upl cliff mountain; dsimp only; rw [map_add,wrap_step,← add_assoc]
lemma upl_Ct (o:Site n)(p:deck (Shade G) n)(u:G.El): upl o (hue u p)=plumeX u (upl o p):=rfl
lemma Pacing (p:Pole (Scoop G b) k): (Honey (Soul p)).abides:=by
       intro i n t w; rw [← timing,dropK]; unfold Soul; apply ContinuousMultilinearMap.map_coord_zero p i; change Packer G b (Exposure _ (upl _ (Function.update t i (cliff w) i)))=_; rw [update_self,upl_Cl,Fort2]
lemma TickY (p:Pole (Scoop G b) k)(hp:Sym p)(h:budHue p): (Honey (Soul p)).sorted ∧ (Honey (Soul p)).painted:=by
       refine ⟨HoneyT (v:=Soul p) (fun i s=> hp (fun j=>Packer G b (i j)) s),fun n x v=>?_⟩; rw[← timing,dropK,← timing,dropK]; let Y:= fun i=> Packer G b (Exposure (4*b) (upl (0:Site n) (x i))); change p _=p Y; refine Eq.trans (congr_arg p ?_) (h Y v); funext i; exact FortQ b (upl (0:Site n) (x i)) v -- upl hue defeq
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin
variable {τ:Phase→ℕ}
abbrev pulseBill (G:Gauge)(b:ℕ):= ((strideSize G).choose*(1+8*b))*((strideSize G).choose)
lemma pulse_nn (G:Gauge)(b:ℕ):0≤ pulseBill G b:=by unfold pulseBill; have he:= (strideSize G).choose_spec.1; have hp:=zero_lt_one.trans_le he; positivity
lemma PackEnt (G:Gauge)(b:ℕ):‖Packer G b‖≤ pulseBill G b:=by
       let p:= (strideG G b).toContinuousLinearMap; let u:=socket b (G:=G); let v:=((strideG G (4*b)).symm).toContinuousLinearMap; obtain ⟨h,H⟩:= (strideSize G).choose_spec; unfold pulseBill
       rw [mul_assoc]; exact (ContinuousLinearMap.opNorm_comp_le p (u ∘L v)).trans (mul_le_mul (H _|>.1) ((ContinuousLinearMap.opNorm_comp_le u v).trans (mul_le_mul (RootNorm _) (H _|>.2) (norm_nonneg _) (by positivity))) (norm_nonneg _) (zero_le_one.trans h))
lemma LampC (p:Pole (Scoop G b) k):‖Soul p‖≤ ‖p‖*pulseBill G b ^k:=by
       refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_; rw [prod_const, card_univ,Fintype.card_fin]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (PackEnt G b) _) (norm_nonneg _)
def billP (d b m:ℕ)(p:Song (Scoop G b)):=∑ i∈range (d+1),gumBill G (4*b) i m*(‖p i‖*pulseBill G b^i)
lemma TomX (m:ℕ)(d:ℕ)(p:Song (Scoop G b))(hp:ReadyP p d): Volume (ShapeX p) d m (billP d b m p):=by
      let z(i):=gumBill G (4*b) i m * (‖p i‖*pulseBill G b^i); have hz(i):0≤ gumBill G (4*b) i m:= by unfold gumBill; positivity
      have hv(i):0 ≤ z i:=mul_nonneg (hz _) (mul_nonneg (norm_nonneg _) (pow_nonneg (pulse_nn ..) _)); have ht(i)(h:i>d): ShapeX p i=0:=by funext t; unfold ShapeX Honey Soul; rw [(show _ from (show ∀ i:ℕ,i>d→p i=0 from hp.finance.1)) i h]; split <;> rfl
      refine ⟨ht,fun i=>?_⟩; by_cases he:i ≤ d
      · exact (crownG (Soul (p i)) m).tips (le_trans (b:=z i) (mul_le_mul_of_nonneg_left (LampC _) (hz i)) (Finset.single_le_sum (fun j _=>hv j) (mem_range.mpr (by omega))))
      rw [ht i (by omega)]; exact Sack.zero (Finset.sum_nonneg fun i _=>hv i) _
end YM.OPE.Spells
