import YM.OPE.Compatible.Soup.Droll
/-!
# Epoch growth. Limited trajectory tape. variance observables without spectral cost loss
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.OPE.Owl.HillZ
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG Gauge Precision
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ENNReal ContDiff
open Eyrie Push Push.AbsoluteSums Push.Mark Cascade Flume Flume.Page Flume.Script Pilot Finset
open Silt Libra Coin Rill Silt.Float Votive PertExtension Series GaussianScore Radial Next.Foundations
open Merchant Merchant.Aloof Merchant.Sleeve Merchant.SiteL
open Next.Free Next.Scheduling Stroke Spells Lass Lass.Zest Pill CardinalQ
variable {I:Type}{φ:Filter I}{G:Gauge} {K:Sponsor G}{T:Seasons K}
variable {β:I→ℝ}{n:I→Side}{S:Stage}{i j d r k:ℕ}{τ s a B:ℝ}
variable {A:∀ x:I,HillZ (T:=T) S i r d τ (β x) (n x)}{U: Scaffold φ (Counters β) n (Mnd i S A) r}
variable (D:I→ Law (Merchant.Chamber G r))(hs:G.Simple)
open Merchant.SiteL
variable (h:Tendsto β φ atTop) (A U)
open Source Labels Metric Cinders
-- P φ(T.actual), no projection.Curving witness.P leads Γ.
noncomputable abbrev Xτ (j:I):=(A j).art
noncomputable abbrev Recα (j:I):= (A j).cost (A j).art
noncomputable abbrev ScoreX (j:I):= Torch.caged (Xτ A j) (A j|>.living)
noncomputable abbrev νsize (j:I):= (A j).living.B
noncomputable abbrev feeτ (j:I):= Torch.πcost (Xτ A j) (A j|>.living)
noncomputable abbrev δS (j:I):= clove ((frames G).level d) (A j|>.living.c) (Xτ A j)*Ξoff (Meta A j)
noncomputable abbrev hNu (j:I):2*((A j).living.B+1)<(n j).val:= Torch.γage (A j|>.living)
noncomputable abbrev signalF (j:I)(x:Config G (n j)):= (Recα A j).exponentialEntry 0 (localSection G d) (Stru A j) x
noncomputable abbrev ωZ (j:I):=(Recα A j).density 0 (localSection G d) (Stru A j)
lemma fish (j:I):GaugeInvariant (ωZ A j):=Push.Local.Kernel.insertion_gauge (sound G d) (A j).gen.lawful ((A j).living.kM.pet _).form (SectorMeasure.Presented.lawful_gi (A j).gen.lawful) -- import available
lemma AuthCap (j:I): Acceptance 0 (Meta A j) (d+6+6) (ScoreX A j) ((A j).living.B) (feeτ A j):= Torch.accepted ..
lemma stars_y (j:I)(c:Config G (n j))(hp:flags (Barrier A j) c=∅): ‖signalF A j c-ScoreX A j c‖≤ δS A j := ((A j).living.taxes _).2 c (by unfold Healthy; rw [show (A j).path.p.threshold=Barrier A j from rfl,hp]; simp)
lemma φ_s (j:I)(U:Config G (n j))(hp:flags (Barrier A j) U=∅): ωZ A j U= (Real.exp (PriceΩ A j U))* signalF A j U:=by
        let X:= Recα A j; let P:= Stru A j; have hZ(s:Finset ℕ):X.marked P s U=0:=by
             unfold Coefficient.marked; split_ifs with hz
             · have he : s=∅:=by
                                                                   by_contra h; obtain ⟨i,hi⟩:= Finset.nonempty_iff_ne_empty.mpr h; let L:=(P.activities.forced i).inventory; obtain ⟨x,hx⟩:= (P.activities.forced i).inventory_ne; exact Finset.notMem_empty x (by rw[← hp,show Barrier A j=P.p.threshold from rfl,← hz.2]; exact Finset.mem_biUnion.mpr ⟨i,hi,hx⟩)
               simp only [he, Finset.sum_empty]
             rfl
        change (↑(P.eval U) :ℂ)*_+_* (∑' s,X.marked P s U)= _; rw[Rep.eval,P.activities.gas_one P.p hp,mul_one]; simp_rw[hZ,tsum_zero,mul_zero,add_zero];rfl
include h
lemma Xfees : Receipt β φ (Xτ A):= (YM.OPE.Score.steady (2:ℝ) (carth h)).under (Eventually.of_forall fun i=>(A i).norm)
lemma LEDΛ : Wax β φ (δS A) Deb:= (torν i S A h).meritV (Xτ A) (Xfees A h)
lemma ηSal : Receipt β φ (feeτ A):= (torν i S A h).skies (Xτ A) (Xfees A h)
lemma νGrow : Receipt β φ (fun j:I=>(νsize A j:ℝ)):= (torν i S A h).flour
set_option quotPrecheck false
lemma healthyMint :∃ c:I→ℝ,Receipt β φ c∧∀ᶠ i in φ,∀ U:Config G (n i),‖ωZ A i U‖≤ Real.exp (PriceΩ A i U)*(c i):=by
        let Y:= (frames G).level d; let H:= torν i S A h; let B:=Xfees A h; let v(i):=(A i).living.c*Y.coeffSize (Y.core (Xτ A i)); let a(i):= (1+(A i).living.a)*Y.coeffSize (Xτ A i); let W:= carth h; have he:=H.cθ (Xτ A) B; have hx:Receipt β φ v:=he; have hz:Receipt β φ a:= ((YM.OPE.Score.steady _ W).plus H.vote W).product (H.FrY (Xτ A) B); refine ⟨_,(hz.plus hx W).plus hx W,?_⟩; filter_upwards [(H.dusk.tends (by norm_num) W).eventually (ge_mem_nhds zero_lt_one), (βmoment h (-1)|>.tends (by norm_num) W).eventually (ge_mem_nhds zero_lt_one),H.tithe] with i hi hv hP U; have hp':Pet 0 (localSection G d) (Recα A i) (A i|>.living.a) (salary (β i)) (v i) (H:=hol G) (R:=Stru A i):= (A i).living.kM.pet _; apply Penn U (A i|>.gen.lawful) (localSection G d) (o:=0) hv hp'.cap hi
        have hh:= YM.MergeProof.Accent.hull (localSection G d) (Stru A i) 0 (Recα A i) U hp'.columns hp'.cap hi hP; rw [show (Recα A i).x=Xτ A i from (A i).living.kM.mark _] at hh; exact hh
end YM.OPE.Owl.HillZ
