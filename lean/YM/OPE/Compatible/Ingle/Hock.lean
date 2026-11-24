import YM.OPE.Compatible.Ingle.Stave
import YM.OPE.Compatible.Sward.Lucent
/-!
# Build fixed-height real analytic×smooth LP mark extraction. Uniform Scrape.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}{C:KernelChoices}
open Finset
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin Module
open Labels Source Source.Drops
variable {d:ℕ}{X:Labels.Frame G d}(T:SectionData X)(P:Pad G) (C:KernelChoices)(H:Hol G)
-- capture record with coordinates independently chosen quantities (cofinal domain separation built in).
structure Asp (T:SectionData X) (H:Hol G)(k:ℕ) where
      N :Side
      W:Site N
      Φ:Rep G N
      clipw:ℝ
      b:ℕ
      l:10*b<N.val
      tight: 2*(4*b+1)<N.val
      guard : k+6 ≤ Φ.p.order
      Wide : Widen Φ.p b
      (a B c :ℝ)
      xraw : Coefficient X N
      I : Finset ℕ
      h : Pet W T xraw a c B (H:=H) (R:=Φ)
      he : Shoo W T xraw b I
namespace Asp
variable (oF : Asp T H k)
include oF
lemma boarded : 2*(oF.b+1)<oF.N.val:=by have ht:=oF.tight; omega
abbrev boxval : Coefficient X oF.N:=oF.xraw
noncomputable def fArt:= GroveV oF.W T oF.xraw oF.I oF.Φ
abbrev costS := oF.a * X.coeffSize (oF.xraw.x) + oF.B
lemma lemmaH : Acceptance oF.W oF.Φ.p (k+6) (fArt T H oF) oF.b (costS T H oF):= Coal oF.W T oF.xraw oF.h oF.he oF.guard oF.Wide
variable (A:ℂ→L[ℝ]ℝ)(V:Train r)(hv:4 ≤ r)
noncomputable def Orx:= OrionV oF.W P (oF.boarded ..) oF.Φ.p (fArt T H oF) A C V hv oF.clipw (lemmaH T H oF)
noncomputable abbrev MeshP (m:ℕ): bed G (k+6) m :=ArK oF.W T A (boarded T H oF) oF.Wide oF.clipw C V hv oF.xraw oF.he oF.h oF.guard P m
lemma GuardM (m:ℕ): ‖MeshP T P C H oF A V hv m‖ ≤ billP (k+6) oF.b m (Orx T P C H oF A V hv):= dosh (Recon oF.W P (boarded T H oF) oF.Φ.p (fArt T H oF) A C V hv oF.clipw (lemmaH T H oF))
end Asp
section toll
variable {Junk:Type}
variable {H T C} {β:Junk→ℝ}{l:Filter Junk}{R:Junk→ Asp T H k}{V:Junk→ Train r}{u:ℝ}
structure Salary (_χ:Tendsto β l atTop) (W:Junk→ Asp T H k):Prop where
      Htu:TuneUp β l (fun i=>(W i).Φ.p) (fun i=>(W i).clipw)
      hR:Receipt β l (fun i=> ((W i).b:ℝ))
      charge: Receipt β l (fun i=> Asp.costS T H (W i))
namespace Salary
variable {χ:Tendsto β l atTop} (K:KernelChoices) (W:Junk→Asp T H k) (h:Salary χ W) (A:ℂ→L[ℝ]ℝ)(z:Junk→Train r)(hz:4 ≤ r)
include h
lemma sector : Receipt β l (fun i=> billP (k+6) (W i).b m (Asp.Orx T P K H (W i) A (z i) hz)):=by
      let v(i):= Asp.Orx T P K H (W i) A (z i) hz; apply OrbitPay h.Htu h.hR v _ _ _ le_rfl; intro j hj; let Q:= varn h.Htu G K z hz (n:=fun i=>(W i).N) (- (1/2)) (k+6) h.hR; apply Score.pointwise (Q.product (receiptK h.Htu G P A h.hR h.charge (k+6))) _ (Eventually.of_forall fun i=> norm_nonneg _); exact Eventually.of_forall fun i=> clothV (W i).W P (Asp.boarded ..) (W i).Φ.p (Asp.fArt T H (W i)) A K (z i) hz _ (Asp.lemmaH T H (W i)) j hj
lemma strikesFee : Receipt β l (fun i=>Asp.MeshP T P K H (W i) A (z i) hz m):= Score.under (sector P K W h A z hz (m:=m)) (Eventually.of_forall fun _=> Asp.GuardM ..)
lemma ζF (W':Snap G d)(t m:ℕ)(hv:d ≤ m): Wax β l (fun i=> ζSig W' (W i|>.clipw) (W i|>.Φ.p) t m hv) 0:=by
       let F(i):=θh (W i|>.clipw) (W i|>.Φ.p); have hg:Wax β l (fun i=>(F i)⁻¹) 0:=(by simpa only[neg_zero] using! (CalmP h.Htu|>.inv.pays (carth χ))); unfold ζSig; apply RateLE.sum (f:=fun i j=> _) (carth χ); intro i hi; have he: Wax β l (fun j=> θFoil W' (W j|>.clipw) (W j|>.Φ.p) t m i.val (show i.val ≤ m from by omega)) 0:=by
            unfold θFoil; apply RateLE.sum (carth χ); intro B hB; simpa only [mul_zero,add_zero] using! (RateLE.smul (RateLE.pow B.length hg (carth χ)) (RateLE.const (θShelf W' B t m (by omega)) (carth χ)))
       exact (RateLE.smul (RateLE.const _ (carth χ)) he).mono (by norm_num)
lemma Watch (W':Snap G d)(η:Junk→ℝ) (he:Wax β l η (-1))(hT:T.Sound H)(hp:d<k+6)(ht:d ≤ m)(hR:∀ᶠ i in l,∀ x∈ Hoard G (4*(W i).b) (k+6) m,
       ‖boostS (rentV G (z i) hz K (W i|>.N)) (1/2) m (k+6) x-boostS (atlasF G (z i) hz K) (1/2) m (k+6) x‖ ≤ η i*‖x‖):
       Tendsto (fun i=>‖ A (OpticZ (X:=X) (W i|>.xraw.x) W')-ζSig W' (W i|>.clipw) (W i|>.Φ.p) (k+6) m ht (boostS (atlasF G (z i) hz K) (1/2) m (k+6) (Asp.MeshP T P K H (W i) A (z i) hz m).val)‖) l (𝓝 0):=by
             choose U v hu hx using fun i:Fin (d+1)=> RayV H W' i.val
             let g (j:Fin (d+1))(i):= U j*(1+((W i|>.b):ℝ))^(v j); have hg(j):Receipt β l (g j):= (Score.steady _ (carth χ)).product (((Score.steady (1:ℝ) (carth χ)).plus h.hR (carth χ)).power _ (carth χ)); have hv:= tankρ h.Htu P A d (fun i=>(W i).b) _ g hg (nubby (v:=fun i=>(W i).N) h.Htu.Clock G K z hz h.hR) h.charge h.hR; have hy:= (ζF W h W' (k+6) m ht|>.norm).mul (he.mul ((waitG χ (strikesFee P K W h A z hz (m:=m))).norm)); have hq:= (hv.zero χ).add ((hy.tends (by norm_num) (carth χ))); rw [add_zero] at hq; refine squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) ?_ hq
             filter_upwards [hR,h.Htu.opens] with i hi he; let F:=W i; exact Perc F.W T F.xraw W' A F.he F.h hT F.l (Asp.boarded ..) F.tight F.guard F.Wide P F.clipw he (fun j=>g j i) (fun j=>hx j F.b F.Φ.p.threshold F.Φ.p.threshold_pos F.Φ.p.threshold_le) K (z i) hz hp ht hi
end Salary
end toll
end YM.OPE.Spells
