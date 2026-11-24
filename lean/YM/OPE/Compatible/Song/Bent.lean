import YM.OPE.Compatible.Song.Host
/-!
# Lift of shifted projection and Field law. Probe.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL
variable {i j d k m r l b:ℕ}{n:Side}{V:ℝ}
variable {I W:Type} {B:I→ Finset (Edge Cover)}{N:I→ Side}{φ:Filter I}{Z:I→ℝ}
variable {M:I→ℕ}
-- shadow casts(em) charge Tower.F.Measure
noncomputable abbrev ofCourse (p:GlyphQ G N)(q:ℕ): Forge G N:=fun i=>Pawn.mold (p i) q
noncomputable def Torque (e:Edge Cover)(u:G.ColorIndex)(p:Forge G N):Forge G N:= fun i=> Topper (sett _ 0 e) (Phone G u) false (p i)
noncomputable def Flan (e:Edge Cover) (A T: GlyphQ G N)(f:CrysP N G)(r:ℕ):Forge G N:=fun i=> Cake (sett (N i) 0 e) false (A i) (T i) (f i) r
local notation "B!"=>fun i:I=>bark (M i)
variable (A:Audience φ Z N M r)
namespace PlaneQ
include A
lemma phi (p:Forge G N)(e:↥(fieldP r))(u:G.ColorIndex)(hv:∀ v:G.ColorIndex,PlaneQ (B!) φ Z (loft N e.val v p) k): PlaneQ (B!) φ Z (Torque e.val u p) k:=by
       let f(j:G.ColorIndex):Forge G N:= fun i=>Mount (sett (N i) 0 e.val) (Phone G u) false j
       have he(j:G.ColorIndex):PlaneQ (B!) φ Z (f j) 0:=hold_stamp A ..; rw [show Torque e.val u p=∑ j,f j* loft N e.val j p from funext fun i=> by rw[Finset.sum_apply]; rfl]
       refine totals A.fair _ _ fun j _=>?_ ; simpa only [Nat.zero_add] using PlaneQ.prod A.fair (he j) (hv j)
lemma quasar (P T:GlyphQ G N)(L:I→Law (Chamber G r))(hS:Shroud A P T L)(p:CrysP N G)(k:ℕ)(j:↥(fieldP r))(h:ShineX A p k j): PlaneQ (B!) φ Z (Flan j.val P T p k) (k+1)∧ Divining φ (Flan j.val P T p k):=by
       have hR: Divining φ (Flan j.val P T p k):=⟨(hS.calm.and h.march).mono fun _ hi=> crestV hi.2.1 hi.1.1 hi.1.2.1 hi.1.2.2 hi.2.2⟩; refine ⟨?_,hR⟩
       let W:=(B!); let U:=billcoat P T; let B₀:= (Phone G); let K(j:G.ColorIndex):GlyphQ G N:=fun i=> B₀.coord j ∘ p i; have hK(u):∀ᶠ i in φ,ContDiffAt ℝ ω (K u i) 0:=h.march.mono fun i hi=> (B₀.coord u).toContinuousLinearMap.contDiff.contDiffAt.comp _ hi.1.smooth
       let X(v:G.ColorIndex):=ofCourse (K v) k; let z(v):= Torque j.val v (X v); let y(v):=Torque j.val v U; have hz(v:G.ColorIndex):PlaneQ W φ Z (z v) k:= PlaneQ.phi A _ j v fun a=> roof A j (K v) a k (h.cost v) (hK v); have hy(v):PlaneQ W φ Z (y v) 1:=PlaneQ.phi A _ j v (hS.ink j)
       have ht: Flan j.val P T p k = ∑ i, (y i * X i-z i):=by funext i; rw [Finset.sum_apply]; rfl -- Flan may need unfold
       rw [ht]; refine PlaneQ.totals A.fair _ _ fun i _=> PlaneQ.shiftz A.fair ((PlaneQ.prod A.fair (hy _) (h.cost i)).pit (by omega)) ((hz _).pit (Nat.le_succ _))
end PlaneQ
end YM.OPE.Merchant
