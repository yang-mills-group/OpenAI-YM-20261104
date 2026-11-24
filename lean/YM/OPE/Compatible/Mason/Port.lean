import YM.OPE.Compatible.Mason.Zeal
/-! # Bridge from true GP mark projection and physical pulse. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type}{i j k m:ℕ}{ε v t c:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown
variable {K:Sponsor G}{T:Seasons K}
section
variable {L:Host K T}
local notation "Fθ"=> L.ForestQ
local notation "Xθ"=> Bid.Dir G L.c
local notation "BDr"=> Fiber.drape Xθ (AxisChart G Fθ) L.F.L.M
-- instrument uses host. prepares anchor fine.
variable (hp:4 ≤ L.i)
abbrev Rpaper (p:Crown.Viewer L)(w:ℝ)(h: Viewer.Pledge p t (k+6)) {τ:Phase→ℕ}(S:Aware (k+6) τ):= ChiselV S (Recon p.x p.P p.hi p.U p.p p.Λ K.K L.A.gear hp w h.valid)
abbrev Vpass (L:Host K T) := (flats G L.f).toContinuousLinearMap ∘L (ribz L.Z L.H ∘L (Fiber.drape (Bid.Dir G L.c) (AxisChart G L.ForestQ) L.F.L.M).toContinuousLinearMap)
variable (p:Crown.Viewer L)(w:ℝ)(h: Viewer.Pledge p t (k+6)) {τ:Phase→ℕ}(S:Aware (k+6) τ)(A:Law (Bid.Dir G L.c))(μ:Measure (Bid.Dir G L.c))[μ.IsAddHaarMeasure](hA: Licence (Vpass L) (united A L.F.L.Q) L.A.gear K.K)
variable {N:ChartRatio G}(hN:LocalRatio N)
set_option quotPrecheck false
local notation "Rμφ"=> μ.prod (Chart.tangent G (Fθ).Free)
local notation "TΓ"=> Rpaper hp p w h S
local notation "Wℓ"=> L.F.L
local notation "XΘ"=> TracePay L.Z L.H L.U L.A L.k L.g N (k+6) (spread G (k+6) τ (Rpaper hp p w h S).val) L.b
noncomputable def scone (i:L.DirA) := RestD p.x p.P p.hi p.U p.p p.Λ K.K L.A.gear hp w h.valid (ath L.Z L.H p.x i.2)
include hA
lemma Thr_S : Weight (united A L.F.L.Q) (μ.prod (Chart.tangent G (forest L.Z.ratio L.H).Free)) k ((scone hp p w h) ∘ Fiber.drape (Bid.Dir G L.c) (AxisChart G L.ForestQ) L.F.L.M):=by
         let D:=Vpass L; let f:=RestD p.x p.P p.hi p.U p.p p.Λ K.K L.A.gear hp w h.valid; let g: L.DirA → Token:=fun i=> f (ath L.Z L.H p.x i.2); let q:=p.scoreV w; let Y:= ribz L.Z L.H (G:=G); let A':=united A (Wℓ).Q
         have hθ(i: L.DirA): f (Charu p.x D i)=(g ∘ BDr) i:=by apply congr_arg; rw [← climbsF]; change charW p.x ((flats G L.f).symm ((flats G L.f) _))= _; rw [ContinuousLinearEquiv.symm_apply_apply];rfl
         haveI : (μ.prod (Chart.tangent G (forest L.Z.ratio L.H).Free)).IsAddHaarMeasure:= Pilot.twoHaar (E:=Bid.Dir G L.c) (F:=AxisChart G (forest L.Z.ratio L.H)) μ (Chart.tangent G (forest L.Z.ratio L.H).Free)
         refine ⟨fun i=>?_⟩; have hx:= shineD p.x L.A.gear hp D (μ.prod (Chart.tangent G (forest L.Z.ratio L.H).Free)) A' K.K p.k hA p.P p.U w p.p p.Λ p.hi h.valid i
         have he : GuardB (μ.prod (Chart.tangent G (forest L.Z.ratio L.H).Free)) A' 0 (k+7-3*i.val) (fun y=> (f (Charu p.x D y)).seq i.val):= hx.skids (Nat.zero_le _) le_rfl
         exact (congr_arg (GuardB _ _ _ _) (funext fun y:L.DirA=> congr_arg (fun v:Token=>v.seq i.val) (hθ y))).mp he -- annotate
include hN

lemma Thrill (x:Site L.c)(hx:p.x=L.Z.ratio.embed x):
    Weight A μ k (GPY L (p.scoreV w) N - TracePay L.Z L.H L.U L.A L.k L.g N (k+6) (spread G (k+6) τ (Rpaper hp p w h S).val) L.b x L.F):=by
         let D:=Vpass L; let f:=RestD p.x p.P p.hi p.U p.p p.Λ K.K L.A.gear hp w h.valid; let g: L.DirA → Token:=fun i=> f (ath L.Z L.H p.x i.2); let q:=p.scoreV w; let T':= Drift.spread G (k+6) τ (TΓ).val; let z:= inkM T' (k+6) p.x; let Y:= ribz L.Z L.H (G:=G); let A':=united A (Wℓ).Q
         have hh: Weight A' (μ.prod (Chart.tangent G (forest L.Z.ratio L.H).Free)) k (g ∘ BDr):= Thr_S hp p w h A μ hA

         have hf (i: L.DirA): q i.2=((z ∘ Y)+g) i:= weds p.x p.P p.hi p.U p.p p.Λ K.K L.A.gear hp w h.valid S (letter L.Z L.H G i.2)
         have htZ: Status z:= fun j=> Stature.poly (InkG p.x (TΓ).val j|>.cost) 0
         have ht : Status ((z ∘ Y) ∘ BDr):= statusF (X:=L.DirA) (statusF htZ Y) (BDr).toContinuousLinearMap
         have hZ : XΘ x L.F=(Wℓ).predicts N (z ∘ Y):=congr_arg ((Wℓ).predicts N) (congr_arg (fun x:Site L.f=> inkM T' (k+6) x ∘ Y) hx.symm)
         have ht' : GPY L q N=(Wℓ).predicts N (z ∘ Y)+(Wℓ).predicts N g:=(congr_arg ((Wℓ).predicts N) (funext hf)).trans (SaltPeg _ _ _ _ ht (fun i=>(hh.color i).hW))
         let X:=(Wℓ).predicts N g; have he' : GPY L q N-XΘ x L.F=X:=by exact (congr_arg₂ (fun f g:Bid.Dir G L.c→Token=>f-g) ht' hZ).trans (add_sub_cancel_left _ _)
         exact (congr_arg (Weight A μ k) he').mpr (Weight.clutch A μ Wℓ N hN g hh) -- use Eq.mpr
end
-- manufacture Licence
variable (P:Flight i j)(Y:Alps K T i v)(D:Medal P.patch G K.K i)(hv:Mag i j)(he:Y.gear=P.wing)
include he
lemma Vauth (c f:Side)(hx:f.val=c.val*P.L.val)(b:ℝ):
     let S:=P.visit K.K hx; let U:=boxF P K hv D Y.gear; let H:= installed S.ratio (P.duo K.K.penalty).A0; let B:=Vessel K.K P.land G c hv.2.1
     ∀ V:Rep G f,∀ t:S.Choices,∀ g:Bid.Dir G c→AxisChart G (forest S.ratio P.odd), licensed S P.odd U Y.clip Y.live H Y.sky g → ∀ X:FibreRep S P.odd U t Y g b, Licence (Vpass (T:=T) (K:=K) ⟨_,_,S,P.odd,i,v,Y,U,b,V,H,g,t,X⟩) (united B X.L.Q) Y.gear K.K:=by
          intro S U H B V t g ht X; let L:Host K T:=⟨_,_,S,P.odd,i,v,Y,U,b,V,H,g,t,X⟩; let F:=chorus (climbs (Master S P.odd (P.duo K.K.penalty).A0) ∘L (flats G c).toContinuousLinearMap) (vertD S P.odd (G:=G)); have hX: Vpass L=F:=by apply ContinuousLinearMap.ext; rintro ⟨u,x⟩; exact uprush S P.odd _ g Y U t ht X u x -- tactic stuck TC
          rw [show Vpass _ =F from hX]; exact winter P hx K T hv b v Y he D g t ht X
end YM.OPE.Borealis
