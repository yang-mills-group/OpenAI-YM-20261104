import YM.OPE.Compatible.Limn.Ore
/-! # Sage patch book keeping -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Limn
open Function Filter Set MeasureTheory Lattice Laurent RG Matrix Precision Exterior Tree Push Push.AbsoluteSums Wilson Woody
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge}{c f:Side}
open Next.SectorChange Next.SectorChange.Schur PertExtension Series Libra GaussianScore Flume Flume.Page Flume.Script Flume.Virgin Zeph
open AnalyticNext.QuarticMatch Radius Estimate Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom AnalyticNext.QuarticMatch.Local
open Cascade Rill Votive Stationary Progress.StationaryScenes Work.F03 Next.Free Work.F05 Glass Coin Pilot Next.Foundations Work.F08 FreeResolvent
open PhysicalNext.Repeat.Aroma
variable {r R B b ε X:ℝ}{m:ℕ}
variable (S:StepData c f)(H:Odd S.ratio.count.val)
open Finset Module
open Green (wt)
local notation "F"=> forest S.ratio H
local notation "Wκ"=> Wings G c
local notation "Q"=> (Bid.Dir G c × AxisChart G F)
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u:ℝ}
variable (A:Alps K T i v)(U:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g:Bid.Dir G c→ AxisChart G (forest S.ratio H)}(k:S.Choices)
variable (V:FibreRep S H U k A g b)(h:licensed S H U A.clip A.live L A.sky g)
local notation "Σ!"=>pane F k A.clip A.live
local notation "Q!"=>Key F G
include h
abbrev sleeve (G:Gauge)(R t:ℝ):=max (farm G (t/2/2)) (creep G (t/2/2)) * (R*Premium.overall (t/2))
abbrev flowerC (G:Gauge)(s t R B:ℝ):=(farm G (t/2)*B)* sleeve G R s
lemma RegularM {p:Site f→(Bid.Dir G c ×AxisChart G (forest S.ratio H))→ℝ} (ht:0<r)(hR:0≤R)(he:0<ε)(hx:Dew.Pile S F ε R r m Σ! p)(hm:2 ≤ m)(Z:VaultC G r R U.C.gap u X):
         Pours (LiftM S H A k U) (pointK S F) (cotW S) (u/2) (flowerC G r u R X):=by
               let f:=FUND S H U; obtain ⟨_,_,hh⟩:= spend S H U A.clip A.live k h (Embedding.refl _) Z ht hR he hx hm; have hW: Pours (f⁻¹) (pointK S F) (pointK S F) (u/2) (farm G (u/2)*X):=by
                    apply tillS S F Z.warmth Z.broad.le; intro i j; simpa using! hh i j
               have hy:= (hW.fuse ((trim_c S H A k _ ht hR he hx hm).weaker ((half_le_self Z.warmth.le).trans Z.charge) le_rfl) (half_pos Z.warmth).le).scale (-1); rwa[abs_neg,abs_one,one_mul,neg_one_smul] at hy
omit h
open Radial
noncomputable abbrev onset (I:Seats F)(x:AxisChart G F)(w:Bid.Dir G c) := ChartUp S F I V.L.Q (V.L.M w-x)
include h in
lemma spiceJ (j:ℕ)(hj:0<j) (x:Q): jet V.L.f j x=jet Σ! j x:=by
    unfold jet; rw[(V.meter.iteratedFDeriv ℝ j).eq_of_nhds]; -- expression
    have hz:ContDiffAt ℝ (j:WithTop ℕ∞) Σ! 0:=(viewer k h.2.1).origin.of_le le_top; let f:Q→ℝ:=fun _=> Σ! 0; rw [show (fun x:Q=>pane F k A.clip A.live x-pane F k A.clip A.live 0)=Σ! -f from rfl,iteratedFDeriv_sub_apply hz (show ContDiffAt ℝ (j:WithTop ℕ∞) f 0 from contDiffAt_const)]; have hh:iteratedFDeriv ℝ j f 0=0:=by unfold f; rw[iteratedFDeriv_const_of_ne (Nat.ne_of_gt hj)];rfl
    rw [hh,sub_zero]
noncomputable abbrev PatchM (I:Seats F):= bit I V.L.Q
include h in
lemma WarpedQ (w:Bid.Dir G c)(x: AxisChart G F): -- not omit
              jet Σ! 2 (w,V.L.M w+x)=jet Σ! 2 (w,V.L.M w)+V.L.Q.P x x/2:=by rw [← spiceJ S H A U k V h _ (by norm_num),← spiceJ S H A U k V h _ (by norm_num) (w,V.L.M w)]; exact V.L.split ..
end YM.OPE.Limn
