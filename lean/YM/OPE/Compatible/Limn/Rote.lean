import YM.OPE.Compatible.Limn.Ord
/-! # Full gap and principal inverses currency -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Limn
open Function Filter Set MeasureTheory Lattice Laurent RG Matrix Precision Exterior Tree Push Push.AbsoluteSums Wilson Woody
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge}{c f:Side}{X:Type}
open Next.SectorChange Next.SectorChange.Schur PertExtension Series Libra GaussianScore Flume Flume.Page Flume.Script Flume.Virgin Zeph
open AnalyticNext.QuarticMatch Radius Estimate Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom AnalyticNext.QuarticMatch.Local
open Cascade Rill Votive Stationary Progress.StationaryScenes Work.F03 Next.Free Work.F05 Glass Coin Pilot Next.Foundations Work.F08 FreeResolvent
variable {t r R B b u C ε:ℝ}{m:ℕ}
variable (S:StepData c f)(H:Odd S.ratio.count.val)(U: Boxes G S.patch S.kernel)
local notation "Fλ"=> Woody.forest S.ratio H
local notation "AK"=> Active G (forest S.ratio H)
open Green (wt)
open Finset
lemma soleGap : Gapped (FUND S H U) U.C.gap:=by
       let D:= U.g; let X:= forge S.patch S.kernel G D; let T:=pink S.kernel.penalty D; let Z:=squad S.ratio H G; have he: FUND S H U=(X.acts c).submatrix Z Z:= hedge_acts T ((heart_saves _ S.kernel.penalty_pos U.hi (fun i:Train U.t=>i)).1.whole _) S H (G:=G); rw [he,AnalyticBridge.LocalGaussianLaws.gapped_iff]; exact (U.C.deep U.g c).submatrix Z Z.injective
variable (P:Clip)(W:PathData G){L:Matrix (Body 1 f) (Body 1 c) ℝ}{M:Bed}
variable {g: Bid.Dir G c→AxisChart G (Woody.forest S.ratio H)} (k:S.Choices)(h: licensed S H U P W L M g)
section price
lemma palmPos (G:Gauge)(ht:0 ≤ R)(t:ℝ): 0 ≤ limbC G t R:=by unfold limbC farm; exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (Premium.cover_ge _)))) (mul_nonneg ht (zero_le_one.trans (Premium.cover_ge _)))
structure VaultC (G:Gauge)(r b u:ℝ)(t C:ℝ):Prop where
     warmth : t>0
     broad : C > 0
     charge : t ≤ r/2/2
     voice {V:Type} [Fintype V][DecidableEq V]{c:Side}(a:V→Site c)(A:Matrix V V ℝ) : Pours A a a (r/2/2) (limbC G r b) → Gapped A u→ A.IsSymm → ∀ i j,wt t (a i) (a j)*|A⁻¹ i j| ≤ C
lemma purchased (G:Gauge)(h:0<u)(hp:0<r)(hb:0≤b):∃ t C:ℝ,VaultC G r b u t C:=by
       obtain ⟨t,C,hT,ht,hC,H⟩:=inverse_tilt h (palmPos G hb r) (half_pos (half_pos hp)); exact ⟨t,C,hT,hC,ht,fun a V h h' hs i j=> H a V h h' hs j i⟩
-- uniform *patch* choice uses all pre settings.U.C.gap
include h
lemma spend {s b c' t:ℝ}{p:Site f→(Bid.Dir G c ×AxisChart G (forest S.ratio H))→ℝ} [Fintype X][DecidableEq X](e:X↪ Key Fλ G)(Z:VaultC G s b U.C.gap t C)
 (ht:0<s)(hR:0≤b)(he:0<c')(hx:Dew.Pile S (Woody.forest S.ratio H) c' b s m (pane Fλ k P W) p)(hm:2 ≤ m) :
    Pours ((FUND S H U).submatrix e e) (pointK S Fλ ∘ e) (pointK S Fλ ∘ e) t (limbC G s b) ∧ Gapped ((FUND S H U).submatrix e e) U.C.gap ∧∀ i j,wt t (pointK S Fλ (e i)) (pointK S Fλ (e j))*|((FUND S H U).submatrix e e)⁻¹ i j| ≤ C:=by
          have hh:= sculpt e (Palm S H U P W k h ht hR he hx hm); have hE:= spired e (soleGap S H U); exact ⟨hh.weaker Z.charge le_rfl,hE,Z.voice _ _ hh hE (Matrix.isHermitian_iff_isSymm.mp ((ulk_force S H U).isHermitian.submatrix _))⟩
end price
end YM.OPE.Limn
