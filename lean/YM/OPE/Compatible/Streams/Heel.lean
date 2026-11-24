import YM.OPE.Compatible.Streams.Hope
/-!
# Sap.EOM radical membership at launch.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}{R:Patch}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Alps Roles Planned.PrimaryIntegral295.Carrier Hark Quit.Jac
variable {u d s r l k m:ℕ}{W I E:Type}{τ:Phase→ℕ}
variable {K:Sponsor G}{S:Seasons K}{t:ℝ}(A: Alps K S s t)(hr:LocalRatio P)(hp:4 ≤ s)(hs:G.Simple)(hv:0 ≤ t)(R:Patch){n:Side}(x y:Site n)(H:Even n.val)
local notation "M!"=> CountL n R.L
local notation "Y!"=> solar G d τ
noncomputable def SailSap (a:Axis)(l:ℕ):Submodule ℝ (solar G d τ):= MainSap A hr hp hs hv R l ⊓ Submodule.comap (spose a G d τ).toLinearMap (MainSap A hr hp hs hv R l)
lemma fuel (p:Y!)(a:Axis)(h:p∈SailSap A hr hp hs hv R a l)(hy:Aware d τ): trellisA G hy p∈ SailSap A hr hp hs hv R a l :=by
      obtain ⟨hP,hQ⟩:= h; refine ⟨minor A hr hp hs hv R p hP hy,?_⟩; change spose a G d τ (trellisA G hy p) ∈ MainSap ..; rw [spinC hy]; exact minor A hr hp hs hv R _ hQ hy
local notation "μ"=> lapPrice (Patch.L R) l
noncomputable abbrev HillP (a:Axis)(i:Phase)(j:ℕ): Dice (solar G d τ):= rollD (spose a G d τ) (ContinuousLinearMap.id _ _) (BitA A hr hp hs hv R x y H i j)
include H in
lemma swapY (h': Pins K R x y):Pins K R y x:=by
      obtain ⟨v,hv,hq⟩:=h'; exact ⟨v,hv,fun i=>SettleQ (spikeS K R x i) (spikeS K R y i) (evenBoot K R H i) v (hq i)⟩
lemma quakeX (p:Y!)(a:Axis)(h:p∈SailSap A hr hp hs hv R a l)(h':Pins K R x y) (q:Y!) (i:Phase):
    let X:=HillP (d:=d) (τ:=τ) A hr hp hs hv R x y H a i; Thick (μ*(μ)) (fun j=> X j p q) ∧ Thick (μ*(μ)) (fun j=> X j q p) :=by
        intro X; let Z := spose a G d τ; have hz(n:Side)(x y:Site n)(H: Even n.val)(he:Pins K R x y)(i:Phase)(q:Y!): Thick (μ*(μ)) (fun j=>BitA A hr hp hs hv R x y H i j (Z p) q):= h.2 n x y H he i q
        refine ⟨hz n x y H h' i q,?_⟩; rw [show (fun j=>X j q p)=fun j=> BitA A hr hp hs hv R y x H i j p (Z q) from ?_]; exact h.1 n y x H (swapY R x y H h') i (Z q); funext j; rw [BitSeq]; exact (show BitA A hr hp hs hv R x y H i j (Z q) p= _ from (BitSeq ..|>.trans (congr_arg (fun u:Token=> u.seq i.val) (BoltCom (R:=P) (n:=CountL n R.L j) A (spikeS K R x j) (spikeS K R y j) _ hs hp (Z q) p))))
section
variable [Fintype I](e:RootEdge)(f:Libra.Keys G I→G.Color)(D:I→RootEdge)(a:Bool)(p:solar G d τ)
lemma sapSpend (hF:r≤d)(hΘ:∀ i,StencilTax d k ≤ τ i)(hm:l+l< k)(hA:ContDiffAt ℝ ω f 0) (he:∀ (i:Side)(x:Site i),Variance.Cand r (f∘dip D i x))(he':Holds p (fun n x=> Cake (sett n x e) a (Dune A) (Rh A) (f∘ dip D n x) r)):
   p ∈ MainSap A hr hp hs hv R l:=by
     rintro n x y H hx i q; rw [show (fun j:ℕ=>BitA A hr hp hs hv R x y H i j p q)=_ from (show _=(fun j:ℕ=>(WQ A hp hs x y H p q j (P:=P) (R:=R)).seq i.val) from funext fun _=> BitSeq ..)]; exact polyZ _ (EndFare R.L k) (GrowthP A hr hp hs hv x y H e f D a p hF hΘ hA (fun i=>he _ _) he' hx i q) (badge (e:=l) (d':=l) (Nat.lt_succ_self l) k hm)
lemma Hero (hF:r+1≤d)(hΘ:∀ i,StencilTax d k ≤ τ i)(hm:l+l< k) (hA: BudY e false r D f)(ht: Holds p (SongY A e r D f))(a:Axis): p ∈ SailSap A hr hp hs hv R a l:= by
      exact ⟨sapSpend A hr hp hs hv R e f D false p ((Nat.le_succ _).trans hF) hΘ hm hA.sm hA.tilt_i ht, sapSpend A hr hp hs hv R (angleZ a e) (f∘ Turned a D) (angleZ a ∘ D) (false.xor ((Wm a).flip e.2)) (spose a G d τ p) ((Nat.le_succ _).trans hF) hΘ hm ((((Turned a D).map_zero.symm ▸ hA.sm : ContDiffAt ℝ ω f (Turned a D 0)).comp 0 ((Turned a D).contDiff.contDiffAt))) (fun i x=> Candturned a _ _ x (hA.tilt_i i _)) (RotHeld a A D f e p hs hA ht) ⟩
end
end YM.OPE.Variance
