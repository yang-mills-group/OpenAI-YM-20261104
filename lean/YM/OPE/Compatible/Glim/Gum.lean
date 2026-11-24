import YM.OPE.Compatible.Glim.Draco
/-! # EOM budget representatives -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r l:ℕ}{Z I J M:Type}{n:Side}(e:RootEdge)(b:Bool)
-- need eventual only for examples earlier.Coherence
variable {K:Sponsor G}{T:Seasons K}{V:M→ℝ}(A:(j:M)→Alps K T i (V j)){τ:Phase→ℕ}
local notation "µ"=> Tested.germ
abbrev mind (P:Tower (Shade G) k τ):foliage G:= fun _ x=> inkM (spread G k τ P) k x
lemma goose (P:Tower (Shade G) k τ)(h:∀ᶠ n in atTop,∀ x:Site n,(tor n).Marbles (mind P n x)): Pathic k (spread G k τ P):=by
   obtain ⟨t,ht⟩:=eventually_atTop.mp h; intro n x; let m:= n*t; have hp:t≤m:= Nat.le_mul_of_pos_left _ n.pos; let u:=wrap m (lift x); have hT:= ht m hp u; let hz:n.val ∣ m.val:=dvd_mul_right ..; let Y:= mind P n x; let T:= Booklet hz G; let P':=mind P m u; have hv:Y=P'∘T:=funext fun i=>Eq.symm ((labRel hz u i _ _).trans (congrArg (fun y=>mind P _ y i) ((lease hz _).trans (wrap_lift x)))) -- define
   change (tor n).Marbles Y; rw [hv]; refine ⟨fun i=>(hT.toll i).compLinear T.toLinearMap,fun {a b s} h=>?_⟩; apply (hT.honors (brink hz h)).congr' _ Filter.EventuallyEq.rfl; filter_upwards with i; simp only [Function.comp_apply,map_smul];rfl
lemma Shine {q:M→ℝ}{A:M→ Status G}(h:Take q A k m):∃ c:ℝ, 0≤c ∧∀ i,∃ x: Seat k m (Shade G), ‖x‖ ≤ c*q i∧(∀ j,(lilies m k _ x j).sorted)∧∀ᶠ n:Side in atTop,column G (lilies m k _ x) k n=A i n:=by
     obtain ⟨c,hc,H⟩:=h.available; refine ⟨c,hc,fun i=>?_⟩; obtain ⟨p,hp,h⟩:= H i; let f:= Paver.bow p; have hv:Volume f k m (c*q i):= beagle p hp; let x:= fundus f _ hv; refine ⟨x,sproutsU f hv,?_,?_⟩; · intro j;rw [show lilies _ _ _ x=f from sproutsX f hv]; exact stir (p j)
     rw [show lilies _ _ _ x=f from sproutsX f hv]; apply h.mono; intro n hx;rw [← hx]; funext y v; exact Finset.sum_congr rfl (fun j _=> scoring _ (sootS (hp.2 j)) _ _)
lemma Brunt {q:M→ℝ}(hq:0≤q){P:M→ foliage G}(hp:∀ j:Phase,Shut q P k (τ j)) (h:∀ i,∀ᶠ n in atTop,∀ x:Site n,(tor n).Marbles (P i n x)):∃ c:ℝ,0 ≤ c∧∀ i,∃ p:solar G k τ,‖p‖ ≤ c*q i∧∀ᶠ n:Side in atTop,mind p.val n=P i n :=by
      choose c hc H using fun j=> Shine (hp j j); refine ⟨∑ i,c i,sum_nonneg (fun i _=>hc i),fun i=>?_⟩; choose v hv hV h₁ using fun j=> H j i; let p:=v; have he:∀ᶠ n:Side in atTop,mind p n=P i n :=by
           filter_upwards [eventually_all.mpr h₁] with n hn; funext x y; have hh(j:Phase): (mind p _ x y).seq j.val=(P i n x y).seq j.val:=by unfold mind; rw [vein_i]; exact congr_fun (congr_fun (hn j) _) _
           exact JetS.eta _ _ (hh 0) (hh 1) (hh 2)
      have hp': p∈ solar G k τ := ⟨fun i j=> hV i j, goose p (by filter_upwards [he,h i] with n hn hp ;rw [hn];exact hp)⟩
      exact ⟨⟨p,hp'⟩,(pi_norm_le_iff_of_nonneg (mul_nonneg (sum_nonneg (fun i _=>hc i)) (show 0≤q i from hq i))).mpr fun j=> (hv j).trans (mul_le_mul_of_nonneg_right (single_le_sum (fun i _=>hc i) (mem_univ _)) (hq i)),he⟩
-- family record
variable [Fintype I]
-- specify Cand for all n: finite-stencil Rank even if chosen via Haar
structure BudY (k:ℕ)(m:I→RootEdge)(f:Libra.Keys G I→G.Color):Prop where
     sm : ContDiffAt ℝ ω f 0
     tilt_i(n:Side)(x:Site n): Variance.Cand k (f∘ dip m n x)
     clock(n:Side)(x:Site n): rooted (sett n x e) b (tor n) (f ∘ dip m n x)
noncomputable abbrev School (j:M)(m:I→RootEdge)(f:Libra.Keys G I→G.Color)(r:ℕ): foliage G:=fun n x=>Cake (sett n x e) b (Dune (A j)) (Rh (A j)) (f∘ dip m n x) r
abbrev Holds {τ:Phase→ℕ}(p:solar G k τ)(Y:foliage G):Prop:= ∀ᶠ n in atTop, mind p.val n= Y n
lemma globuleY (m:I→RootEdge)(f:Libra.Keys G I→G.Color)(h:BudY e b r m f)(hp:r+1≤ k){P:Clip}(hv:∀ i,(A i).clip=P)(hx:0 ≤ V)(hs:G.Simple):
    ∃ c:ℝ,0 ≤ c∧∀ i,∃ p:solar G k τ, ‖p‖ ≤ c* ZTheta V i ∧ Holds p (School e b A i m f r):=by
       have hV(j:Phase): Shut (ZTheta V) (fun i=> School e b A i m f r) k (τ j):= Shut.taller (sponsorCake e b A m f h.sm hx hv r) le_rfl hp
       apply Brunt (le_trans zero_le_one (le_add_of_nonneg_right hx):0 ≤ ZTheta V) hV; intro i; filter_upwards with n x; exact crestV (h.tilt_i n x) (DuneAt (A i) hs) (DuneKind (A i)) (RhythmKind _) (h.clock n x)
end YM.OPE.Variance
