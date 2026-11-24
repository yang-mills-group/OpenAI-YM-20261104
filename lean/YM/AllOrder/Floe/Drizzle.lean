import YM.AllOrder.Floe.Post
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge} {c f n : Side} {k j w N : ℕ} {S:StepData c f}
variable {σ C Z D β Θ:ℝ}
open Pace
namespace Aero
variable {ι:Type} {Γ f' s:ι→ℝ} {F:ι→Ink.Money.Bills (Coarse G)} {Δ ζ:ℝ} {δ:ι→ Coin} {l:ℕ}
-- admissible projection width from before, one rank.Motion Param.
def Sparkle (G:Gauge)(a u:ℝ)(k r:ℕ) := ∀ (ι:Type) (x:ι→ ℕ→Atom G r) (Γ ζ : ι→ℝ) (l:ℕ), CreditF Γ l ζ → (∀ i,Extra.Iteration.Charged (x i) a (ζ i)) → money Γ (fun i n=> turnSeries (m:=n) (x i)) k l u
lemma sparkle (G:Gauge)(a:ℝ)(ha:0<a)(k r:ℕ): ∃ b, 0<b ∧ ∀ u,0<u → u ≤ b → Sparkle G a u k r:= by
 obtain ⟨u,M,ht,h,hU⟩:=orbit_cost G r k ha; refine ⟨u,ht,fun s hx hs ι x Γ ζ l hz he=> ?_⟩; choose W hW hX using fun i=>hU (x i) (ζ i) (he i); exact money.squeeze (show money Γ (fun i n=> turnSeries (m:=n) (x i)) k l u from ⟨W,_,hz.mul (freeC _ h),fun n i=>hX i n,hW⟩) hs hx le_rfl
-- lease rank for down path supplied clip.bounds pre-L standing Stage data. money profiles for *each query* independent post order t. Covers whole.Le.
def Slanted (G:Gauge)(p:Clip) (a C u:ℝ)(k:ℕ) : Prop:= ∀ (ι:Type)(x:ι→PathData G) (Γ ζ :ι→ℝ) (l:ℕ), CreditF Γ l ζ → (∀ i,(x i).Bounds p a C (ζ i)) → ∀ j:ℕ, money Γ (fun i=>Pace.base p (x i) j) k l u ∧ money Γ (fun i=> clerk (fun _=>Precision.loop (x i)) 0 j) k l u
lemma vane_cut (hx:money Γ F k l σ) (he:mental F) (hs:0<σ) (j:ℕ): money Γ (fun i n=>jet (F i n) j) k l σ:= by
 by_cases h:k+1=j; subst j; apply money.adapt hx; intro i n; exact (Haiku.Project.self _ (he i n|>.contDiffAt) _).symm
 exact money.void (fun i n=> Haiku.Project.other _ (Ne.symm h)) hs
set_option maxHeartbeats 200000 in
lemma angles (G:Gauge) (p:Clip)(a C:ℝ)(ha:0<a)(hC:0≤C)(k:ℕ):∃ b,0<b ∧ ∀ u,0<u→u≤b→Slanted G p a C u k:= by
 obtain ⟨t,T,h,h0,ht⟩:= column_price G k C p.direct ha p.quadratic_pos.le; obtain ⟨v,hv,h1⟩:= sparkle G a ha k 2; obtain ⟨q,hq,h2⟩:= sparkle G a ha k 3; obtain ⟨z,hz,h3⟩:= sparkle G a ha k 4
 let b:= min (min t v) (min q z); refine ⟨b,lt_min (lt_min h hv) (lt_min hq hz),fun u hu hD ι x Γ ζ l hζ hx j=> ?_⟩
 choose p₀ hp hP using fun i=> (ht p (x i) _ _ _ le_rfl (hx i) ((hx i).rows)).2; have h₀ : money Γ (fun i n=> inputSeries p (x i) (m:=n)) k l u:= money.squeeze (show money Γ (fun i n=>inputSeries p (x i) (m:=n)) k 0 t from ⟨p₀,(fun _=>T),freeC _ h0,fun n i=>hP i n,hp⟩) (hD.trans ((min_le_left ..).trans (min_le_left ..))) hu (Nat.zero_le l)
 let F₁:= fun i=> (x i).loop; let F₂:= fun i=> (x i).cubic; let F₃:= fun i=> (x i).quartic; let f₀(i:ι) (n:Side):= inputSeries p (x i) (m:=n); let f₁ i (n:Side):=turnSeries (m:=n) (F₁ i); let f₂ i (n:Side):= turnSeries (m:=n) (F₂ i); let f₃ i (n:Side):=turnSeries (m:=n) (F₃ i)
 let hc:CreditF Γ l (fun _=>C):= (freeC _ hC).up (Nat.zero_le _); have hw:mental f₀:= fun i n=> (stain_knit _ _ (hx i)).analytic; have hx₁: mental f₁:= fun i n=> turns_analytic _ ha ((hx i).two); have hx₂:mental f₂:=fun i n=>turns_analytic _ ha ((hx i).three); have hx₃:mental f₃:=fun i n=>turns_analytic _ ha ((hx i).four);
 have hl₁:money Γ f₁ k l u:= h1 _ hu (hD.trans ((min_le_left ..).trans (min_le_right ..))) ι F₁ Γ _ l hζ fun i=> (hx i).two
 have hl₂:money Γ f₂ k l u:= h2 _ hu (hD.trans ((min_le_right ..).trans (min_le_left ..))) ι F₂ Γ _ l hc fun i=> (hx i).three
 have hl₃:money Γ f₃ k l u:= h3 _ hu (hD.trans ((min_le_right ..).trans (min_le_right ..))) ι F₃ Γ _ l hc fun i=> (hx i).four
 have hh:=money.zipper (U:=f₀+f₂) ((money.zipper h₀ hl₂ hw hx₂).1) hl₃ (fun i n=>(hw i n).add (hx₂ i n)) hx₃; refine ⟨money.adapt (vane_cut hh.1 (fun i n=> ((hw i n).add (hx₂ i n)).add (hx₃ i n)) hu (j+2)) ?_,vane_cut hl₁ hx₁ hu j⟩
 intro i n; rw [show Pace.base p (x i) j n= _ from (show Pace.base p (x i) j n=jet (intended p (x i) (m:=n)) (j+2) from rfl),intent]; rfl
-- prices of grouping q extra; q costs.ALL Ward prerequisite rank currents.Scope.Inhabit. choose when required; no extrapolated V-layer.
variable (t:Age)(i:Age)(V:ι→Layout G)(X:Finset Age)(v : Age→ℝ)
variable (hP:∀ i,Legal X (V i))(hx:∀ i∈X,0<v i)(ht:∀ i∈X,∃ f:ι→ℝ,CreditF Γ l f∧∀ j,Extra.Iteration.Charged (V j i) (v i) (f j)) (he:∀ j≤N,Pace.Cost Γ l (fun i=>δ i j))
include hP ht hx he
lemma apostles {a:ℝ}(h:0<a)(hs:∀ i∈X,Sparkle G (v i) a k (Age.r i))(hj:j≤N): money Γ (fun i=> Pace.glory (δ i) (V i) X j) k (l*N+l) a:= by
 let u (t i):= (V i t); let f (t i):= Pace.moiety (δ i) t (V i); let g (t i):= Haiku.Coat.trade t.e (u t i)
 have hv (t:Age)(hT:t∈X) : money Γ (fun i=>f t i j) k (l*N+l) a:= by
    let q i:= ladder (elapsed t) (δ i); obtain ⟨C,hC,H⟩:= ht t hT
    have hh : (fun i=> f t i j)=(fun i (n:Side)=> ∑ p∈range (j+1), q i p • g t i (j-p) n):= by funext i n; exact weighs _ _ _ _
    rw [hh]
    refine money.total (s:=Finset.range (j+1)) (F:=fun p i n=> q i p • g t i (j-p) n) ?_ ?_ h
    · intro p hp; have hz : Pace.Cost Γ (l*N) (fun i=> q i p):= Cost.up (Cost.transfer (j:=p) (fun t hj'=>he t (by have hh:=mem_range.mp hp; omega)) _) (Nat.mul_le_mul_left _ (by have hh:=mem_range.mp hp; omega))
      have hg: mental (fun i=>g t i (j-p)):= fun i n=> (trade_r _ _ _ t.pricey).read.smooth.contDiffAt.analyticAt
      by_cases h': t.e≤j-p; swap; · apply money.void _ h; intro i n; unfold g trade; rw [if_neg h']; simp
      apply money.scale (U:=fun i=>g t i (j-p)) _ hg hz h
      exact money.adapt (vane_cut (hs t hT ι (fun i=>V i t) Γ C l hC H) (fun i n=>turns_analytic _ (hx t hT) (H i)) h (j-p-t.e+t.r)) (fun i n=> by unfold g trade; rw [if_pos h'])
    intro p hp i n; exact ((Rank.scal (trade_r (S:=u t i) t.e (j-p) n t.pricey) (q i p)).read.smooth.contDiffAt.analyticAt)
 unfold glory; rw [show (fun (i:ι)=> (∑ t∈X,moiety (δ i) t (V i)) j)=(fun i (n:Side)=>∑ t∈X,Pace.moiety (δ i) t (V i) j n) from (by funext i n; simp [Finset.sum_apply])]; exact money.total X hv (fun t h i n=> ((moiety_pose (δ i) t (V i) X j (hP i) h).rank j le_rfl n).read.smooth.contDiffAt.analyticAt) h -- hv order
variable (p:Clip)(y:ι→PathData G)(hy:∀ v,(y v).Bounds p σ C (s v))(hv : CreditF Γ l s) (g:G.Simple)
include hv hy g
lemma bless {a:ℝ}(hs:Slanted G p σ C a k)(h:0<a)(hr:∀ i∈X,Sparkle G (v i) a k (Age.r i))(hj:j≤N): money Γ (fun i=> grouping (δ i) (V i) X p (y i) j) k (l*N+l+l) a:= by
 have hh j:= hs ι y Γ s l hv hy j; let f (i:ι):= Pace.base p (y i); let w (i:ι):= clerk (fun n:Side=> Precision.loop (y i) (n:=n)) 0; let r:= fun i=> Pace.factor (δ i) (f i); have hr₀(x:ℕ): mental (fun i=> f i x):= fun i n=> ((base_pose p (y i) (hy i) g).rank x le_rfl n).read.smooth.contDiffAt.analyticAt; have hw:mental (fun i=> w i j):= fun i n=> ((loop_pose p (y i) (hy i)).rank j le_rfl n).read.smooth.contDiffAt.analyticAt
 have ht': mental (fun i=> r i j):= fun i n=> (((base_pose p (y i) (hy i) g).proceed _).rank j le_rfl n).read.smooth.contDiffAt.analyticAt; let z(i):= glory (δ i) (V i) X; have hZ:mental (fun i=> z i j):= fun i n=> ((Valid.sum X (fun k hk=>moiety_pose (δ i) k (V i) X j (hP i) hk)).rank j le_rfl n).read.smooth.contDiffAt.analyticAt
 have hm : money Γ (fun i=> r i j) k (l+l) a := by
    rw [show (fun i=>r i j)= _ from (show (fun i=>r i j)=(fun i (n:Side)=>∑ k∈ range (j+1),δ i k • f i (j-k) n) from funext fun i=> funext fun n=> weighs _ _ _ _)]
    apply money.total _ _ _ h; · intro k hk; exact money.scale (L:=fun i=>δ i k) (hh (j-k)).1 (hr₀ _) (he k ((Nat.le_of_lt_succ (mem_range.mp hk)).trans hj)) h
    intro k hk i n; exact analyticAt_const.mul (hr₀ _ i n)
 refine (money.zipper (U:=fun i=>shiftB (δ i) p (y i) j) ?_ ((apostles V X v hP hx ht he h hr hj).squeeze le_rfl h (by omega)) (fun i n=>((hr₀ _ _ _).add (hw _ _)).add (ht' _ _)) hZ).1; exact (money.zipper (money.squeeze ((money.zipper ((hh j).1) (hh j|>.2) (hr₀ j) hw).1) le_rfl h (by omega)) (money.squeeze hm le_rfl h (by omega)) (fun i n=>(hr₀ j i n).add (hw i n)) ht').1
-- total argument
end Aero
end YM.AllOrder.Floe
