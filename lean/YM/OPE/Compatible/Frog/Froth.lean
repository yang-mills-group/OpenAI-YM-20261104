import YM.OPE.Compatible.Frog.Lucid
/-!
# Marker pulse.Ward conditions on spheres and pure shifts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d m l k:ℕ}{K:Sponsor G}{T:Seasons K}{v b:ℝ}
open Module
variable {τ:Char.Phase→ℕ}
local notation "T!"=> Tower (Shade G) d τ
lemma epochFiber (q:Fin d):q.val≤d:=q.isLt.le
lemma wist (i:ℕ)(r:Page I i): Continuous fun x:Seat k m I=> lilies m k _ x i r := ((stairL m r)∘L (moduleAt m k i I)).continuous
-- Closure by Filters
lemma clBed (G:Gauge)(k m:ℕ) : IsClosed ((bed G k m:Set (Seat k m (Shade G)))):=by
     apply isClosed_iff_forall_filter.mpr; intro p f h hx hu; let x(i:Seat k m (Shade G))(r:ℕ):= lilies m k _ i r; have he : ∀ᶠ i in f,i∈bed G k m:=?_
     · have hg (r:ℕ)(n:Side)(p': Fin r → deck (Shade G) n): Tendsto (fun y=> scribe 0 (x y r) p') f (𝓝 (scribe 0 (x p r) p')):=by
            obtain ⟨C,hC⟩:= voicedCL (m:=m) (k:=k) 0 p'; rw [show (fun y=>scribe _ _ p')=C from funext (fun i=>(hC i).symm)]; rw [← hC]; exact Filter.Tendsto.mono_left (C.continuous.tendsto _) hu
       intro i; refine ⟨⟨_,(sproutV m k p).2 i⟩,fun h S y q=> tendsto_nhds_unique_of_eventuallyEq (hg i S _) (tendsto_const_nhds) (he.mono (fun z hz=> (merit hz i).1 h S y q)),fun n a y=>tendsto_nhds_unique_of_eventuallyEq (hg i n _) (hg i n _) (he.mono fun z hz=> (merit hz i).2.2 n a y),fun g=>?_⟩
       ext1 j; have hx (j:Page (Shade G) i):= (wist (k:=k) (m:=m) i j).tendsto p|>.mono_left hu; exact tendsto_nhds_unique_of_eventuallyEq (hx (j∘g)) (hx j) (he.mono fun z hz=>congr_fun ((merit hz i).2.1 g) j)
     exact Filter.le_principal_iff.mp hx -- check order
instance (G:Gauge)(k m:ℕ): CompleteSpace (bed G k m):= (clBed G k m).completeSpace_coe
lemma clSun (G:Gauge)(d:ℕ)(τ:Phase→ℕ): IsClosed ((solar G d τ) : Set (Tower (Shade G) d τ)):=by
     let X:=spread G d τ; apply isClosed_iff_forall_filter.mpr; intro p f h hx hu; have he:∀ᶠ i in f,i∈solar G d τ:=?_
     · refine ⟨fun i j g=>?_,fun n x=>?_⟩
       · ext1 v; let F(u:Tower (Shade G) d τ)(v):=spread G d τ u i j v; have ha(v):Tendsto (fun u=> F u v) f (𝓝 (F p v)):= ((show Continuous (fun u=> F u v) from (wist (k:=d+i.val) (m:=τ i) j v).comp (continuous_apply i)).tendsto p).mono_left hu; exact tendsto_nhds_unique_of_eventuallyEq (ha (v∘g)) (ha v) (he.mono (fun z hz=>congr_fun ((show Rainbow (X z) from hz.1) i j g) v))
       apply (pores (tor n) (meridian _ d 0 x _ (resin p (m:=0) (fun i=> Nat.zero_le _)))).mpr; intro a b s hr; let y:=Gael.ratioU a; let z:= Gael.ratioU b; have hY:Gael y:=Gael.walk _ hr.hX hr.gx; have hz: Gael z:= Gael.walk _ hr.hY hr.gy; have hh(i:Phase): (mine (fun t=> inkM (X p) d x (y t))).seq i.val=(mine (fun t=> inkM (X p) d x (z t))).seq i.val:=by
            refine tendsto_nhds_unique_of_eventuallyEq (((mortal (d:=d) (τ:=τ) x y hY i).tendsto p).mono_left hu) (((mortal (d:=d) (τ:=τ) x z hz i).tendsto p).mono_left hu) ?_; apply he.mono; intro k hk; have hp:(tor n).Marbles (inkM (X k) d x):=hk.2 n x; exact congr_arg (fun t:Token=> t.seq i.val) ((pores (tor n) hp.toll).1 hp hr)
       exact JetS.eta _ _ (hh 0) (hh 1) (hh 2)
     exact Filter.le_principal_iff.mp hx
instance (G:Gauge)(d:ℕ)(τ:Phase→ℕ):CompleteSpace (solar G d τ):=(clSun G d τ).completeSpace_coe
end YM.OPE.Drift
