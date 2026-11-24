import YM.OPE.Compatible.Stamen.Ride
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ} {H:Gauge}
open Cloud JetS
open scoped ContDiff
variable {v y:fieldX (Shade H)}
open Tensor WardBin
-- budget C estimate.O. Use masks of bad axes
open Cascade Terp Paver Rill Shell FreeResolvent Exterior MSbar.Tree MSbar.Tree.Resolvent Frequency Streamer
variable {N:Side}{L:KernelChoices} (x:Site N)
local notation "F!"=>Vec H N 1
open PertExtension Series GaussianScore
section
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (Z:E→L[ℝ] Vec H N 1)
variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure] (A:Law E)
variable (v:Train r)(h:4 ≤ r)(C:KernelChoices)
local notation "V"=> Prog C v H N
variable (a:Seat k m (Shade H))
local notation "P"=> Aγ v h C (m:=m) (N:=N) a
-- revision if proof macros h.S Panic
lemma fancy (d:ℕ)(ht:0 < m)(hn:n≤m)(hq:j+n+1 ≤ d)(hA:Licence Z A v C) (hp:a∈ empa H.ColorIndex k m) (he: Deep (m:=m) a d): Husk μ A j (fun i=> PenD (m:=m) (Aγ (N:=N) (m:=m) v h C a) (Charu x Z i) (mores (Charu x Z i) n)):=by
       let Q:= Aγ (N:=N) (m:=m) v h C a; let U:= Charu x Z; let g(i:Root (Shade H))(b:E):= mores (U b) n i; let f(i:Root (Shade H))(b:E):= Worth (m:=m) (Dragon i k m Q) (U b); have hU(i):Quiet (U i) 0:= park x Z _
       have htV:settled (m:=m) Q:= (writ (pointAt H v h C N) hp _).1; have hb(b:E):= prize (m:=m) (U b) (mores (U b) n) (hU b) Q htV (plumQ _ (hU b) n) hn
       let X(i):=f i*g i; have hx(i b): X i b=g i b*f i b:=mul_comm ..; refine limel μ A X ?_ (k:=k+n) ?_ _ (fun b=>?_) -- 
       · intro i; have heF: Husk μ A (d-1) (f i):=by
               unfold f Q Aγ; simp_rw [candleD a i _ _ hp.1]; apply AuroraV x Z μ A v h C (m:=m) (Dragon i k m a) ht hA (stoneD a i hp); apply dragDeep; rwa[Nat.sub_add_cancel (by omega:1≤d)]
         exact heF.laysL _ _ (show anthem n (g i) from vim x Z i) (by omega)
       · intro i; exact (ChartU x Z (m:=m) (Dragon i k m Q)).times (vim x Z _)
       simp_rw [hx]; exact hb _
lemma stormT (ht:4 ≤ m)(hA:Licence Z A v C)(hp:a∈empa H.ColorIndex k m)(he:Deep (m:=m) a (j+6)): Husk μ A j (fun i=>PenD2 (m:=m) (Aγ (N:=N) (m:=m) v h C a) (Charu x Z i) (mores (Charu x Z i) 2)):=by
       let Q:= Aγ (N:=N) (m:=m) v h C a; let U:=Charu x Z; let Xv:= Bunch (Shade H)
       let w(i:Xv) := ((fun b:E=>mores (U b) 2 i.1)*(fun b:E=>mores (U b) 2 i.2))
       have hw(i): anthem 4 (w i):=(vim (k:=2) x Z _).times (vim (k:=2) x Z _)
       let f(i:Xv)(b:E):= Worth (m:=m) (Dragon i.2 k m (Dragon i.1 k m Q)) (U b); let X(i:Xv):= f i*w i
       have hh(b:E):= prize2 (U b) _ (park x Z b) Q ((writ (pointAt H v h C N) hp (-(1/2))).1) (plumQ (U b) (park x Z b) 2) ht -- fix param
       refine limel μ A (I:=Xv) X ?_ (k:=k+4) ?_ _ (fun i=>?_)
       · intro i; let p':= Dragon i.1 k m a; have hp': Dragon i.1 k m a∈ empa H.ColorIndex k m:= stoneD a i.1 hp; have hz: Husk μ A (j+4) (f i):=by
                        unfold f Q Aγ; simp_rw [candleD a i.1 _ _ hp.1,candleD (Dragon i.1 k m a) i.2 _ _ hp'.1]; exact AuroraV x Z μ A v h C _ (by omega) hA (stoneD _ _ hp') (dragDeep _ _ (dragDeep _ _ he))
         exact hz.laysL _ _ (hw i) le_rfl
       · exact fun i=> (ChartU x Z (m:=m) (Dragon i.2 k m (Dragon i.1 k m Q))).times (hw i)
       rw [show (fun v=> X v i)= fun v:Xv=> w v i*f v i from funext fun v=>mul_comm ..]; exact hh _
end
end YM.OPE.Silt.Phere
