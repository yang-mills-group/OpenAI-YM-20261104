import YM.AllOrder.Floe.Fost
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge}{ι:Type}[Nonempty ι]{a b C D Z Λ ε σ Ω:ℝ}{k r m n N l:ℕ}{j:Side}
local notation "e"=> Step.rank k
local notation "I"=> Fin (k+4)
local notation "X"=> tape (k+2)
local notation "P"=> tape (rank k)
variable (p:Clip)(R:PathData G)(h:R.Bounds p σ C Z)(g:G.Simple) (H:Scene G)(A Q:Layout G)(α: Fin (k+4)→ℝ) -- all beams selected
variable (he:Legal (tape (k+2)) A)(hq:∀ i∈ tape (k+2),Q i=A i){t t': Coin} (hl:light t') (hs:Station (rank k) j (ask p R H t (tape (k+2)) A))
    (hQ: Pace.Valid H N) (hN: rank k ≤ N)
    (hr:∀ i<Step.rank k,t i=t' i)(ht: t' (Step.rank k)=t (Step.rank k)+α 0)
local notation "L"=> entry k
variable (hF:∀ i:Fin (k+4),Beam (tape (k+2)) A p R H t (entry k i|>.e) ((entry k i).r) (Q (entry k i)) (α i))
local notation "T"=> ask p R H t X A
local notation "V"=> T e j
local notation "Y"=> Link G j
-- general Station below k all periods property. hs all n or use Etiquette steady at j, need Pose from hS all n. `votes` needs all but Stained just Etiq.P.L. adjust.Country
include hs hF hQ hN g h he
lemma impetus (i:I) :jet (V- α 0 • (Pace.base p R 0 j)) (i.val+2)=jet (turnSeries (Q (L i)) (m:=j)) (i.val+2) := by
 let f:= L i; let d:=f.r; have hp(f:Age)(u:ℝ):Plausible (u • (Pace.base p R 0 j)):= ((base_pose p R h g|>.rank 0 le_rfl j).scal u |>.read)
 have hx : Pace.Valid T N := (Valid.void.sub hQ).sub (glories t _ X p R h he g)
 have hT (i:I): jet (V -α i • (Pace.base p R 0 j)) (i.val+2)=jet (turnSeries (m:=j) (Q (L i))) (i.val+2):= hF i|>.pens j
 by_cases hi:i.val=0; · have hc: i=0:= Fin.ext hi; rw [hc,hT]
 have he : 2 < f.r:= by change 2< i.val+2; omega
 rw [← hT i]; have h0(q:ℝ):jet (q • (Pace.base p R 0 j)) (i.val+2) = 0:= breakR ((base_pose p R h g|>.rank 0 le_rfl j).scal q) he; rw [jet_minus (show Plausible V from (hx.rank e hN j).read) (hp f (α 0)), jet_minus (hx.rank _ hN _|>.read) (hp f (α i)),h0,h0]
include hq hl hr ht
lemma readout : Station (e+1) j (ask p R H t' P Q):= by
 let F' :Y→ℝ:= V-α 0 • (Pace.base p R 0 j);
 intro n hn; rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hn) with hc|rfl; swap -- n notation rfl likely i+≥.
 · let hx:Pace.Valid T N:= (Valid.void.sub hQ).sub (glories t _ X p R h he g); have hv:= hx.rank e hN j; let A₀:= base_pose (N:=N) p R h g; have hu: Rank Y (e+2) F':= hv.sub ((A₀.rank 0 (Nat.zero_le _) j|>.scal (α 0)).up (by omega)); have hz: iteratedFDeriv ℝ 1 F' 0=0:= by
        let u x:= ((hx e hN j).2.paints x); let w x := ((A₀ 0 (Nat.zero_le _) j).2.paints x); have hF':Stained G F':=fun x=> Eventually.of_forall fun t=> by unfold F'; exact congr_arg₂ (fun u v=>u- α 0*v) (u x t) (w x t)
        exact Haiku.Project.still_one g hF' (hu.read.smooth.contDiffAt.analyticAt)
   let f(i:Age) := jet (turnSeries (Q i) (m:=j)) i.r;
   have h₁(v:Y) : (∑ i∈ upto k, f i) v=∑ i:I, jet F' (i.val+2) v:=by
        rw [upto,Finset.sum_image, Finset.sum_apply]; swap
        · intro x hx y hy hxy; exact Fin.ext (congr_arg Age.slots hxy)
        apply Finset.sum_congr rfl; intro i _; exact (congr_fun (impetus p R h g H A Q α he hs hQ hN hF i) v).symm -- args
   have hf(v:Y):jet F' 1 v=0:= by unfold jet; rw [hz]; simp
   intro i s; have hh(x :Y):(ask p R H t' P Q e) j x= F' 0:= by
        rw [painted k p R A Q hq hr hl j H, show t' e-t e=α 0 by rw [ht]; ring]; change F' x-(∑ i ∈ upto k,f i) x= _; rw [h₁]; have hv:=Ink.Pointwise.full_span x hu; rw [sum_range_succ',sum_range_succ',← Fin.sum_univ_eq_sum_range,hf, jet_zero,add_zero] at hv; linarith only [hv]
   exact Eq.trans (hh i) (hh s).symm
 unfold ask; rw [Pi.sub_apply, ← shades k p R A Q hq hr hc]; exact hs n hc
end YM.AllOrder.Floe.Step
