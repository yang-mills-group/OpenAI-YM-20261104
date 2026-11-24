import YM.OPE.Compatible.Kash.Sump
import YM.OPE.Compatible.Glim.Xpand
/-! # Uniform supplies of finite-angular scripts. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Page
variable {i j d k m r l:ℕ}{Z I J:Type}
variable {n:Side}{x t:ℝ}
local notation "C!"=> Curtain (Shade G)
local notation "Φ" n:arg=>Bid.Dir G n
structure UnitL (c:ℝ)(p:Status G)(k m:ℕ):Prop where
       holds:∃ X:Curtain (Shade G), Volume X k m c ∧∀ᶠ n in atTop,column G X k n=p n
variable {p q:Status G}{c v:ℝ}
namespace UnitL
lemma taller(h:UnitL c p k m)(hx:c ≤ v)(he:k ≤ i): UnitL v p i m:=by obtain ⟨x,hx',hq⟩:=h.holds; refine ⟨x,Volume.raise x hx' he hx,hq.mono (fun n hn=>?_)⟩; rw [← hn]; exact funext fun j=>funext fun z=>(Volume.wax x hx' i he (spool _ _ z)).symm
lemma color (t:ℝ)(hp:UnitL c p k m): UnitL (‖t‖*c) (t • p) k m:=by obtain ⟨p',hp,h⟩:=hp.holds; refine ⟨t • p',Volume.spread _ _ hp,h.mono (fun i hi=> ?_)⟩; exact (funext fun x=>funext fun b=> flairCost ..).trans (show t • column _ p' _ _= _ from congr_arg (t • ·) hi)
lemma credits (h:UnitL c p k m):0 ≤ c:=by obtain ⟨p,hp,h⟩:=h.holds; exact Sack.coins (hp.2 0)
lemma sumZ (V:I→ℝ)(P:I→Status G)(s:Finset I)(h:∀ i∈s,UnitL (V i) (P i) k m): UnitL (∑ i∈s,V i) (∑ i∈s,P i) k m:=by
       choose! X hv hx using fun i hi=>(h i hi).holds; refine ⟨∑ i∈s,X i,Volume.sum _ _ _ hv,?_⟩; filter_upwards [eventually_all_finset s |>.2 hx] with n hn; funext x y; rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_apply]; unfold column; rw [flairS _ _ _ _ (fun i hi=> (hv i hi).bound _)]; exact sum_congr rfl (fun i hi=>congr_fun (congr_fun (hn i hi) _) _)
lemma added (h:UnitL c p k m)(hv:UnitL v q k m):UnitL (c+v) (p+q) k m:=by
     obtain ⟨r,hp,h₁⟩:=h.holds; obtain ⟨s,hq,h₂⟩:=hv.holds; refine ⟨r+s,Volume.add _ hp hq,?_⟩; rw [show column G _ _=column G r k+column G s k from funext fun j=>funext fun x=>funext fun t=> flairA _ _ _ (hp.bound r) (hq.bound s)]; filter_upwards [h₁,h₂] with n hn hz; exact congr_arg₂ (·+·) hn hz
lemma up (h:Take (fun _:Unit=>v) (fun _=>p) k m):∃ c,0 ≤ c∧UnitL (c*v) p k m:=by obtain ⟨c,hc,H⟩:=h.available; exact ⟨c,hc,⟨H ()⟩⟩
lemma blaze_zero:UnitL 0 (0:Status G) k m:=by obtain ⟨c,hc,H⟩:= (Take.zero (k:=k) (m:=m) (G:=G) (0:Unit→ℝ)).available; obtain ⟨s,h,hV⟩:=H (); exact ⟨s,(by simpa only [Pi.zero_apply,mul_zero] using h),hV⟩
lemma congrZ (h:UnitL c p k m)(hx:∀ᶠ n:Side in atTop,p n=q n):UnitL c q k m:=by obtain ⟨p',hp,hQ⟩:=h.holds; exact ⟨p',hp,(hQ.and hx).mono (fun i hi=>hi.1.trans hi.2)⟩
lemma kilo (P:Script (Shade G) i)(h:soot m P c):UnitL c (fun n x p=>Flume.Script.value x P (spool G n p)) i m:= ⟨_, givenHammer _ _ h le_rfl, Eventually.of_forall (fun _=> funext fun _=>funext fun _=>throw_flair _ le_rfl _ _)⟩
lemma product {f g:Status G}(h:UnitL c f k m)(ht:UnitL v g d m): UnitL (((k:ℝ)+1)*((d:ℝ)+1)*c*v) (f*g) (k+d) m:=by
    obtain ⟨p,hP,h₁⟩:=h.holds; obtain ⟨r,hR,h₂⟩:=ht.holds; let t:Finset ℕ:=range (k+1); let s':Finset ℕ:=range (d+1)
    let F(i j:ℕ):= Shell.throw (Bake (p i) (r j)); let W:= ∑ i∈t,∑ j∈s', F i j; let b:ℕ→ℕ→ℝ:=fun _ _ => c*v
    have hp(i j)(he:i∈t)(h:j∈s'): Volume (F i j) (k+d) m (b i j):= by unfold F b; refine givenHammer _ _ (BakePair (p i) (r j) _ _ (hP.2 _) (hR.2 _)) (Nat.add_le_add (Nat.le_of_lt_succ (mem_range.mp he)) (Nat.le_of_lt_succ (mem_range.mp h)))
    let U(i):=∑ j∈s',F i j; have hU(i)(hi:i∈t): Volume (U i) (k+d) m (∑ j∈s',b i j):=Volume.sum _ _ _ (fun j hj=> hp i j hi hj)
    refine ⟨W,Volume.raise W (Volume.sum _ _ _ hU) le_rfl ?_,?_⟩; · apply le_of_eq; simp [t,s',b]; ring
    filter_upwards [h₁,h₂] with n hn hn'; funext x w; let yX:=spool G n w; rw [show (f*g) n x w= column G p k n x w* column G r d n x w from congr_arg₂ (·*·) (congr_fun (congr_fun hn.symm _) _) (congr_fun (congr_fun hn'.symm _) _)]; change Flair (∑ i∈t,U i) (k+d) yX x= (∑ i∈t,Flume.Script.value x (p i) yX)*(∑ j∈s',Flume.Script.value x (r j) yX)
    rw [flairS _ yX x U (fun i h=> (hU i h).bound _),sum_mul]; apply sum_congr rfl; intro i hi; unfold U; rw [flairS (k+d) yX x _ (fun j hj=> (hp i j hi hj).bound _),mul_sum]; apply sum_congr rfl; intro j hj; unfold F; rw [throw_flair _ (Nat.add_le_add (Nat.le_of_lt_succ (mem_range.mp hi)) (Nat.le_of_lt_succ (mem_range.mp hj))), BakeReading (p i) (r j) _ _ (hP.2 i) (hR.2 j)]
end UnitL
end YM.OPE.Variance
