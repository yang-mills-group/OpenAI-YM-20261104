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
abbrev Status (G:Gauge):=(n:Side)→ Site n→ Bid.Dir G n→ℝ
noncomputable abbrev column (G:Gauge)(v:Curtain (Shade G))(k:ℕ):Status G:=fun n x y=> Flair v k (spool G n y) x
structure Take (t:Z→ℝ)(v:Z→ Status G)(k m:ℕ):Prop where
    available : ∃ c:ℝ,0 ≤ c∧∀ i,∃ p:Curtain (Shade G), Volume p k m (c*t i) ∧∀ᶠ n in atTop,column G p k n=v i n
variable {q y:Z→ℝ} {f g:Z→ Status G}
lemma Take.congr (h:Take q f k m)(he:∀ i, ∀ᶠ n in atTop,f i n=g i n): Take q g k m:=by obtain ⟨c,hc,H⟩:=h.available; exact ⟨_,hc,fun i=> (H i).imp fun _ hp=>⟨hp.1,(hp.2.and (he i)).mono fun _ hh=> hh.1.trans hh.2⟩⟩ -- need outer ∃
lemma Take.raise (h:Take q f k m)(hz:q ≤ y)(ht:k≤ d): Take y f d m:=by
    obtain ⟨c,hc,H⟩:= h.available; refine ⟨c,hc,fun i=>?_⟩; obtain ⟨p,hp,h⟩:= H i; exact ⟨p, Volume.raise p hp ht (mul_le_mul_of_nonneg_left (hz i) hc), by rw [show column G p d=column G p k from funext fun j=> funext fun i=>funext fun z=> (Volume.wax p hp d ht (spool _ _ z)).symm]; exact h⟩
lemma Take.scale (h:Take q f k m)(v:ℝ): Take q (v • f) k m:=by
     obtain ⟨c,hc,H⟩:=h.available; refine ⟨‖v‖*c,mul_nonneg (norm_nonneg _) hc,fun i=>?_⟩; obtain ⟨p,hp,h⟩:=H i; refine ⟨v•p,?_,?_⟩; rw [mul_assoc]; exact Volume.spread _ _ hp; rw [show column G _ _=v • column G p k from funext fun n=> funext fun x=> funext fun i'=> flairCost ..]; filter_upwards [h] with n hn; exact congr_arg ((v:ℝ) • ·) hn
lemma Take.add (h:Take q f k m)(ht:Take q g k m): Take q (f+g) k m:=by
      obtain ⟨c,hc,H⟩:=h.available; obtain ⟨v,hv,V⟩:=ht.available; refine ⟨_,add_nonneg hc hv,fun i=>?_⟩; obtain ⟨p,hp,h₁⟩:=H i; obtain ⟨r,hr,h₂⟩:= V i; refine ⟨p+r,?_,?_⟩; rw [add_mul]; exact Volume.add _ hp hr; rw [show column G _ _=column G p k+column G r k from funext fun j=>funext fun x=>funext fun t=> flairA _ _ _ (hp.bound p) (hr.bound r)]; filter_upwards [h₁,h₂] with n hn hz; exact congr_arg₂ (·+·) hn hz
lemma Take.zero (q:Z→ℝ): Take q (fun _=>(0:Status G)) k m:=by
      refine ⟨0,le_rfl, fun i=>⟨0, ⟨fun _ _=>rfl,fun k=>?_⟩,Eventually.of_forall (fun i=> funext fun x=>funext fun j=> flair0 ..)⟩⟩; exact Sack.zero (by rw [zero_mul]) _
lemma Take.Sum (s:Finset I)(f:I→ Z→ Status G)(h:∀ i∈s,Take q (f i) k m): Take q (∑ i∈s,f i) k m:=by induction s using Finset.induction_on with
     |  empty=> rw[sum_empty]; exact Take.zero _
     | insert i s hi ih=> rw [sum_insert hi]; exact Take.add (h i (mem_insert_self ..)) (ih (fun i hi=> h _ (mem_insert_of_mem hi)))
-- multiplication
lemma givenHammer (X: Script (Shade G) i)(t:ℝ)(h:soot m X t)(he:i≤ k): Volume (Shell.throw X) k m t :=by
    refine ⟨fun j hv=> hubbub (by omega),fun j=>?_⟩; by_cases hp:j=i; subst j;rw [show Shell.throw X i=X from Pi.single_eq_same ..]; exact h;rw [hubbub hp]; exact Sack.zero (Sack.coins h) _
lemma Take.bead (P: Z→ Script (Shade G) i)(c:ℝ)(hc:0≤c)(h:∀ z,soot m (P z) (c*q z)): Take q (fun z n x p=>Flume.Script.value x (P z) (spool G n p)) i m:= ⟨c,hc,fun i=> ⟨_, givenHammer _ _ (h i) le_rfl, Eventually.of_forall (fun _=> funext fun _=>funext fun _=>throw_flair _ le_rfl _ _)⟩⟩
lemma Take.product (h:Take q f k m)(ht:Take y g d m): Take (q*y) (f*g) (k+d) m:=by
    obtain ⟨c,hc,H⟩:=h.available; obtain ⟨v,hv,V⟩:=ht.available; let t:Finset ℕ:=range (k+1); let s':Finset ℕ:=range (d+1)
    let a:ℝ:= ∑ i∈ t,∑ j∈s',c*v; have ha:0 ≤ a:=sum_nonneg fun _ _=> sum_nonneg fun _ _=>mul_nonneg hc hv; refine ⟨a,ha,fun z=>?_⟩; obtain ⟨p,hP,h₁⟩:=H z; obtain ⟨r,hR,h₂⟩:=V z; let F(i j:ℕ):= Shell.throw (Bake (p i) (r j)); let W:= ∑ i∈t,∑ j∈s', F i j; let b:ℕ→ℕ→ℝ:=fun _ _ => c*v*(q*y) z
    have hp(i j)(he:i∈t)(h:j∈s'): Volume (F i j) (k+d) m (b i j):= by unfold F b; refine givenHammer _ _ (Sack.tips (BakePair (p i) (r j) _ _ (hP.2 _) (hR.2 _)) ?_) (Nat.add_le_add (Nat.le_of_lt_succ (mem_range.mp he)) (Nat.le_of_lt_succ (mem_range.mp h))); rw [Pi.mul_apply]; apply le_of_eq;ring
    let U(i):=∑ j∈s',F i j; have hU(i)(hi:i∈t): Volume (U i) (k+d) m (∑ j∈s',b i j):=Volume.sum _ _ _ (fun j hj=> hp i j hi hj)
    refine ⟨W,?_,?_⟩; unfold a; simp_rw [Finset.sum_mul]; exact Volume.sum _ _ _ hU
    filter_upwards [h₁,h₂] with n hn hn'; funext x w; let yX:=spool G n w; rw [show (f*g) z n x w= column G p k n x w* column G r d n x w from congr_arg₂ (·*·) (congr_fun (congr_fun hn.symm _) _) (congr_fun (congr_fun hn'.symm _) _)]; change Flair (∑ i∈t,U i) (k+d) yX x= (∑ i∈t,Flume.Script.value x (p i) yX)*(∑ j∈s',Flume.Script.value x (r j) yX)
    rw [flairS _ yX x U (fun i h=> (hU i h).bound _),sum_mul]; apply sum_congr rfl; intro i hi; unfold U; rw [flairS (k+d) yX x _ (fun j hj=> (hp i j hi hj).bound _),mul_sum]; apply sum_congr rfl; intro j hj; unfold F; rw [throw_flair _ (Nat.add_le_add (Nat.le_of_lt_succ (mem_range.mp hi)) (Nat.le_of_lt_succ (mem_range.mp hj))), BakeReading (p i) (r j) _ _ (hP.2 i) (hR.2 j)]
end YM.OPE.Variance
