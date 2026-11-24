import YM.OPE.Compatible.Karu.Scroll
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.PriceZ
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {v v' b:ℝ} {A:Alps K T i v}{D:Alps K T j v'}{U:Boxes G P K.K}
local notation "Y!"=> solar G d τ
local notation "T!"=> Tracts G d τ
variable (Y Z:(solar G d τ)→L[ℝ] (solar G d τ))(hp:LocalRatio R)(hq:Aware d τ)(he:Crest G P K.K m)(hs:G.Simple)
variable (B: Medal P G K.K P.J)
variable (F:Sailing T P p R b)(H:Even c.val)
open Hark
variable (x y:Site c)(ψ:Phase)
local notation "S'"=>Sailing T P p R b
local notation "q!"=> χV P d
section Basic

variable [NormedAddCommGroup E][CompleteSpace E]
lemma chops {S:Type}[Nonempty S] (p:S→ℕ→ℕ→ E) (u:S→ℝ) {θ b:ℝ}(g:S→ℕ→S)(hg:∀ i j a n,p (g i j) a n=p i (j+a) n∧ u (g i j)=u i)(ht:0 ≤ θ)(h:θ<1)(_he:0 < b)
   (hh:∀ v:ℝ,∃ c:ℝ,0 ≤ c∧∀ i j:S, ∀ n k:ℕ,max (u i) (u j)≤ v→‖p i n k‖ ≤ c*b^k∧ ‖p i n k-p j n k‖≤ c*b^k*θ^n):
   ∃ Y:ℕ→ E,(∃ c,Hex b Y c)∧∀ i:S,∃ c:ℝ,0 ≤ c ∧∀ n k:ℕ,‖p i n k-Y k‖≤ c*b^k*θ^n:=by
      let x:= Classical.arbitrary S; obtain ⟨c,hc,H⟩:=hh (u x); have h(i j k)(hp:i ≤ j): ‖p x i k-p x j k‖≤ c*b^k*θ^i:=by
          obtain ⟨a,B⟩:= hg x (j-i) i k; have hh: max (u x) (u (g x (j-i)))≤ u x:=by rw [B,max_self]
          have ht:= (H x (g x (j-i)) i k hh).2; rwa [a,Nat.sub_add_cancel hp] at ht
      have hp(k:ℕ):CauchySeq fun i=> p x i k:=by
          have hx:= (tendsto_pow_atTop_nhds_zero_of_lt_one ht (by assumption)).const_mul (c*b^k); rw [mul_zero] at hx; apply Metric.cauchySeq_iff'.mpr; intro ε hε; obtain ⟨i,hv⟩:= eventually_atTop.1 (hx.eventually (gt_mem_nhds hε)); exact ⟨i,fun j hj=> (by rw [dist_comm]; rw [dist_eq_norm]; exact lt_of_le_of_lt (h _ _ _ hj) (hv i le_rfl))⟩
      choose Y hy using fun k=> cauchySeq_tendsto_of_complete (hp k); have he' (n k):‖p x n k-Y k‖≤c*b^k*θ^n:= le_of_tendsto (Tendsto.norm (Tendsto.sub (f:=fun _=>p x n k) tendsto_const_nhds (hy k))) (.mono (eventually_ge_atTop n) fun i hi=>h n i k hi); refine ⟨Y,⟨c,fun i=> le_of_tendsto' ((hy i).norm) (fun j=>(H x x j i (by simp)).1)⟩,?_ ⟩; intro i; obtain ⟨d,hd,D⟩:=hh (max (u i) (u x)); refine ⟨d+c,by positivity,fun n k=>?_⟩; rw [add_mul,add_mul]; exact (norm_sub_le_norm_sub_add_norm_sub _ (p x n k) _).trans (add_le_add (D i x n k le_rfl).2 (he' _ _))
end Basic
include H he
lemma album [Nonempty (S')] : ∃ U':ℕ→Dice (Tracts G d τ), (∃ C, Hex q! U' C)∧∀ V:S', ∃ a:ℝ,0≤a ∧ ∀ i j:ℕ, ‖Fitt Y Z hp hq hs V H x y ψ i j-U' j‖≤ a* (q!)^j*θC^i:=by
     let f(i:S'):= Fitt Y Z hp hq hs i H x y ψ; have ht(i:S')(j a n:ℕ): f (Sailing.shiftS i j) a n=f i (j+a) n∧ (Sailing.shiftS i j).cost=i.cost:=⟨rfl,rfl⟩; refine chops (E:= Dice (Tracts G d τ)) f Sailing.cost Sailing.shiftS ht thetaC.1.le thetaC.2 (by unfold χV;positivity) ?_; intro v; let W:= {a:TileC T P p R b // upperX a ≤ v}×ℕ; let g: W→TileC T P p R b:= fun i=>i.1.val; obtain ⟨c,hc,H⟩:= tides Y Z hp hq he hs H W g (v:=v) (fun i=> i.1.property) x y ψ Prod.snd; exact ⟨c,hc,fun i j n k hn=>H (⟨((i,j),n),hn⟩,k)⟩
end YM.OPE.Quit.PriceZ
