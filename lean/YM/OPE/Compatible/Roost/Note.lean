import YM.OPE.Compatible.Roost.Sunny
/-!
# Warmup of carols. Cost basis clip may change. Payer chooses once per requested test. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)
open Topic
variable (Z:Topic H hs X B D₀)
variable {Y Y' α:M→ℝ}
lemma cashDay (S:Quota K T P'.J j)(L:ℝ)(U:(i:M)→Alps K T P'.J (Y i))(hy:1≤ Y)(h: Mag P'.J j)(hp:p.direct≤K.γ j)(hv: S.minL ≤P'.L.val)(ht:LocalRatio R): ∃ Y':M→ℝ,1 ≤Y'∧Wealth Y' Y 1 ∧ (∀ i,L≤Y' i) ∧ ∃ α:M→ℝ,Wealth α Y 1∧∃ V:(i:M)→Alps K T j (Y' i),∀ i,(V i).clip=p∧ Charm P'.L (U i) (V i) (α i) R:=by
     let k:= max 1 (max L (S.tab P'.L)); let f(x:M):= k*Y x; have hh:1 ≤ k:=le_max_left ..; have hX(i):k ≤ f i:=le_mul_of_one_le_right (zero_le_one.trans hh) (hy i); have hp'(i): Y i ≤ f i:= le_mul_of_one_le_left (zero_le_one.trans (hy i)) hh; choose N y hz hq hy' using fun i=>tuber hp P'.L S hv P'.coarse ((le_max_right ..|>.trans (le_max_right ..)).trans (hX i)) h P'.odd_side ht (hy i) ((half_le_self (zero_le_one.trans (hy i))).trans (hp' i)) (U i);
     refine ⟨f,fun i=>hh.trans (hX i),⟨k,zero_le_one.trans hh,1,fun i=>by have hx:=hh.trans (hX i); rw[Real.norm_of_nonneg (zero_le_one.trans hx),Pi.one_apply,pow_one,mul_one]⟩,fun i=>(show L ≤k from (le_max_left ..|>.trans (le_max_right ..))).trans (hX i),y,⟨max 0 (big_cost S P'.L),le_max_left ..,0,fun i=>?_⟩,N, fun i=>⟨hq i, hy' i⟩⟩; rw [pow_zero,Pi.one_apply,mul_one,mul_one]; exact (hz i).trans (le_max_right ..)
lemma growL (S:Quota K T P.J P.J)(U:(i:M)→Alps K T P.J (Y i))(hv:1 ≤ Y)(ht:∀ i,(U i).clip=p)(hp:p.direct≤ K.γ P.J)(he: S.minL ≤ P.L.val) (h:big_cost S P.L≤ b)(hh:∀ i,S.tab P.L≤Y i)(hr:LocalRatio R): ∃ X:M→Sailing T P p R b,(Sailing.cost ∘ X)=Y∧∀ i,HEq ((X i).U 0) (U i):=by
      choose A hA hX using fun i=> Sailing.launchAt S _ (hv i) he (hh i) (show Mag P.J P.J from ⟨P.order_cut,P.order_cut,Or.inl rfl⟩) hp hr (U i) (ht i) h; exact ⟨A,funext hA,hX⟩
namespace Topic
variable {Z} {U:(i:M)→Alps K T j (Y i)}{P0:Z.Ω M Y'}{a:Axis}{hj:4 ≤ j}{hY:0 ≤Y}
lemma Floss.pullAlong (p:Floss Z U P0 hj hY k Hp a)(q:I→ M): Floss Z (u:=Y∘q) (fun i=>U (q i)) (P0.branch q) hj (fun i=> hY (q i)) k Hp a:=⟨p.dimD,p.cap,p.vol,p.ward,fun i hi z=>p.turn i hi (q z),fun e he i n v x y h ht z=> p.corn e he i n v x y h ht (q z)⟩
end Topic
end YM.OPE.Stroke
