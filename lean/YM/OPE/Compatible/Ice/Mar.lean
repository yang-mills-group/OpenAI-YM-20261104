import YM.OPE.Compatible.Ice.April
/-! # taxes during expansion. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Ibis
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{K: KernelChoices}{I:Type}{i j k m b d e F:ℕ}{n:Side}{ε v t s r R A:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals Stroke
open Borealis Lav Borealis.Galea Quit.PriceZ Quit.Jac
variable {τ:Phase→ℕ}
section fee
variable (G)
variable {l:Filter I}{V p r':I→ℝ}
variable (n:I→ℕ)(h:Tendsto V l atTop)
lemma TownQ (b:ℕ): (Fintype.card (Fpaper G b):ℝ) ≤ (1+(b+b+1:ℝ)^4*4)*(Fintype.card G.ColorIndex:ℝ):=by
         simp only [Fpaper,Fintype.card_prod,Nat.cast_mul]; let u:Side:= ⟨2*(b+1)+1,by omega⟩; have hx:= scoopμ b u 0 (lt_add_one (2*(b+1))); apply mul_le_mul_of_nonneg_right _ (by positivity); exact (le_add_of_nonneg_left zero_le_one).trans hx
include h
lemma plot (s:ℝ)(hs:0 ≤ s)(he:RateLE l V (fun i=>(n i:ℝ)) s): RateLE l V (fun i=>(Fintype.card (Fpaper G (n i)):ℝ)) (4*s):=by
         let f(i):=(n i:ℝ); let H:= RateLE.const (1:ℝ) h; have ht : RateLE l V (fun i=> f i+f i+1) s:=(he.add he h).add (H.mono hs) h; have hx: RateLE l V (fun i=>(1+(f i+f i+1)^4*4)*(Fintype.card G.ColorIndex:ℝ)) (4*s):= (((H.mono (show 0 ≤ 4*s by positivity)).add (((ht.pow 4 h).mul (RateLE.const (4:ℝ) h)).mono (by norm_num)) h).mul (RateLE.const _ h)).mono (by norm_num)
         exact RateLE.of_norm_le hx (Eventually.of_forall fun i=>by rw [Real.norm_natCast]; exact TownQ ..)
lemma town_R (hs:0 ≤ s)(he:RateLE l V (fun i=>(n i:ℝ)) s):RateLE l V (fun i=>GramU G (n i) m k) ((4*k+m:ℝ)*s):=by
          let C:=fun i=> (n i:ℝ); apply RateLE.sum (f:=fun j i=> gumBill G (n i) j m) h; intro j hj; have hx(c:ℝ):=RateLE.const c h; unfold gumBill; push_cast; refine (((plot G n h s hs he).pow j h).mul (((hx _|>.mono hs).add (((hx _).mul ((hx _).mul he)).mono (by norm_num)) h).pow m h)).mono ?_; have ht: (j:ℝ) ≤ k:= Nat.cast_le.mpr (by have h:=mem_range.mp hj;omega); nlinarith only [mul_le_mul_of_nonneg_right ht hs]
noncomputable def StrayT (s t:ℝ):ℕ:= ⌊Real.exp (s*t)⌋₊
lemma slope_K (hs:0 ≤ s) : RateLE l V (fun i=>(StrayT s (V i):ℝ)) s∧RateIs l V (fun i=>((StrayT s (V i)+1:ℕ):ℝ)) s:=by
       let X:= fun i=>StrayT s (V i); let f(i):= (X i:ℝ); let v(i):=Real.exp (s*V i); have hv:RateLE l V f s:=RateLE.of_norm_le (RateLE.exp s h) (Eventually.of_forall (fun i=>by unfold f;rw [Real.norm_natCast]; exact Nat.floor_le (Real.exp_nonneg _)))
       refine ⟨hv,?_⟩; push_cast; exact (RateIs.exp s h).of_sandwich (hv.add ((RateLE.const (1:ℝ) h).mono hs) h) (Eventually.of_forall fun i=>(Nat.lt_floor_add_one (v i)).le) (Eventually.of_forall fun _=>le_rfl) h
variable (K:KernelChoices)(hz:4 ≤ j)
lemma ZeraX (hs:RateLE l V r' s)(hp:0≤v)(ht: - (F*v) ≤ s)(hc:s + (4*k+m:ℝ)*v ≤ R)(hl:RateLE l V p 0)(j' i':ℕ): RateLE l V (fun i=> let b:=StrayT v (V i); SearZ G k m d b ((Wfee_Z F b)⁻¹*p i) (ViewsK hz K i') (σGm hz G K m j') (r' i) (Real.exp (s*V i)) (p i)) R:=by
          let b(i):= StrayT v (V i); obtain ⟨hf,hb⟩:= slope_K h hp; let v₀:= σGm hz G K m j'; have hu(i:ℝ):= RateLE.const i h; have hv : RateLE l V (fun i=>v₀*((Wfee_Z F (b i))⁻¹*p i)) s:=(((hu _).mul ((((RateIs.power hb F).inv.pays h)).mul hl)).mono (by simpa using ht)) -- signature RateIs.pow
          have hP: s≤R:=by linarith only [hc,mul_nonneg (show 0 ≤ 4*k+(m:ℝ) by positivity) hp]
          exact ((((hu _).mul (hv.add (((RateLE.exp s h).mul hl).mono (by norm_num)) h)).mono (by linarith only [hP])).add (((town_R G _ h hp hf).mul (hv.add ((hs.mul (hu _)).mono (by norm_num)) h)).mono (by linarith only[hc])) h)
end fee
end YM.OPE.Ibis
