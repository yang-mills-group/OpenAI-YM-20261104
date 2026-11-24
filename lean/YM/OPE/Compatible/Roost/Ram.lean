import YM.OPE.Compatible.Roost.Price
/-!
# Energy transfer budgets.Flight post.L. m heights depend only calendar demand
-/
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
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {v v' b u:ℝ}(A:Alps K T i v){D:Alps K T j v'} {U:Boxes G P K.K}
local notation "Y!"=>solar G d τ
local notation "T!"=> Tracts G d τ
-- avoid section implicit
variable (H:LocalRatio R)(hs:G.Simple)
variable {vν:M→ℝ}(V:(j:M)→ Alps K T P.J (vν j))(B:Medal P G K.K P.J)
lemma physTip {s:ℝ}{A:M→Row I J}(h:Tip s A 1 1):∃ z:ℝ,∀ w,(A w).strip s z:=by obtain ⟨a,b,n,H⟩:=h; exact ⟨a,fun i=>(by simpa using H i)⟩
lemma RateP (V:M→ Train P.J):∃ a b:ℝ, 0<a ∧ 0≤ b ∧∀ i:M, Telet P (charmSeal B (V i)) a b:=by
      obtain ⟨t,ht,h,_,_,hv,_,_⟩:=tipsDelta B (X:=(1:M→ℝ)) (v:=0) one_pos le_rfl le_rfl V V (show Tip 1 (fun i=> Op K.K (V i) - Op K.K (V i)) 0 1 from by simp_rw [sub_self]; refine ⟨0,le_rfl,0,fun i a b=>?_⟩; simp [Width, SumBudget]); let U(i):= charmSeal B (V i)
      obtain ⟨c,hc⟩:= physTip h; obtain ⟨u,hu⟩:= physTip (tipRoot (J:=Shade G) h zero_le_one le_rfl); obtain ⟨v,hv'⟩:= physTip hv; obtain ⟨w,hw⟩:= physTip (shuttle hv); let A:=max 0 (max (max c u) (max v w)); refine ⟨t,A,ht,le_max_left ..,fun i=>?_⟩; exact ⟨strip_mono (hc i) le_rfl (by unfold A;grind),strip_mono (hu i) le_rfl (by unfold A;grind), strip_mono (hv' i) le_rfl (by unfold A;grind), strip_mono (hw i) le_rfl (by unfold A;grind)⟩
lemma Sales (hl:∀ j,(V j).clip=p)(hv:1 ≤ vν) (b:ℝ)(m:ℕ)(S:ChartRatio G):∀ i:Ask, Loan m (fun j=>Paloma (Yarn G P K.K S (V j).live (V j).clip b) i) 1 vν:=by
      have hy(n:ℕ): Auger m (boardA V n) (boardA V n) 1 vν:=appVan (boardLoan V (word_loan p V hl) hv); have hh : Auger m (fun i:M=> collarY P (V i).live) (fun i:M=> collarY P (V i).live) 1 vν:=appVan (Loan.plat (drip G P.L) (drip_cash G P.L) (leaf_loan (m:=m) (r:=2) V (le_trans zero_le_one hv) le_rfl)); have hV:= auger_roll (plusA (plusA (auger_roll (hy 2) (-b)) (auger_roll hh (-1)) hv zero_le_one) (appVan (Loan.fixed (m:=m) _ (Boxes.folk_cap (G:=G) P S))) hv zero_le_one) ((2:ℝ)⁻¹); intro i; fin_cases i; exact (auger_roll (hy 3) (-6)⁻¹).A; exact (auger_roll (hy 3) (-6)⁻¹).A; exact (auger_roll (hy 4) (-24)⁻¹).A; exact hV.A.twirl.land; exact (nilA vν 1 _ _ m).A
-- stiffness envelope
lemma payLoan {A:M→Script I k}(h:Loan m A 1 vν)(hv:1 ≤ vν):∃ f:M→ℝ,Wealth f vν 1 ∧ 0 ≤ f ∧∀ i,soot m (A i) (f i):=by
      obtain ⟨c,hc,k,H⟩:=h; have hz(i):0 ≤vν i:=zero_le_one.trans (hv i); let f(i):= c*vν i^k; have hy:0 ≤ f:=fun i=>mul_nonneg hc (pow_nonneg (hz i) _)
      exact ⟨f,⟨c,hc,k,fun i=>by rw [Real.norm_of_nonneg (hy i),Pi.one_apply,mul_one]⟩,hy,fun i=> by simpa only [Pi.one_apply,mul_one] using H i⟩
lemma legV (S:ChartRatio G)(hv:1 ≤ vν)(hp:∀ i,(V i).clip=p)(b:ℝ)(k:ℕ):∃ f:M→ℝ, Wealth f vν 1 ∧1 ≤ f∧∀ i,weightsB (novel P K.K (vν i) P.J (V i) b S) k (fun _=> f i):=by
      choose f hf hh h using fun i=> payLoan (Sales V hp hv b k S i) hv; let Q(i:M):= ∑ j,f j i; have hp:0 ≤ Q:=fun i=> Finset.sum_nonneg (fun j _=>hh j i); exact ⟨1+Q,fortSum (p:=1) (wealthC 1) (wealthset _ _ (fun i _=>hf i) hv zero_le_one) hv zero_le_one,le_add_of_nonneg_right hp,fun i j=>(h j i).tips ((single_le_sum (fun j _=>hh j i) (mem_univ j)).trans (le_add_of_nonneg_left zero_le_one: Q i ≤1+Q i))⟩
end YM.OPE.Stroke
