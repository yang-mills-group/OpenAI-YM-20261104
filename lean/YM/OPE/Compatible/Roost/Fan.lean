import YM.OPE.Compatible.Roost.Ram
/-!
# Energy transfer ψ budgets.Flight post.L -/
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
variable {v v' b u:ℝ}{U:Boxes G P K.K}
local notation "Y!"=>solar G d τ
local notation "T!"=> Tracts G d τ
variable (H:LocalRatio R)(hs:G.Simple)
variable {vν:M→ℝ}(V:(j:M)→ Alps K T P.J (vν j))(B:Medal P G K.K P.J)
section
variable [NormedAddCommGroup E] {a:M→ℝ}
lemma soloWe {p:M→E}(h:Wealth p a 1): Brim p p a 1:=⟨h,h,(sub_self p).symm ▸ wealthZ ..⟩
lemma augW {b:M→ℝ}{p:M→E}(hb: Wealth b a 1)(ht:0≤ b)(h: Wealth p b 1):Wealth p a 1:=by
     obtain ⟨c,hc,k,H⟩:=h; obtain ⟨d,hd,m,M⟩:=hb; refine ⟨c*d^k,mul_nonneg hc (pow_nonneg hd _),m*k,fun i=>?_⟩; have hz:0 ≤ b i:=ht i; have hv:=M i; rw[Real.norm_of_nonneg hz,Pi.one_apply,mul_one] at hv; rw [Pi.one_apply,mul_one]
     have ht:=H i;rw [Pi.one_apply,mul_one] at ht;apply ht.trans; exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz hv _) hc).trans_eq (by rw [mul_pow,pow_mul (a i) m k,mul_assoc])
end
lemma PowWe {a b:M→ℝ}(h:Wealth b a 1)(k:ℕ): Wealth (fun i=>b i^k) a 1:=by
     induction k with
     | zero=>simp_rw[pow_zero]; exact wealthC _
     | succ n ih=>
         exact Eq.mp (by rw [one_mul] : Wealth (fun i=>b i^(n+1)) a ((1:M→ℝ)*1)= Wealth _ a 1) (wealth_mul ih h fun i=> (show ‖b i^(n+1)‖≤ ‖b i^n‖* ‖b i‖ from by rw [pow_succ,norm_mul]))
include hs H
lemma larking (b:ℝ)(m d:ℕ)(he:45 ≤ m)(hv:1 ≤ vν)(h:∀ i,(V i).clip=p):∃ z:M→ℝ, Wealth z vν 1∧ 0 ≤ z ∧∀ i,Paid P K.K (charmSeal B (V i).gear) (V i) R m 1 d (z i) b:=by
     obtain ⟨s,a,h₁,h₂,hT⟩:= RateP B (fun i=>(V i).gear); obtain ⟨U,hU,hE,hQ⟩:=legV V R hv h b m; obtain ⟨c,hc,hV⟩:= costsS _ _ P hs he s a h₁ h₂ K T R H K.K P.J d; let v(i:M):=c*(U i)^5; refine ⟨v,Hark.scaleD (k:=c) (PowWe hU 5),fun i=>mul_nonneg hc (pow_nonneg (zero_le_one.trans (hE i)) _),?_⟩
     intro i n _ _ L g ho t Z p X D hb; let A:=V i; have ht:= hV n (charmSeal B A.gear) (hT i) _ b A L g ho t Z p X D hb _ (hE i) (hQ i); rw[bustDD P K.K _ _ R X _ b p ht.1]; exact ⟨fun i=>beagle _ (ht.1 i), ht.2⟩
variable (Y:∀ i,Era (charmSeal B (V i).gear) (V i))(h: Aware d τ) {η:M→ℝ}
lemma Bkarst (b:ℝ)(hv:1 ≤ vν)(hp:∀ i,(V i).clip=p): Wealth (fun i:M=>actor (V i) (charmSeal B (V i).gear) R b ⟨hs,H,Y i⟩ h) vν 1:=by
      let U(i:M):= charmSeal B (V i).gear; let L(i):RollD (V i) (U i) R:=⟨hs,H,Y i⟩; let X(i):= actor (V i) (U i) R b (L i) h; change Wealth X _ _; suffices he : Brim X X vν 1 from he.A
      apply Wπ hv zero_le_one; intro i
      let f(j:Phase): Tower (Shade G) d τ→L[ℝ] _:= ContinuousLinearMap.proj j; let T(j:Phase)(x:M):= Drift.chamber (V x) (U x) R b j i (L x) h; have ht(j:Phase): Brim (T j) (T j) vν 1:=by
           by_cases he:j ≤ i; swap; · unfold T Drift.chamber; simp_rw [dif_neg he]; exact Brim.constant _
           let Q(x):= sectorOp P K.K (V x) (U x) R b (awareLeaf h j) d j i hs (Y x) H
           obtain ⟨z,hz,hq,H⟩:=larking H hs V B b (τ j) d (awareLeaf h j) hv hp; have he': Wealth Q vν 1:= normDig hz (fun x=>(publicFee (d:=d) (m:= τ j) (a:=j) (y:=i) P K.K (V x) (U x) R b (Y x) _ _ _ _ (H x) (hq x)).trans_eq (Real.norm_of_nonneg (hq x)).symm); unfold T Drift.chamber; simp_rw [dif_pos he]; exact Canal (soloWe he') (Brim.constant _) hv zero_le_one
      exact Brim.way _ _ Finset.univ (fun j _=> Canal (Brim.constant (f j)) (ht j) hv zero_le_one ) hv zero_le_one
end YM.OPE.Stroke
