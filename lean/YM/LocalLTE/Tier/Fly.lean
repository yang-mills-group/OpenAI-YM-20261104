import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Coffer
import YM.LocalLTE.Tier.Hoist
import YM.LocalLTE.Tier.Vine
/-! High rate tail control purchase (any size ℓ). Assemble later against
marker vouchers. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Height
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Time Supply Input Testing
open ConnectedActivityE6.Blaze Blaze.March Captain PriceCompiler Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}
section thresholds
variable {P : Teller G} {Q : YM.ConnectedActivityE6.Target G P}

def Balloons (p : Q.Expense)(L:Side)(W μ c₁ c x e : ℝ)(ℓ j n : ℕ)(χ:Chi) (o:Target.Order G W): Prop :=
    ∀ (c' f:Side)(S:StepData c' f)(T:Tube G S), Works P L x S T → Stamp T→∀ (R:RG.Rep G f) (H:Cash W x μ L Q o c T R), ∀ (F: ℕ→ℝ), Pumps R F (c₁*incomingE G L x) →
     ∃ (C' d v t A b r B q : ℝ) (k:ℕ) (N:Captain H j C' d v t A b r B q k χ),
        Ac.Hit (Captain.reachability (H:=H)) (radiusB x) (fun z=> if tiredN H ℓ z then rocket H F z*N.markΦ z n else 0) p.earn (betaF G x L^e)
lemma gusts (Q : YM.ConnectedActivityE6.Target G P) : ∃ m:ℕ, ∀ L:Side,m≤L.val → ∀ (X:Q.Expense)(W μ c c₁:ℝ)(o:ConnectedActivityE6.Target.Order G W), 0<W→0<μ→Q.rate< -(3/8:ℝ) →∀ e:ℝ,∀ (ℓ j n:ℕ) χ, -(3/8:ℝ)*ℓ+(3/8)+Q.rate < e → ∀ᶠ x:ℝ in atTop,Balloons X L W μ c₁ c x e ℓ j n χ o:= by
  obtain ⟨m,hm⟩:= adjudicateT P Q
  refine ⟨m,fun L hL X W μ c c₁ o hW hμ hr e ℓ j n χ he =>?_⟩
  by_cases hh : ∃ D : Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j
  swap; · exact Eventually.of_forall fun x c' f S T h=> (hh ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩).elim
  obtain ⟨D,hd,hF,hX⟩:=hh
  obtain ⟨A,a,C,d,v,t,r,B,q,k,hB,hq,H⟩:=hm L hL D hd j ℓ χ c₁ W hW μ hμ o
  obtain ⟨y,hg,hK⟩:= Armada.ensemble Q L hμ X.earn X.price (by linarith [X.worth,X.first,X.second]) j k hB
  let S s:= salary Q L μ (B s) s j k
  have hs: Rate G L Q.rate S := by
    have hf:= ((Rate.const 1).add (hB.mul_left (2^j:ℝ))).mul (Q.rate_none L hμ 0 k 0); rw [zero_add] at hf; exact hf
  have hu: Rate G L (-(3/8:ℝ)*ℓ) (fun x=> (grow G L x ^ ℓ)⁻¹) := Rate.congr Rate.power (by
    filter_upwards [Delay.shift_pos G L] with x hx
    rw [neg_mul, Real.rpow_neg hx.le, Real.rpow_mul hx.le]; unfold grow; norm_num)
  have hv := (hu.mul (Rate.power (G:=G) (L:=L) (a:=3/8))).mul (hg n 0)
  filter_upwards [byline ℓ X L hμ,H,hK,hv e he,(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1,pressureYoung G L (i:=Q.δ) (Q.rate_root L hμ (β:=1) (C:=0)) (by linarith),pressureYoung G L (i:=y) hs (by linarith)] with x hx H hK hv hP hΓ hΩ
  intro c' f K T h hx' R I F' hp
  obtain ⟨N,hN⟩:=H _ _ K T (h.patch hF hX) hx' _ _ I F' hp
  have hu: 1 ≤ grow G L x:=Real.one_le_rpow hP (by norm_num)
  refine ⟨_,_,_,_,_,_,_,_,_,_,N,fun s=> budget_loosen (extensionT N hu F' hp.1 hN n hK hx.1 hx.2 hΓ hΩ s) (le_trans ?_ ((le_abs_self _).trans hv))⟩
  exact le_of_eq (by unfold grow; ring)
end thresholds
end YM.PhysicalNext.Repeat.Height
