import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Chant

/-! The native one-step nonlinear and occupied expenses at a prescribed positive price on a fixed plate. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Cub
namespace Restored
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels Peak Mercury 
open Bid Planned.PrimaryIntegral295 WaterLevels
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Circlet PPX Next.Free
variable {G : Gauge}{M : Sheet G}{K : MapPrices}{C:Programs M}{R:ℕ→ℕ→Record}{V: Targets M K}{Y: Expenses V}{l:ℕ→ℝ}{W : Return.Wages}{r : ℕ→ℕ→ℕ} {J N n :ℕ} {P:Teller G}
variable (D: Rolls M) (h:Register D Y W l)
set_option quotPrecheck false

/-- The price charged by the nonlinear conditional before it is rounded to the usual block bound. -/
def fare (M:ConnectedActivityE6.Target G P) (d:ℕ) (P0 P1:Stage) (L:Side)
    (x current tol:ℝ) : Prop :=
  ∀ c:ℝ, c ≤ credibility G P1.supportExponent P1.order P1.power →
    ∀ (f:Side) (H:Rep G f) (Z:Cloud H), H.p.mass Z.live.crest Z.live.weight=c →
      let F:=(Labels.frames G).level d
      let kp:=Local.testPrice F*current+Local.readPrice (hol G) F*
        ((L.val:ℝ)^d*(2*marvel (Q:=M) (L:=L) (x:=x) Z))
      Motion.orbitCost F*(Local.errorPrice (hol G) F*(corn G d*title G P0*kp)) ≤ tol

theorem purchase (Lx : Side)(C : Libretto G n)(D:Record)(K : KernelChoices)(M: ConnectedActivityE6.Target G P) (μ t:ℝ)(d j i r:ℕ)(P0 P1 : Stage)(o:Target.Order G t)(hD:D.ε≤1/4) (hi:4≤ i)(hj:4≤j)(hn:2≤ n)(hz:d≤j)(hm:0<μ) (tol:ℝ)(htol:0<tol):∀ᶠ x in atTop, ∃ E : Eve j i d n Lx P0 P1 P K C D M t o μ x r, fare M d P0 P1 Lx x E.current tol :=by
  let F:=(Labels.frames G).level d; let A:= hol G; let S0:=localSection G d
  let e:= title G P1; let a:=title G P0; have he₀:1≤e:=title_one ..; have ha:1≤a:=title_one ..
  let h:= credibility G P1.supportExponent P1.order P1.power
  have hh :0<h:=mul_pos (Real.exp_pos _) (zero_lt_one.trans_le he₀); let y:=min (Doors.rate Lx) tol; have hy:0<y:=lt_min (Doors.rate_pos _) htol
  let z:=Motion.orbitCost F * Local.errorPrice (hol G) F*(corn G d*a)
  have hw := (Local.probe_budget F).choose_spec.choose_spec.1; let Z:= Local.testPrice F; have hk:1 ≤ Z:=hw
  have hx:0< z:=mul_pos (mul_pos (zero_lt_one.trans_le (Motion.orbitCost_one_le F)) (zero_lt_one.trans_le (Local.errorPrice_pos A F))) (mul_pos (zero_lt_one.trans_le cornBig) (zero_lt_one.trans_le ha))
  let κ:=(y/2)/(z*Z); let V:=Push.Local.tests F; have hκ:0<κ:=div_pos (half_pos hy) (mul_pos hx (zero_lt_one.trans_le hk))
  let g (p:Local.Probe G d) (x:ℝ):=Push.Local.partPrice A p*(Cub.gaugeMeter d*((Lx.val:ℝ)^d*(2*(e*x+x))))+x
  have he (p:Local.Probe G d) : ∀ᶠ x in nhds (0:ℝ), g p x ≤ κ:= ((show Continuous (g p) by unfold g; fun_prop).continuousAt (x:=0)).eventually (ge_mem_nhds (show g p 0 < κ by simpa [g] using hκ))
  obtain ⟨b,(hv:0<b),hb⟩:= Metric.mem_nhds_iff.mp (V.eventually_all.mpr (fun i _=> he i))
  let Q:= b/2; have hQ':0<Q:=half_pos hv; have hg (p) (hz:p∈ V) : g p Q ≤ κ:= hb (Metric.mem_ball.mpr (by rw [Real.dist_eq,sub_zero,abs_of_pos hQ']; exact half_lt_self hv)) p hz
  obtain ⟨u,hu,hγ⟩:= Mercury.tuned M P0.power C D t μ o Chi.canonical Lx hn hD
  let B:= (Lx.val:ℝ)^d; let T:=Local.readPrice A F; have h':1 ≤ T:=Push.Local.readPrice_pos A F
  let S:= (y/2)/(z*T*h); have hS:0<S:=div_pos (half_pos hy) (mul_pos (mul_pos hx (zero_lt_one.trans_le h')) hh)
  filter_upwards [Rebuild.geometry (G.slopeConstant*Real.log Lx.val), V.eventually_all.mpr (fun p _=> eventually_all.mpr (fun i=> Cub.starlight p S0 A (sound G d) (Next.Foundations.valuation G d) K.penalty_pos hj hi hz (i: F.Index) Lx hQ')), hγ, hu.below (by norm_num) Q hQ', Cub.garnets C D Lx r P0.power (zero_le_one.trans he₀) hQ', Blush.fruition hm (L:=Lx) M B S hS] with x hx' ha' H hf hU hM
  -- hu may negative; take abs.Survey. 
  have ht(P' P'': BudgetPoint)(ht:P'.threshold=temp x)(hQ:P''.threshold=fiery G x Lx) : Blend 2 P''.threshold P'.threshold:=by
     refine ⟨one_le_two,P''.threshold_pos,P'.threshold_pos,P''.threshold_le,P'.threshold_le,?_ ,?_⟩
     · apply (div_le_iff₀ P''.threshold_pos).mpr; rw [ht,hQ]; exact hx'.2.2
     apply (div_le_iff₀ P'.threshold_pos).mpr; rw [ht,hQ]; exact hx'.2.1
  have priced : fare M d P0 P1 Lx x κ y :=by
    intro c h' N H Z hZ
    let Y:= H.p.mass Z.live.crest Z.live.weight
    set m:= Blush.marvel (Q:=M) (L:=Lx) (x:=x) Z
    have hB:0≤ B:=by unfold B; positivity
    have hL:= hM N H Z (B:ℂ) (by rw [Complex.norm_real,Real.norm_of_nonneg hB]); rw [Complex.norm_real,Real.norm_of_nonneg hB] at hL
    have he': B*(m+m)≤ S* h:= hL.1.trans (mul_le_mul_of_nonneg_left (hZ.trans_le (by exact h')) hS.le)
    intro Fp kp
    change Motion.orbitCost F*(Local.errorPrice (hol G) F*(corn G d*a*kp)) ≤ y
    have hh: T*(B*(m+m)) ≤ (y/2)/z:= (mul_le_mul_of_nonneg_left he' (by positivity)).trans_eq (by unfold S; field_simp)
    calc
       _ = z*kp:=by unfold z; ring
       _ = z*(Local.testPrice F*κ+(T*(B*(m+m)))):=by unfold kp; unfold Fp; congr 2; ring -- substitution
       _ ≤ z*(Local.testPrice F*κ+(y/2)/z):=mul_le_mul_of_nonneg_left (add_le_add_right hh _) hx.le
       _ = y:=by unfold κ; change z*(Local.testPrice F*((y/2)/(z*Local.testPrice F))+(y/2)/z)= y; field_simp [(show Local.testPrice F≠0 from (zero_lt_one.trans_le hk).ne')]; ring
  let E : Eve j i d n Lx P0 P1 P K C D M t o μ x r :=by
    refine ⟨Q,hQ',ht,|u x|,abs_nonneg _,?_,fun P' P'' _ f X α β a δ ψ μ hω=>?_,(fun p hp a c f S T Y A C C' b c' hB hX _ _=> (ha' _ hp a) _ _ _ _ _ A C C' b c' hB hX),κ,hκ.le,fun p hp=> le_trans ?_ (hg _ hp), fun c hc N H Z hZ=>(priced c hc N H Z hZ).trans (min_le_left _ _)⟩
    · intro c f' S T hk R e H0 F X i hx hh hχ hu J hK hb hP Y I _ _ a q b z hz hy he' hA M hM L' hL hL' j U hj hu' hn; exact (H c f' S T hk R e H0 F X i hx hh hχ hu J hK hb hP Y I a q b z hz hy he' hA M hM L' hL hL' j U hj hu' hn).climb (mul_le_mul_of_nonneg_left (le_abs_self _) M.profit) le_rfl
    · have hc:=ht _ _ α β; exact hU P' P'' δ β (a.symm ▸ hx'.1.1) ((div_le_iff₀ hc.fine).1 hc.accounted) μ hω f X ψ
    · unfold g; have h:=@Cub.horizon d; have ht:= Local.partPrice_pos A p; gcongr
  exact ⟨E,fun c hc N H Z hZ=>(priced c hc N H Z hZ).trans (min_le_right _ _)⟩

end Restored
end YM.PhysicalNext.Repeat.Cub
