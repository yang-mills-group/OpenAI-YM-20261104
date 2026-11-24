import YM.MergeProof.Tray
import YM.LocalLTE.Marked.Destiny
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
variable {μ W:ℝ} {P : Teller G} {Q : YM.ConnectedActivityE6.Target G P}


open Daisy Reserves
private lemma ffalls (Q: YM.ConnectedActivityE6.Target G P) (L:Side)(hμ:0 < μ)(i:ℕ): Rate G L (3/8+Q.rate) (fun t=> shortfall Q L μ t i):=by
   have hp:Rate G L Q.rate (fun t => (swing Q L μ 0 t 0).rootHit):=(Q.rate_root (C:=0) (β:=0) L hμ).add (Rate.power.mul_right _)
   unfold shortfall treeYield; exact (((((Rate.power (a:=3/8)).mul hp).mul_right _).mul_right _).mul_left _) -- order
-- Post-lattice for a prescribed derivative billing level
variable (P)
def Borrow (p:Q.Expense) (j n ℓ:ℕ)(χ:Chi)(o: Target.Order G W)(L:Side)(μ t v a:ℝ): Prop:=
    ∀ (c f:Side)(S:StepData c f)(T:Tube G S), Works P L t S T → Stamp T → ∀(R:Rep G f)(C':ℝ)(H:Cash W t μ L Q o C' T R),∀(D:ℕ→ℝ), Raw.Pumps R D (1*incomingE G L t) →
       ∃ (A b C d r s z B e q:ℝ)(k:ℕ)(N: Captain H j C d r s A b z B e k χ), r=v ∧ HostQ H N.conduit A B k ∧ Bikes Q L μ t p.earn q B j k ∧ ∀ (ι:Type)(_:Fintype ι) (M:ι→Lotus.Leaf R)(rA:ι→ℝ), (∀ i,0≤rA i) → (∑ i,mcount (S:=S) (G:=G) (L:=L) (s:=t) M rA D ℓ i*R.p.mass (M i).crest (M i).weight) ≤ Q.goal L t →
         Ac.Hit (Captain.reachability (H:=H)) (radiusB t) (fun z=> beaconN H ℓ z*rocket H D z* markU N M rA z n) p.earn a
-- Different Captain fits.B.looms uniform across stages. n,j arbitrary even bought afterwards.
lemma canaries (Q:YM.ConnectedActivityE6.Target G P) (p:Q.Expense) (hQ:Q.rate< -(3/8:ℝ)) : ∃ m:ℕ,∀ L:Side,m≤L.val→∀ W μ:ℝ,∀ o:ConnectedActivityE6.Target.Order G W, 0<W→0<μ→∀ j n ℓ χ,∃ v a:ℝ→ℝ,Rate G L (1/2) (fun x=>(v x)⁻¹)∧ Rate G L (3/8+Q.rate) a ∧ ∀ᶠ x in atTop, Borrow P p j n ℓ χ o L μ x (v x) (a x):=by
    obtain ⟨m,hm⟩:= adjudicateQ P Q; obtain ⟨b,hb⟩:= Daisy.early Q
    refine ⟨max m b,fun L hL W μ o hW hμ j n ℓ χ=>?_⟩
    by_cases hh : ∃ D : Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j
    swap; · exact ⟨fun _=>0,fun _=>0,(Rate.const (0:ℝ)⁻¹).weaken (by norm_num), fun e _=> (Delay.shift_pos G L).mono (fun x hx=> by rw [abs_zero]; exact Real.rpow_nonneg hx.le _),Eventually.of_forall fun x c f S T h=> (hh ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩).elim⟩ -- zero fun
    obtain ⟨D,hd,hF,hX⟩:=hh
    obtain ⟨A,a,C,d,v,t,r,B,u,k,hv,hB,hq,H⟩:= hm L ((le_max_left ..).trans hL) D hd j ℓ χ 1 W hW μ hμ o
    let i:= (Q.exp-p.earn)/2; have hi:0 < i:= by unfold i; linarith [p.price,p.worth,p.first,p.second]
    have ht: p.earn+i+i≤Q.exp:=by unfold i; linarith
    let Y s:= Height.allotQ k j (B s) s Q L μ; let E' x:= collars G i x j n*(Y x *(1-1/2:ℝ)⁻¹)
    have h := Height.ffalls Q L hμ k
    let f x:=grow G L x*(Daisy.swing Q L μ 0 x 0).rootHit
    have hf:Rate G L (3/8+Q.rate) f:= (Rate.power).mul ((Q.rate_root (C:=0) (β:=0) L hμ).add (Rate.power.mul_right _))
    have hY:Rate G L (3/8+Q.rate) Y:= by
       have he := ((hB.mul_left ((2:ℝ)^j)).mul h); rw [zero_add] at he; exact he.add h
    have hη : Rate G L 0 shiftG := (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4
    have hU:Rate G L (3/8+Q.rate) E' := by simpa only [zero_add,zero_mul] using! (((hη.pow (n*j)).mul_right (Reserves.polyPrice i (n*j))).mul (hY.mul_right ((1-1/2:ℝ)⁻¹)))
    have hX0 (F:ℝ→ℝ)(i:ℝ)(h:Rate G L (3/8+Q.rate) F):∀ᶠ s in atTop,degreePrice (radiusB s) (F s) i≤1/2:=by
       have he:Rate G L 0 (fun x=>(Animals.ballCost (radiusB x):ℝ)):=by simpa only [one_mul,add_zero] using! (Census.width_rate G L 1 0)
       have hr:Rate G L (3/8+Q.rate) (fun s=> degreePrice (radiusB s) (F s) i):=by
          unfold degreePrice Trees.stretch; simp_rw [div_eq_mul_inv]; simpa only [zero_add] using! ((((he.mul h).mul_right i⁻¹).mul_left 4))
       exact (hr.below (by linarith) (1/2) (by norm_num)).mono fun x hx=> (le_abs_self _).trans hx
    refine ⟨v,E',hv,hU,?_⟩
    filter_upwards [(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1,H,hX0 f Q.δ hf, hX0 Y i hY,Daisy.stables L Q hμ B hi ht p.price hB j k n] with x hx h hh he hb'
    intro c f S T hp hT R C' H W₀ h'
    obtain ⟨N,hN,hH⟩:= h _ _ S T (hp.patch hF hX) hT R _ H W₀ h'
    have hg:1≤grow G L x := Real.one_le_rpow hx (by norm_num)
    let Z:= swing Q L μ R.beta x C; have ht' : Z.Buy S.patch.L Q.halo (radiusB x):= hp.length_eq.symm ▸ (hb'.1.rev _ _ (hp.length_eq ▸ N.conduit.lives))
    refine ⟨_,_,_,_,_,_,_,_,_,_,k,N,rfl,hH,hb'.1,fun ι H0 M rA hv hw=> extensionQ N hg h'.1 hN M rA hv (hb _ ((le_max_right ..).trans hL)) (by rw [H.laws.intake.sizes,hp.length_eq]; exact hb'.1.covers) hw ht' hh n i p.earn p.price hi ht (?_) he⟩
    unfold shortfall treeYield Reserves.extract Reserves.polyPrice; have hG:0 < (swing Q L μ 0 x 0).rootHit:=ht'.γ; have hx:= Q.usable; positivity
end thresholds
end YM.PhysicalNext.Repeat.Height
