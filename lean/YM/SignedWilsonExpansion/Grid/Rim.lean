import YM.SignedWilsonExpansion.Grid.Cohort
import YM.SignedWilsonExpansion.PairFlow
namespace YM.SignedWilsonExpansion.Overlap.Rim
/-! # Independent Cabins at rank-two probe and closed screen

Uses the unsmeared phase defined at time `axis`, with extant noncut vertices
on DOrd (not truncate estimates or boundary Ward modes). -/
set_option autoImplicit false
noncomputable section
open Function MeasureTheory Set Filter Finset
open MS MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.Plane.Wire MS.High MS.Tone MS.Land MS.Latch MS.Rake
open Energy (leg)
open FVA2 FVA2.Lambda Area HighRank HighScale Walk PhasePair FourierGaussian TwoGrid AxisChoice OrderHigh MassShift MarkShift
open PhasePair PairFlow Align PanelE Cohort Fair TreeLine
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge} (m:Bool)
local notation "P" => FourP
local notation "μ" => covMeasure Axis
local notation "U" => Branch G Axis
local notation "Φ" => PlanetD G
local notation "Hκ" => MS.Latch.SatP
local notation "E" => Energy.plane ( degreeX m ) 2 G 0
local notation "N" => Energy.called ( degreeX (!m)) 2 G
local notation "Q" => (Energy.leg (degreeX m) 2)
local notation "Z" => Momentum.sq
local notation "Ω" => AxisChoice.disk
local notation "π" => Fair.price
local notation "Wξ" => PhasePair.rate
local notation "KPZ" => Landau.precision
local notation "τ" => Tone.bill
local notation "Ψ" => field («P»:=FourP) (Landau.parity (A:=Axis) (C:=G.ColorIndex))
variable (X:P)(t:ℝ)(p k:P){d:ℝ}(F H:Law G)(A:G.ColorIndex)(i j:Axis)
local notation "HOT" => Shells.hot t
local notation "Δ" => Φ t
variable {X t F H}
lemma soldierD (h:SatP μ (Φ t) F H X) (Left:F=E∨ H=E) : κZ (Cabin X (Φ t) μ F H) p A=screen X t F H p A+screen X t F H (-p) A:= by
   have hv(i j:Axis)(p:P) := lanes p A i j h
   have he(i j:Axis): Cabin X (Φ t) μ F H [ W i A p,W j A (-p) ] = τ X p*(∫ k,lane X t p k F H A i j∂μ)+ τ X (-p)*(∫ k,lane X t (-p) k F H A j i∂μ):= by
        rw [ Duet.wantedD m _ _ _ _ Left 0 ]; rw [ hv i j p, ← hv j i (-p), neg_neg]; rw [ show cross (Ψ _) (Ψ _)=(1:ℂ) from rfl, one_mul ]
   have hz(p:P): ∑ i:Axis,∑ j:Axis,( KPZ i j p:ℂ )* ( τ X p * ∫ k,lane X t p k F H A i j∂μ) = screen X t F H p A:= by
        unfold screen panel; rw [ integral_finsetSum ]; swap; · exact fun i _=> integrable_finsetSum _ (fun j _=> (lane_paid p A i j h).const_mul _)
        rw [ Finset.mul_sum ]; apply Finset.sum_congr rfl; intro i _; rw [ integral_finsetSum _ ( fun j _=> (lane_paid p A i j h).const_mul _ ), Finset.mul_sum ]; apply Finset.sum_congr rfl; intro j _; rw [ integral_const_mul ]; ring
   unfold κZ; simp_rw [ he, mul_add, Finset.sum_add_distrib ]; rw [ hz ]; congr 1; conv_lhs=>rw [ Finset.sum_comm ]
   rw [← hz]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; rw [ Landau.k_even,Landau.realK i j ]
lemma lane_gaugeD (Left:F=E∨H=E) : lane X t p k F H A i j= ((2:ℂ)*τ X k)*(∑ u:Axis,∑ v:Axis, ( (bond HOT k u v:ℝ):ℂ)*(F [ W u A k, W i A p ]* H [ W v A (-k), W j A (-p) ])):= by
    have h(z:Lane4 G)(k:Lane4 G)(he:Bubble.wing z): E [z,k]=0:= Walk.plane_g _ ⟨z,by simp,Bubble.side he⟩
    let f(u v:U):= F [(u,k),W i A p]* H [(v,-k),W j A (-p)]; let c:ℂ:=2*τ X k
    have ht(u v:U): τ X k * meshZ (Φ t) u v F H [W i A p] [ W j A (-p) ] k= c * ( lineL G HOT u v k* f u v ):= by unfold meshZ; rw [ dotL, show cross (Landau.parity v) (degree Ψ [W i A p])= (1:ℂ) from cross_false' _ ]; unfold f c; ring
    unfold PanelE.lane; simp_rw [ ht, ← Finset.mul_sum ]; rw [ starLine ]; have hu (u v:U)(hh: Landau.parity u=true)(hv:Landau.parity v=true): f u v=0:= by unfold f; rcases Left with ha|ha; rw [ ha, h (u, k) _ hh, zero_mul ]; rw [ha,h (v,-k) _ hv,mul_zero]
    simp_rw [ hu ( Area.U₀ _ _ ) ( Area.C₀ _ ) rfl rfl, hu (Area.C₀ _) (Area.U₀ _ _) rfl rfl, mul_zero, Finset.sum_const_zero, add_zero ]; rw [ Finset.sum_eq_single_of_mem A ( mem_univ _ ) ];
    intro c _ hv; refine Finset.sum_eq_zero fun u _=> Finset.sum_eq_zero fun v _=>?_ ; apply mul_eq_zero_of_right; change F [ W u c k,W i A p ] * H [ W v c (-k), W j A (-p) ] =0; rcases Left with ha|ha; rw [ha, peel,if_neg hv,zero_mul]; rw [ha,peel,if_neg hv,mul_zero]

lemma E_mirD :ghostMir E A:= by intro i j p q; rw [peel,peel,if_pos rfl,if_pos rfl, leg_neg, leg_neg ]; push_cast; ring
lemma mirD (hp:ghostMir F A)(ht:ghostMir H A)(Left:F=E∨H=E): lane X t p k F H A i j = lane X t p k H F A j i:= by
    rw [lane_gaugeD m _ _ _ i j Left,lane_gaugeD m _ _ _ j i Left.symm]; congr 1
    conv_rhs=> rw [ Finset.sum_comm ]
    refine Finset.sum_congr rfl fun u _=> Finset.sum_congr rfl fun v _=>?_
    rw [ht, hp,mul_comm (H _), Walk.bond, Walk.bond, Landau.realK u v ]
lemma flipPD (hp:ghostMir F A): panel X t p k E F A=panel X t p k F E A:= by
    unfold panel; simp_rw [ mirD m (X:=X) (t:=t) p k A _ _ (E_mirD m A) hp ( Or.inl rfl ) ]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_; rw [ Landau.realK ]
variable (X t)
abbrev L0D (A:G.ColorIndex)(k p:P)(i:Axis):ℂ:= ∑ u:Axis,(Q u k) • F [ W u A k, W i A p ]
lemma fixedD (p k:P)(i j:Axis) : E [W i A p,W j A k]= ↑( (-2:ℝ)*Q i p*Q j k):= by rw [ Walk.peel, if_pos rfl ]
lemma lane_tD : lane X t p k F E A i j= ( (-4:ℂ)*τ X k * (↑(Q j p*(Z k*HOT (Z k))):ℂ) )* L0D m (F:=F) A k p i:= by
    rw [ lane_gaugeD m _ _ _ _ _ ( Or.inr rfl ) ]; simp_rw [ show ∀ v:Axis,E [W v A (-k), W j A (-p)]=↑( (-2:ℝ)*Q v k*Q j p) from fun v=> ( E_mirD m A .. ).trans (fixedD m A ..) ]; push_cast
    have he(u:Axis):(∑ v:Axis,( bond HOT k u v:ℂ)*( F [ W u A k,W i A p ] * ( -2*( Q v k :ℂ)*(Q j p:ℂ) ) ) )= (Z k:ℂ)*(HOT (Z k):ℂ) * ((Q u k):ℂ) * ( F [ W u A k,W i A p ] * ( -2*(Q j p:ℂ)) ):= by
        rw [ show (Z k:ℂ)*(HOT (Z k):ℂ)*(Q u k:ℂ)=∑ v:Axis,(bond HOT k u v:ℂ)*(Q v k:ℂ) from ?_ ]; swap; · rw [← Complex.ofReal_mul, ← Complex.ofReal_mul,← projection HOT ]; push_cast; rfl
        rw [ Finset.sum_mul ]; exact Finset.sum_congr rfl fun i _=> by ring
    push_cast at he; simp_rw [ he ]; unfold L0D; rw [ Finset.mul_sum,Finset.mul_sum ]; apply Finset.sum_congr rfl; intro u _; rw [ Complex.real_smul ]; ring
abbrev mixZD (F:Law G)(k p:P)(A:G.ColorIndex):=∑ u:Axis,∑ i:Axis, Q u k • Q i p • F [ W u A k,W i A p ]
lemma panel_tD (F:Law G) : panel X t p k F E A =
         ( (-4:ℂ)*τ X k * (↑( Z p * Z k * HOT (Z k) ):ℂ) ) * mixZD m F k p A:= by
    unfold panel; simp_rw [lane_tD]; let A'(i:Axis):= L0D m (F:=F) A k p i
    have he(i:Axis):(∑ j:Axis, (KPZ i j p:ℂ)* (( (-4:ℂ)*τ X k*(↑(Q j p * (Z k*HOT (Z k))):ℂ) )*A' i))=
        ( (-4:ℂ)*τ X k * (↑(Z p*Z k* HOT (Z k)):ℂ) ) * ((Q i p:ℂ)*A' i):= by
            have hv : (Z p*Q i p:ℝ)=∑ j:Axis, KPZ i j p*Q j p:= by simpa [bond] using ( projection (p:=p) (a:=degreeX m) (b:=2) (j:=i) (fun _=>1) ).symm
            let X₀:= (-4:ℂ)*τ X k*( ↑( Z k * HOT (Z k)):ℂ )* A' i
            rw [ show ( (-4:ℂ)*τ X k * (↑(Z p*Z k* HOT (Z k)):ℂ) ) * ((Q i p:ℂ)*A' i) =(↑(Z p*Q i p):ℂ)*X₀ from (by unfold X₀; push_cast; ring),hv, Complex.ofReal_sum,Finset.sum_mul ]; refine Finset.sum_congr rfl fun j _=>?_ ; unfold X₀; push_cast; ring
    change (∑ i:Axis,∑ j:Axis,(KPZ i j p:ℂ)* ((_)* A' i))=_
    simp_rw [he]; unfold mixZD; conv_rhs=>arg 2; rw [ Finset.sum_comm ]
    unfold A' L0D; simp_rw [ Complex.real_smul,Finset.mul_sum ]; apply Finset.sum_congr rfl; intro i _; exact Finset.sum_congr rfl fun j _=>by ring
-- continued operator to heat projections
variable {B: Land.Booked (Press.portDeck G)} (M:Land.MS_Data G B)(simple:G.Simple) (v y:ℝ)
local notation "T" => MarkShift.settled M N v (0,0)
local notation "K" => leap v (MarkRows.packet M N 2) (y,t)
local notation "α" => (v*OrderHigh.kinetic G)
local notation "β" => (v*Align.salaryQ G)
local notation "E'" => Energy.plane (degreeX (!m)) 2 G 0
include simple
lemma legsM (t:ℝ) (i j:Axis)(p q:QP)(A:G.ColorIndex):
    MarkShift.bridge M N v t [ W i A p,W j A q ]=
       (↑(α * (PhasePair.rate t p+PhasePair.rate t q)):ℂ)* E' [ W i A p,W j A q ]:= by
    unfold MarkShift.bridge; rw [ Walk.ampL, Energy.found, carried M simple ]; simp only [Finset.sum_add_distrib,peel, ↓reduceIte, ← Complex.ofReal_mul ]
    have hx (u:Axis)(p:QP)(q:QP)(j:Axis): E' [W u A p, W j A q]= (( ( (-2:ℝ)*Energy.leg (degreeX (!m)) 2 u p*Energy.leg (degreeX (!m)) 2 j q):ℝ):ℂ):= by rw [ Walk.peel,if_pos rfl ]
    simp_rw [ hx, ← Complex.ofReal_mul, ← Complex.ofReal_sum, ← Complex.ofReal_add ]; apply congr_arg
    let B:=OrderHigh.kinetic G
    have he (p q:QP)(i j:Axis): (∑ k:Axis, (2*B*v*amp t p.sq*p.sq*precision i k p) * ( (-2*Energy.leg (degreeX (!m)) 2 k p)* Energy.leg (degreeX (!m)) 2 j q))= 2*B*v*p.sq*( p.sq*amp t p.sq *Energy.leg (degreeX (!m)) 2 i p)*(-2*Energy.leg (degreeX (!m)) 2 j q):= by
       rw [← Walk.projection (amp t)]; simp_rw [ Finset.mul_sum, Finset.sum_mul ]; apply Finset.sum_congr rfl; intro k _; unfold bond; ring
    unfold B at he; rw [ he p, he q ]; unfold PhasePair.rate rateV; ring

lemma shiftLP : ghostMir K A:= by
    intro i j p q; rw [ MarkShift.per_mark M N simple ( Energy.firstE (degreeX (!m)) 2 G 0 ) Energy.full _ _ _ rfl,
       MarkShift.per_mark M N simple _ Energy.full _ _ _ rfl, legsM (m:=m) M simple v, legsM (m:=m) M simple v ]; dsimp only; rw [ Cohort.flipNorm p m M simple v A q i j, E_mirD (!m) A ]; unfold PhasePair.rate; rw [ PhasePair.rate_neg, PhasePair.rate_neg ]
lemma mixvD : mixZD m K k p A = Cohort.escrow m M v A k p + (α * (Wξ t k+Wξ t p)) • mixZD m E' k p A := by
    unfold mixZD; simp_rw [ MarkShift.per_mark M N simple _ Energy.full v (y,t) _ ( show [_,_].length=2 from rfl ), smul_add, legsM (m:=m) M simple v (y,t).2 ]; -- cast
    unfold Cohort.escrow; simp_rw [ Finset.smul_sum, Finset.sum_add_distrib ]; congr 1; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; simp_rw [ Complex.real_smul ]; ring

end
end YM.SignedWilsonExpansion.Overlap.Rim
