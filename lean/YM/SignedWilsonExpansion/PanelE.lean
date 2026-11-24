import YM.SignedWilsonExpansion.TwoGrid
namespace YM.SignedWilsonExpansion.PanelE
/-! # Independent Cabins at rank-two probe and closed screen

Uses the unsmeared phase defined at time `axis`, with extant noncut vertices
on DOrd (not truncate estimates or boundary Ward modes). -/
set_option autoImplicit false
noncomputable section
open Function MeasureTheory Set Filter Finset
open MS MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.Plane.Wire MS.High MS.Tone MS.Land MS.Latch MS.Rake
open Energy (leg)
open FVA2 FVA2.Lambda Area HighRank HighScale Walk PhasePair FourierGaussian TwoGrid AxisChoice OrderHigh MassShift MarkShift
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}
local notation "P" => FourP
local notation "μ" => covMeasure Axis
local notation "U" => Branch G Axis
local notation "Φ" => PlanetD G
local notation "Hκ" => MS.Latch.SatP
local notation "E" => Energy.plane 1 2 G 0
local notation "N" => Energy.called 1 2 G
local notation "Q" => (Energy.leg 1 2)
local notation "Z" => Momentum.sq
local notation "Ω" => AxisChoice.disk
local notation "π" => TwoGrid.price
local notation "Wξ" => PhasePair.rate
local notation "KPZ" => Landau.precision
local notation "τ" => Tone.bill
local notation "Ψ" => field («P»:=FourP) (Landau.parity (A:=Axis) (C:=G.ColorIndex))
variable (X:P)(t:ℝ)(p k:P){d:ℝ}(F H:Law G)(A:G.ColorIndex)(i j:Axis)
local notation "HOT" => Shells.hot t
local notation "Δ" => Φ t
abbrev lane :ℂ:= ∑ u:U,∑ v:U,τ X k*meshZ (PlanetD G t) u v F H [ W i A p ] [ W j A (-p) ] k
abbrev panel :ℂ:= ∑ i:Axis,∑ j:Axis,( ↑(KPZ i j p):ℂ ) * lane X t p k F H A i j
-- exact WW evaluation
variable {X t F H}
lemma lane_paid (h: SatP μ (Φ t) F H X): Integrable (fun k=>lane X t p k F H A i j) μ:= integrable_finsetSum Finset.univ fun u _=> integrable_finsetSum Finset.univ fun v _=> h ..
lemma panel_int (h:SatP μ (Φ t) F H X): Integrable (fun k=>panel X t p k F H A) μ:= integrable_finsetSum Finset.univ fun i _=> integrable_finsetSum Finset.univ fun j _=> (lane_paid p A i j h).const_mul _
lemma lanes (h:SatP μ (Φ t) F H X) : cuts X ( Φ t ) F H [ W i A p ] [ W j A (-p) ]= τ X p*∫ k:P,lane X t p k F H A i j∂μ:= by
   unfold lane cuts; rw [ integral_finsetSum ]; swap; · exact fun u _=>integrable_finsetSum _ fun v _=> h ..
   rw [ show net [W i A p]=p from (by simp [net,W,qnote]) ]; congr 1; exact Finset.sum_congr rfl fun u _=> ( integral_finsetSum _ ( fun v _=> h ..) ).symm
abbrev screen (X:P) (t:ℝ)(F H:Law G)(p:P)(A:G.ColorIndex):= τ X p * ∫ k:P,panel X t p k F H A∂ μ
lemma soldier (h:SatP μ (Φ t) F H X) (Left:F=E∨ H=E) : κZ (Cabin X (Φ t) μ F H) p A=screen X t F H p A+screen X t F H (-p) A:= by
   have hv(i j:Axis)(p:P) := lanes p A i j h
   have he(i j:Axis): Cabin X (Φ t) μ F H [ W i A p,W j A (-p) ] = τ X p*(∫ k,lane X t p k F H A i j∂μ)+ τ X (-p)*(∫ k,lane X t (-p) k F H A j i∂μ):= by
        rw [ PhasePair.wanted _ _ _ _ Left 0 ]; rw [ hv i j p, ← hv j i (-p), neg_neg]; change _ =_; rw [ show cross (Ψ _) (Ψ _)=(1:ℂ) from rfl, one_mul ]
   have hz(p:P): ∑ i:Axis,∑ j:Axis,( KPZ i j p:ℂ )* ( τ X p * ∫ k,lane X t p k F H A i j∂μ) = screen X t F H p A:= by
        unfold screen panel; rw [ integral_finsetSum ]; swap; · exact fun i _=> integrable_finsetSum _ (fun j _=> (lane_paid p A i j h).const_mul _)
        rw [ Finset.mul_sum ]; apply Finset.sum_congr rfl; intro i _; rw [ integral_finsetSum _ ( fun j _=> (lane_paid p A i j h).const_mul _ ), Finset.mul_sum ]; apply Finset.sum_congr rfl; intro j _; rw [ integral_const_mul ]; ring
   unfold κZ; simp_rw [ he, mul_add, Finset.sum_add_distrib ]; rw [ hz ]; congr 1; conv_lhs=>rw [ Finset.sum_comm ]
   rw [← hz]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; rw [ Landau.k_even,Landau.realK i j ]
lemma lane_gauge (Left:F=E∨H=E) : lane X t p k F H A i j= ((2:ℂ)*τ X k)*(∑ u:Axis,∑ v:Axis, ( (bond HOT k u v:ℝ):ℂ)*(F [ W u A k, W i A p ]* H [ W v A (-k), W j A (-p) ])):= by
    have h(z:Lane4 G)(k:Lane4 G)(he:Bubble.wing z): E [z,k]=0:= Walk.plane_g _ ⟨z,by simp,Bubble.side he⟩
    let f(u v:U):= F [(u,k),W i A p]* H [(v,-k),W j A (-p)]; let c:ℂ:=2*τ X k
    have ht(u v:U): τ X k * meshZ (Φ t) u v F H [W i A p] [ W j A (-p) ] k= c * ( lineL G HOT u v k* f u v ):= by unfold meshZ; rw [ dotL, show cross (Landau.parity v) (degree Ψ [W i A p])= (1:ℂ) from cross_false' _ ]; unfold f c; ring
    unfold lane; simp_rw [ ht, ← Finset.mul_sum ]; rw [ starLine ]; have hu (u v:U)(hh: Landau.parity u=true)(hv:Landau.parity v=true): f u v=0:= by unfold f; rcases Left with ha|ha; rw [ ha, h (u, k) _ hh, zero_mul ]; rw [ha,h (v,-k) _ hv,mul_zero]
    simp_rw [ hu ( Area.U₀ _ _ ) ( Area.C₀ _ ) rfl rfl, hu (Area.C₀ _) (Area.U₀ _ _) rfl rfl, mul_zero, Finset.sum_const_zero, add_zero ]; rw [ Finset.sum_eq_single_of_mem A ( mem_univ _ ) ];
    intro c _ hv; refine Finset.sum_eq_zero fun u _=> Finset.sum_eq_zero fun v _=>?_ ; apply mul_eq_zero_of_right; change F [ W u c k,W i A p ] * H [ W v c (-k), W j A (-p) ] =0; rcases Left with ha|ha; rw [ha, peel,if_neg hv,zero_mul]; rw [ha,peel,if_neg hv,mul_zero]

def ghostMir (F:Law G)(A:G.ColorIndex): Prop:=∀ i j p q,F [ W i A (-p),W j A (-q) ] = F [ W i A p,W j A q ]
lemma E_mir :ghostMir E A:= by intro i j p q; rw [peel,peel,if_pos rfl,if_pos rfl, leg_neg, leg_neg ]; push_cast; ring
lemma mir (hp:ghostMir F A)(ht:ghostMir H A)(Left:F=E∨H=E): lane X t p k F H A i j = lane X t p k H F A j i:= by
    rw [lane_gauge _ _ _ i j Left,lane_gauge _ _ _ j i Left.symm]; congr 1
    conv_rhs=> rw [ Finset.sum_comm ]
    refine Finset.sum_congr rfl fun u _=> Finset.sum_congr rfl fun v _=>?_
    rw [ht, hp,mul_comm (H _), Walk.bond, Walk.bond, Landau.realK u v ]
lemma flipP (hp:ghostMir F A): panel X t p k E F A=panel X t p k F E A:= by
    unfold panel; simp_rw [ mir (X:=X) (t:=t) p k A _ _ (E_mir A) hp ( Or.inl rfl ) ]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_; rw [ Landau.realK ]
variable (X t)
abbrev L0 (A:G.ColorIndex)(k p:P)(i:Axis):ℂ:= ∑ u:Axis,(Q u k) • F [ W u A k, W i A p ]
lemma fixed (p k:P)(i j:Axis) : E [W i A p,W j A k]= ↑( (-2:ℝ)*Q i p*Q j k):= by rw [ Walk.peel, if_pos rfl ]
lemma lane_t : lane X t p k F E A i j= ( (-4:ℂ)*τ X k * (↑(Q j p*(Z k*HOT (Z k))):ℂ) )* L0 (F:=F) A k p i:= by
    rw [ lane_gauge _ _ _ _ _ ( Or.inr rfl ) ]; simp_rw [ show ∀ v:Axis,E [W v A (-k), W j A (-p)]=↑( (-2:ℝ)*Q v k*Q j p) from fun v=> ( E_mir A .. ).trans (fixed A ..) ]; push_cast
    have he(u:Axis):(∑ v:Axis,( bond HOT k u v:ℂ)*( F [ W u A k,W i A p ] * ( -2*( Q v k :ℂ)*(Q j p:ℂ) ) ) )= (Z k:ℂ)*(HOT (Z k):ℂ) * ((Q u k):ℂ) * ( F [ W u A k,W i A p ] * ( -2*(Q j p:ℂ)) ):= by
        rw [ show (Z k:ℂ)*(HOT (Z k):ℂ)*(Q u k:ℂ)=∑ v:Axis,(bond HOT k u v:ℂ)*(Q v k:ℂ) from ?_ ]; swap; · rw [← Complex.ofReal_mul, ← Complex.ofReal_mul,← projection HOT ]; push_cast; rfl
        rw [ Finset.sum_mul ]; exact Finset.sum_congr rfl fun i _=> by ring
    push_cast at he; simp_rw [ he ]; unfold L0; rw [ Finset.mul_sum,Finset.mul_sum ]; apply Finset.sum_congr rfl; intro u _; rw [ Complex.real_smul ]; ring
abbrev mixZ (F:Law G)(k p:P)(A:G.ColorIndex):=∑ u:Axis,∑ i:Axis, Q u k • Q i p • F [ W u A k,W i A p ]
lemma panel_t (F:Law G) : panel X t p k F E A =
         ( (-4:ℂ)*τ X k * (↑( Z p * Z k * HOT (Z k) ):ℂ) ) * mixZ F k p A:= by
    unfold panel; simp_rw [lane_t]; let A'(i:Axis):= L0 (F:=F) A k p i
    have he(i:Axis):(∑ j:Axis, (KPZ i j p:ℂ)* (( (-4:ℂ)*τ X k*(↑(Q j p * (Z k*HOT (Z k))):ℂ) )*A' i))=
        ( (-4:ℂ)*τ X k * (↑(Z p*Z k* HOT (Z k)):ℂ) ) * ((Q i p:ℂ)*A' i):= by
            have hv : (Z p*Q i p:ℝ)=∑ j:Axis, KPZ i j p*Q j p:= by simpa [bond] using ( projection (p:=p) (a:=1) (b:=2) (j:=i) (fun _=>1) ).symm
            let X₀:= (-4:ℂ)*τ X k*( ↑( Z k * HOT (Z k)):ℂ )* A' i
            rw [ show ( (-4:ℂ)*τ X k * (↑(Z p*Z k* HOT (Z k)):ℂ) ) * ((Q i p:ℂ)*A' i) =(↑(Z p*Q i p):ℂ)*X₀ from (by unfold X₀; push_cast; ring),hv, Complex.ofReal_sum,Finset.sum_mul ]; refine Finset.sum_congr rfl fun j _=>?_ ; unfold X₀; push_cast; ring
    change (∑ i:Axis,∑ j:Axis,(KPZ i j p:ℂ)* ((_)* A' i))=_
    simp_rw [he]; unfold mixZ; conv_rhs=>arg 2; rw [ Finset.sum_comm ]
    unfold A' L0; simp_rw [ Complex.real_smul,Finset.mul_sum ]; apply Finset.sum_congr rfl; intro i _; exact Finset.sum_congr rfl fun j _=>by ring
-- continued operator to heat projections
lemma mix0 : mixZ E k p A= (( (-2*Ω k*Ω p):ℝ):ℂ ):= by
    have hp (p:P): (∑ i:Axis,Q i p^2)= Ω p:= by rw [TwoGrid.card4]; simp [Energy.leg, AxisChoice.disk, add_comm]
    unfold mixZ; simp_rw [fixed A,Complex.real_smul]; rw [ ← hp k, ← hp p ]; push_cast; simp_rw [ Finset.mul_sum, Finset.sum_mul ]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; exact Finset.sum_congr rfl fun j _=> by ring
lemma heat0 : panel (axis d) t p k E E A= ((8:ℝ)* Z p*Ω p) • FourierGaussian.dot d t k:= by rw [ panel_t,mix0 ]; unfold FourierGaussian.dot; simp_rw [ Complex.real_smul ]; push_cast; ring
variable {B: Land.Booked (Press.portDeck G)} (M:Land.MS_Data G B)(simple:G.Simple) (v y:ℝ)
local notation "T" => MarkShift.settled M N v (0,0)
local notation "K" => leap v (MarkRows.packet M N 2) (y,t)
local notation "α" => (v*OrderHigh.kinetic G)
local notation "β" => (v*OrderHigh.locus G)
include simple
lemma shift : ghostMir K A:= by
    intro i j p q; rw [ MarkShift.per_mark M N simple ( Energy.firstE 1 2 G 0 ) Energy.full _ _ _ rfl,
       MarkShift.per_mark M N simple _ Energy.full _ _ _ rfl, PhasePair.legs M simple, PhasePair.legs M simple ]; dsimp only; rw [ TwoGrid.flipN p M simple v A q i j, E_mir A ]; unfold PhasePair.rate; rw [ PhasePair.rate_neg, PhasePair.rate_neg ]
lemma mixv : mixZ K k p A = TwoGrid.escrow M v A k p + (α * (Wξ t k+Wξ t p)) • mixZ E k p A := by
    unfold mixZ; simp_rw [ MarkShift.per_mark M N simple _ Energy.full v (y,t) _ ( show [_,_].length=2 from rfl ), smul_add, PhasePair.legs M simple v (y,t).2 ]; -- cast
    unfold TwoGrid.escrow; simp_rw [ Finset.smul_sum, Finset.sum_add_distrib ]; congr 1; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; simp_rw [ Complex.real_smul ]; ring
lemma panel_v : panel (axis d) t p k K E A = ((-4:ℂ)*τ (axis d) k * (↑( Z p * Z k * HOT (Z k) ):ℂ) ) * TwoGrid.escrow M v A k p+
                             (α*( Wξ t k+ Wξ t p )) • (((8:ℝ)* Z p*Ω p) • FourierGaussian.dot d t k):= by
    rw [ panel_t,mixv _ _ _ _ M simple v y,← heat0 t p k A,panel_t ]; simp_rw [ Complex.real_smul ]; ring
lemma mean_v : π p (fun p=>π k (fun k=> panel (axis d) t p k K E A))=
         ((8:ℝ)*Z p*Ω p) • ( (β+α*Wξ t p) • FourierGaussian.dot d t k + α • FourierGaussian.bonus d t k):= by
    let G' (p k:P):ℂ:= (-4:ℂ)*τ (axis d) k * (↑( Z p * Z k * HOT (Z k) ):ℂ);
    let F(k p:P):ℂ:= TwoGrid.escrow M v A k p; let R(p k:P):ℂ:= (α * (Wξ t k + Wξ t p)) • (((8:ℝ)* Z p*Ω p) • FourierGaussian.dot d t k)
    have he(p k:P):panel (axis d) t p k K E A= G' p k* F k p+R p k:= panel_v _ _ _ _ _ simple v y
    have hπ(a:P)(f g:P→ℂ): π a (fun p=> f p+ g p)=π a f+π a g:= map_add (π a) ..
    have hx (p:P): π k (fun k=>G' p k*F k p)= G' p k *π k (fun k=> F k p):= TwoGrid.currency ( fun i=>by unfold G'; simp_rw [ trcB,trcF ] ) _
    have ht(p:P): π k (fun k=>R p k)=R p k := TwoGrid.uniform ( fun i=>by unfold R PhasePair.rate PhasePair.rateV FourierGaussian.dot; simp_rw [trcD,trcF,trcB] )
    simp_rw [ he, hπ,hx,ht ]; rw [ TwoGrid.uniform (f:=fun p=> R p k) (c:=R p k) ( fun i=>by unfold R PhasePair.rate PhasePair.rateV; simp_rw [trcD,trcB] ), TwoGrid.currency (f:=fun p=> G' p k) (c:=G' p k) ( fun i=>by unfold G'; simp_rw [ trcB ] ) _ ]; unfold G' R F; rw [ TwoGrid.counted p M simple ]; unfold FourierGaussian.bonus FourierGaussian.dot; simp_rw [ Complex.real_smul ]; push_cast; ring
section val
local notation "†" => Φ t
local notation "a" => axis d
omit simple
variable {V V':Law G}
lemma alike {Y:MS.Latch.Edge G}(hc: SatP μ Y F H X)(he:similar F V)(ht:similar H V') : SatP μ Y V V' X:= by
    intro i j l r; obtain h:=hc i j l r; unfold MS.Latch.meshZ at *; simp_rw [he (_::_) (by simp), ht (_::_) (by simp)] at h; exact h
include M y
lemma sat_g : SatP μ (Φ t) E E X := alike X ( mark_permit t X ( wallet_marker M 0 (y,t) ) ( wallet_marker M 0 (y,t) ) ) ( PhasePair.initial M _ ) (PhasePair.initial M _)
lemma sat_k : SatP μ (Φ t) K E X ∧ SatP μ (Φ t) E K X:= by
   have he: K ∈ MS.Breeze.Wallet G:= ( MS.Breeze.Wallet G ).sub_mem ( wallet_marker M 2 (y+v,t) ) ( wallet_marker M 2 (y,t) )
   exact ⟨ alike X ( mark_permit t X he ( wallet_marker M 0 (y,t) ) ) ( fun _ _=> rfl ) ( PhasePair.initial M _ ), alike X ( mark_permit t X ( wallet_marker M 0 (y,t) ) he ) ( PhasePair.initial M _ ) ( fun _ _=> rfl ) ⟩
include simple
lemma heat_vote : π p (fun p=> ∫ k:P,panel (axis d) t p k K E A∂μ)=
         ((8:ℝ)*Z p*Ω p) • ( (β+α*Wξ t p) • FourierGaussian.bias d t + α • FourierGaussian.wind d t):= by
    have he p:= panel_int p A ( sat_k (axis d) t M v y |>.1 ); simp_rw [ ← show ∀ p, (∫ k, π k (fun k=> panel (axis d) t p k K E A) ∂μ)=(∫ k,panel (axis d) t p k K E A∂μ) from fun p=> TwoGrid.count_int (he p) ]; rw [ TwoGrid.costs_mean _ (fun p k=>π k (fun k=>panel (axis d) t p k K E A)) (fun p=> rotate_int (he p)) ]; simp_rw [ mean_v t p _ A M simple v y, integral_smul ]; rw [ integral_add (show Integrable (fun k=> (β+α*Wξ t p) • FourierGaussian.dot d t k) μ from ( FourierGaussian.dot_int d t ).smul (β+α*Wξ t p)) (show Integrable (fun k=> α • FourierGaussian.bonus d t k) μ from (FourierGaussian.wind_int d t).smul α), integral_smul,integral_smul ]; rfl
omit simple
abbrev plateZ (X p:P):ℂ:= (↑( (8:ℝ)*Z p*Ω p ):ℂ)*( τ X p+τ X (-p) )
omit M y
lemma plate_even : plateZ X (-p)=plateZ X p:= by unfold plateZ; rw [AxisChoice.dial_neg,neg_neg,add_comm (τ X _),Landau.sq_neg]
lemma panel0_sum : (∫ k:P,panel (axis d) t p k E E A∂μ)=((8:ℝ)* Z p*Ω p) • FourierGaussian.bias d t:= by simp_rw [heat0]; rw [integral_smul]; rfl
include M y
lemma ground_panel : κZ ( Cabin (a) (Φ t) μ E E ) p A=plateZ (a) p * FourierGaussian.bias d t:= by
    rw [ soldier _ _ (sat_g (axis d) _ M y) (Or.inl rfl) ]; unfold plateZ screen; simp_rw [ panel0_sum, Landau.sq_neg, AxisChoice.dial_neg, Complex.real_smul ]; ring -- implicit M y need include
lemma mean_lead : π p (fun p=> κZ ( Cabin (a) (Φ t) μ E E ) p A)=plateZ (a) p*FourierGaussian.bias d t:= TwoGrid.uniform (fun i=>by rw [ground_panel t _ A M y]; unfold plateZ; simp_rw [trcB,trcD,trcF,← trcN,trcF])
omit M y in
lemma combine (p:P)(f g: P→ℂ): π p (fun p=> f p+g p)=π p f+π p g:= map_add (π p) ..
include simple
lemma delta_X : π p (fun p=>κZ ( Cabin (a) (Φ t) μ K E ) p A) =
         plateZ (a) p * ( (β+α*Wξ t p) • FourierGaussian.bias d t + α • FourierGaussian.wind d t ):= by
    simp_rw [ soldier _ A (sat_k (a) t M v y|>.1) ( Or.inr rfl ) ]; rw [ combine, TwoGrid.antip (f:=fun p=>screen (a) t K E p A) p ]; unfold plateZ screen
    simp_rw [TwoGrid.currency (f:=fun p=> Tone.bill (axis d) p) (trcF d _) _, heat_vote _ _ A M simple ]; simp_rw [ Complex.real_smul, Landau.sq_neg, AxisChoice.dial_neg ]; unfold PhasePair.rate; rw [ PhasePair.rate_neg ]; ring
lemma delta_Y : κZ ( Cabin (a) (Φ t) μ E K ) p A=κZ (Cabin (a) (Φ t) μ K E) p A:= by
    rw [ soldier p _ ( sat_k (a) t M v y|>.2 ) ( Or.inl rfl ), soldier p _ ( sat_k (a) t M v y|>.1 ) ( Or.inr rfl ) ]; unfold screen; simp_rw [ flipP (X:=a) _ _ A ( PanelE.shift t A M simple v y) ]; -- notations
end val
end
end YM.SignedWilsonExpansion.PanelE
