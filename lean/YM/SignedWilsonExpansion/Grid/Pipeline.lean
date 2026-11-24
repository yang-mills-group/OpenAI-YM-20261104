import YM.SignedWilsonExpansion.Grid.Rim
namespace YM.SignedWilsonExpansion.Overlap.Realm
/-!  # Price/Pipeline: Fair spatial bracket. Mixed overlaps. Independent Cabins at rank-two probe and closed screen

Uses the unsmeared phase defined at time `axis`, with extant noncut vertices
on DOrd (not truncate estimates or boundary Ward modes). -/
set_option autoImplicit false
noncomputable section
open Function MeasureTheory Set Filter Finset
open MS MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.Plane.Wire MS.High MS.Tone MS.Land MS.Latch MS.Rake
open Energy (leg)
open FVA2 FVA2.Lambda Area HighRank HighScale Walk PhasePair FourierGaussian TwoGrid AxisChoice OrderHigh MassShift MarkShift
open PhasePair PairFlow Align PanelE Cohort Fair TreeLine Rim
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

variable {B: Land.Booked (Press.portDeck G)} (M:Land.MS_Data G B)(simple:G.Simple) (v y:ℝ)
local notation "T" => MarkShift.settled M N v (0,0)
local notation "K" => leap v (MarkRows.packet M N 2) (y,t)
local notation "α" => (v*OrderHigh.kinetic G)
local notation "β" => (v*Align.salaryQ G)
local notation "E'" => Energy.plane (degreeX (!m)) 2 G 0
-- mixed bare plane heat. Pointwise odd in k-product 01. Its angular cost 0,
-- also kills both frequency-cut rate multipliers before taking δ_P (outer μ).
def entry (k:P):ℝ:= k 0*k 1
local notation "ι" => entry
local notation "Q'" => Energy.leg (degreeX (!m)) 2
lemma twins : (∑ u:Axis,Q u p*Q' u p)= entry p := by rw [qAxis]; cases m <;> simp [entry,Align.degreeX, Energy.leg] ; ring
lemma bon : Rim.mixZD m E' k p A = (↑( ( (-2:ℝ)*entry k*entry p ):ℝ ):ℂ):= by
    unfold Rim.mixZD
    simp_rw [ Rim.fixedD (!m) ]; rw [← twins m k,← twins m p]; simp only [ Complex.real_smul ]; push_cast; simp_rw [ Finset.mul_sum, Finset.sum_mul ]; rw [ Finset.sum_comm ]; apply Finset.sum_congr rfl; intro i _; exact Finset.sum_congr rfl fun u _=> by ring
lemma star0 : π k (fun k=> Rim.mixZD m E' k p A)=0:= by
   simp_rw [ bon ]; rw [ show (fun k:P=>↑((-2:ℝ)*entry k*entry p))=(fun k:P=> ( (-2:ℂ)*↑(entry p)) * (entry k:ℂ) ) from (funext (fun _=> by push_cast; ring)), Fair.currency ( f:=fun _=>( (-2:ℂ)* ↑(entry p) )) (fun i=> rfl) (fun p=>↑(entry p)), show π k (fun p=> (( entry p:ℝ ):ℂ ))=0 from Fair.story_zero k,mul_zero ]
local notation "S" => (axis d)
include M y
lemma startPhase : SatP μ (Φ t) E' E X:=by
    have ht:= mark_permit t X ( Duet.walletQ M (!m) 0 (y,t) ) ( Duet.walletQ M m 0 (y,t) ); exact PanelE.alike X ht ( Duet.initialD M (!m) _ ) (Duet.initialD M m _)
-- ^ include/omit for SatP_s. make lemma

lemma evolve_X : κZ (Cabin (S) (Φ t) μ E' E) p A=0:= by
    obtain hm:= startPhase m (S) t M y; rw [ Rim.soldierD _ _ _ hm ( Or.inr rfl ) ]; unfold PanelE.screen; suffices ∀ p:P,(∫ k:P,panel (S) t p k E' E A∂μ)=0 by rw [ this,this,mul_zero,mul_zero,add_zero ]
    intro p; rw [ ← Fair.pack_int ( PanelE.panel_int p A hm ) ]; let f(p k:P):= ( (-4:ℂ)*τ (S) k * (↑( Z p* Z k *HOT ( Z k )):ℂ) ); have he(k:P): π k (fun k=>panel (S) t p k E' E A)=0:= by
       simp_rw [ Rim.panel_tD ]; rw [ Fair.currency ( f:=fun k=>f p k ) (c:= f p k ) ( fun i=>by unfold f; rw [ Fair.magπ,Fair.billπ ]) (fun k=> Rim.mixZD m E' k p A),star0,mul_zero ]; -- fixed
    simp_rw [he,integral_zero]
include simple
omit simple in
lemma evolve_mem : SatP μ (Φ t) K E X ∧ SatP μ (Φ t) E K X:= by
   have ht: K ∈ MS.Breeze.Wallet G:= ( MS.Breeze.Wallet G ).sub_mem ( Duet.walletQ M (!m) 2 ( y+v,t ) ) ( Duet.walletQ M (!m) 2 (y,t) ); have hu : MarkRows.packet M (Energy.called (degreeX m) 2 G ) 0 (y,t)∈ MS.Breeze.Wallet G:= Duet.walletQ M m 0 _
   have he:= Duet.initialD M m (y,t)
   exact ⟨ PanelE.alike X ( mark_permit t X ht hu ) (fun _ _=>rfl) he, PanelE.alike X ( mark_permit t X hu ht ) he (fun _ _=> rfl) ⟩
local notation "ℓ" => Fair.cost
lemma mixv_cost : π p (fun p=>π k (fun k=>Rim.mixZD m K k p A))= (↑( -2*β*ℓ k*ℓ p:ℝ ):ℂ):= by
   let u (p k:P):ℂ:= α*↑( ( Wξ t k + Wξ t p ):ℝ )
   have he(r:P): π k (fun k=>Rim.mixZD m K k r A)=π k (fun k=> Cohort.escrow m M v A k r):= by
      let f (r p:P):=Rim.mixZD m E' p r A
      have h(x:P) : Rim.mixZD m K x r A= Cohort.escrow m M v A x r + u r x*f r x:= by rw [ Rim.mixvD m t r x A M simple, Complex.real_smul ]; unfold f u; push_cast; rfl
      rw [ show (fun k=> Rim.mixZD m K k r A)= (fun k=>Cohort.escrow m M v A k r)+(fun k=> u r k*f r k ) from funext h, map_add, Fair.currency ( f:=fun k=>u r k ) (c:=u r k) ( fun i=>by unfold u PhasePair.rate PhasePair.rateV; simp_rw [Fair.magπ]) (fun k=>f r k) ]; unfold f; rw [star0,mul_zero,add_zero]
   simp_rw [ he ]; exact Cohort.counted p m M simple v A k
omit M y simple -- need omit?
def MV (d t:ℝ)(k:P):ℂ:=Tone.bill (axis d) k*(↑( Shells.hot t ( Z k )* Z k* Fair.cost k ):ℂ)
lemma polar : π k (FourierGaussian.dot d t)= MV d t k:= by
   let f(k:P):= τ (S) k* (↑( HOT ( Z k ) * Z k ):ℂ); have hu(k:P): FourierGaussian.dot d t k=f k*( Ω k :ℂ ):= by unfold FourierGaussian.dot f; push_cast; ring
   rw [ funext hu, Fair.currency ( f:=f ) (c:=f k) ( fun i=>by unfold f; simp_rw [ Fair.magπ,Fair.billπ ] ) (fun k=> ↑(Ω k)),Fair.saleV ]; unfold f MV; push_cast; ring
lemma mv_int : Integrable (MV d t) μ:= by rw [ show MV d t=(fun k=>π k (FourierGaussian.dot d t)) from (funext (fun k=> (polar (d:=d) t k).symm)) ]; exact Fair.price_int ( FourierGaussian.dot_int d t )
lemma costMV : (∫ k, MV d t k∂μ)= FourierGaussian.bias d t:= by simp_rw [ ← polar ]; exact Fair.pack_int ( FourierGaussian.dot_int d t )
include M y simple
lemma cost_panel : π p (fun p=>π k (fun k=> PanelE.panel (S) t p k K E A ))=
     (β*8*Z p*ℓ p:ℝ) • MV d t k:= by
   let f (p k:P):ℂ:= (-4:ℂ)*τ (S) k * (↑( Z p * Z k * HOT (Z k) ):ℂ); let g(p k:P):= Rim.mixZD m K k p A
   have hk(p:P): π k (fun k=> f p k*g p k)= f p k*π k (fun k=> g p k):= Fair.currency (f:=fun k=>f p k) (fun i=>by unfold f; simp_rw [Fair.magπ,Fair.billπ]) (fun k=>g p k)
   simp_rw [ Rim.panel_tD ]; change π p (fun p=>π k (fun k=> f p k*g p k))=_; simp_rw [hk]; rw [ Fair.currency (f:=fun p=> f p k) (c:=f p k) (fun i=>by unfold f; rw [ Fair.magπ ]) (fun p=>π k (fun k=>g p k)) ]; unfold g; rw [ mixv_cost m t p k A M simple v y ]; unfold MV f; rw [ Complex.real_smul ]; push_cast; ring
-- pay mean in both directions before derivative.
lemma price_panel : π p (fun p=>∫ k:P,panel (S) t p k K E A ∂μ)=(β*8*Z p*ℓ p:ℝ) • FourierGaussian.bias d t:=by
   have hp(p:P): Integrable (fun k=>panel (S) t p k K E A) μ:= panel_int p A (evolve_mem m (S) t M v y|>.1)
   simp_rw [ ← Fair.pack_int (hp _) ]; rw [ Fair.price_rote p _ (fun p=> Fair.price_int ( hp p )) ]; simp_rw [ cost_panel m t p _ A M simple v y, integral_smul, costMV ]
omit M simple y
def plateQ (X p:P):ℂ:= (8:ℂ)*↑(Z p)*↑(Fair.cost p)*( τ X p+τ X (-p) )
include M y simple
lemma forward : π p (fun p=>κZ (Cabin (S) (Φ t) μ K E) p A)= (plateQ (S) p)* (β • FourierGaussian.bias d t):= by
   simp_rw [ Rim.soldierD m _ A (evolve_mem m (S) t M v y|>.1) ( Or.inr rfl ) ]; rw [ show (∀ f g:P→ℂ, π p (fun p=>f p+g p)=π p f+π p g) from fun f g=> map_add (π p) f g, Fair.antipode p (fun p=>PanelE.screen (S) t K E p A) ]; unfold PanelE.screen
   have he(q:P) : π q (fun p=>τ (S) p * ∫ k,panel (S) t p k K E A ∂μ)= τ (S) q * ( (β*8*Z q*ℓ q:ℝ) • FourierGaussian.bias d t ):= by rw [ Fair.currency (f:=fun p=>τ (S) p) ( c:=τ (S) q ) (fun i=>Fair.billπ i q d) (fun p=> ∫ k,panel (S) t p k K E A ∂μ), price_panel m t q A M simple v y ]
   rw [he,he,Fair.costN,Landau.sq_neg]; unfold plateQ; simp_rw [ Complex.real_smul ]; push_cast; ring
lemma rear : κZ (Cabin (S) (Φ t) μ E K) p A= κZ (Cabin (S) (Φ t) μ K E) p A:= by
   rw [ Rim.soldierD _ _ _ ( evolve_mem m (S) t M v y|>.2 ) (Or.inl rfl), Rim.soldierD _ _ _ ( evolve_mem m (S) t M v y|>.1 ) (Or.inr rfl) ]; unfold PanelE.screen; simp_rw [ Rim.flipPD (X:=S) m _ _ A ( Rim.shiftLP m t A M simple v y) ]
end
end YM.SignedWilsonExpansion.Overlap.Realm
