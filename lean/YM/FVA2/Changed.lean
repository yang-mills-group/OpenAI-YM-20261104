import YM.FVA2.MarketJet
/-!
# Exact ms-body comparison identities. Bare operation D ties converted columns. Includes actual center convention.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option quotPrecheck false
namespace YM.FVA2.WorldJet
open Function Filter Set MeasureTheory
open Pert Pert.Position Maxwell Maxwell.Free PositionX
open PositionX.Jet
open Wilson Lattice Gauge PertExtension PertExtension.Chart
open PertExtension.LatticePT RG FormalOPE.RG10 FormalOPE.RG10.BlockGauge FormalOPE.RG10.MultiGauge FormalOPE.RG10.InversionTop
open MS MS.Menus MS.Land MS.Theater MS.Book MS.Book.Program MS.Book.Convolve
open Clock Score Based PairCoords Modes Paper Trans ColorCode Attend BoxOffice Counterpart Blaze Frost ArchTurn
open PowerSeries
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} (V:Warehouse G)(P:Land.Prescription (wings G))(H:ExactSpin V P)(HI:Trusted P) {sx:ℝ} {x:ℝ} (hl:sx≠0)
    {n m d:ℕ} (i:Owner G d){U J:Type} {N:Side}
local notation "F"=> V.F
local notation "Tt"=> E V.F d
local notation "αV" t "/" k "#" d=> bareReset V P t k H HI d -- missing x.Strength? edit
local notation "ε"=> sx
local notation "θ"=>x
local notation "κψ"=> PairCoords.φ (U:=U) (J:=J)
abbrev posesD (ε₀ η₀: ℝ) (d:ℕ) := fun i=> bareReset V P ε₀ η₀ i H HI d
local notation "Ω"=> posesD V P H HI ε θ d
local notation "pC"=>baring V.F d
local notation "κA"=>sameAxis V.F d
section iso
-- formula for A.Coeff Psalm in any horizon projected.From V,B. exact.Lift Price. launch.Lattice sum.
variable (v:Site N)(b:Module.Basis U ℝ (Wilson.Field G N))
private lemma Price_coord (k:ℕ)(i: Glyph (wings G) d)(p:Owner G d): coeff k ( style V.F Ω κA i (κA (Land.read p))) = rateV P sx x k p i := by
   rw [ ← out_coeff, node4, frame_projects, D_own, loadAt,factory,map_sum, Finset.sum_eq_single_of_mem i (Finset.mem_univ _) ]; · simp
   intro j _ h; simp [h]
lemma price_visible (i:Glyph (wings G) d)(z:Owner G d) : style V.F Ω κA i (κA (Land.read z))= PowerSeries.C ( factorEF sx d i.size )* into (Channel.credits i x (P.fees d z)) := by apply PowerSeries.ext; intro k; rw [ Price_coord,coeff_C_mul, into_coeff, Channel.credits,coeff_mk ]; rfl
variable (p:Team)
local notation "W"=> warp κψ (shift p x) (share p x)
local notation "δ"=> velvet V b v ε d
lemma pricing (k:ℂ)(F1:Cn) : k • F1 = PowerSeries.C k * F1:= PowerSeries.ext fun i=>by rw [ coeff_smul, coeff_C_mul ]; rfl
include hl
-- response conversion, use coordinate d exactly but sum reduce to Common.avoid Fintype univ mismatch.
lemma acted (m:ℕ)(i:Owner G m)(he:m≤d) : (∑ j:Glyph (wings G) d,currency κψ (style F Ω κA j (up F he (sameAxis F m (Land.read i)))) * W (δ (κA j)) )= ((ε:ℂ)^m)⁻¹ • Track.lantern V b v p x (P.fees m i) := by
    -- compare via expanding at each j using inclusion and coeff-sum.Comp.B col
    let M:= sameAxis F m; let t:=M (Land.read i); let ℓ:=up F he; let Z:=velvet V (J:=J) b v ε m; let Y j:=style F (posesD V P H HI ε x m) M j t
    have ht(j:Glyph (wings G) d): style F Ω κA j (up F he (sameAxis F m (Land.read i))) = ∑ k:Glyph (wings G) m, ((κA).coord j (ℓ (M k))) • (Y k):= by
        apply reserve; funext r; rw [map_sum, Finset.sum_apply,node4,frame_projects, D_link ]; rw [show bareD V _ _ _ _ _ (sameAxis F m _)= _ from Eq.symm (M.sum_repr (bareD V P sx x r m t)), map_sum,map_sum ]; refine Finset.sum_congr rfl (fun i _=>?_ ); rw [ map_smul, map_smul, map_smul ]; -- wrong order
        simp only [Y,node4, frame_projects,Pi.smul_apply,smul_eq_mul]; exact mul_comm ..
    let f(k:Glyph (wings G) m):= ℓ (M k); simp_rw [ht, map_sum, Finset.sum_mul ]; rw [ Finset.sum_comm, launched V b v ε p x hl ]; refine Finset.sum_congr rfl fun k _=>?_ ;
    rw [show (PowerSeries.C _ * into (Channel.credits _ _ _)) = Y k from (price_visible V P H HI (d:=m) k i).symm ]; simp_rw [ pricing, map_mul, mul_comm ( currency κψ (PowerSeries.C _) ) (currency κψ (Y k)),mul_assoc,currency_c, ← Finset.mul_sum ]; apply congr_arg; simp_rw [ ← warp_t (A:=_) , ← map_sum ]; -- warp_t lemma namespace fields.A?
    apply congr_arg; simp_rw [ ← map_smul, ← map_sum ]; rw [show (∑ x: Glyph (wings G) d, ((sameAxis V.F d).coord x) (ℓ (M k)) • sameAxis V.F d x)=ℓ (M k) from (κA).sum_repr _ ]; exact velvet_scale ..
end iso
section point
variable (A:Lattice.Cover)(c:Fin n→Lattice.Cover)
variable [Fintype U][Fintype J][DecidableEq J] (he:Even N.val)(b:Module.Basis U ℝ (Wilson.Field G N))(g:Module.Basis J ℝ (Param G N))
local notation "Tt"=> P.team
local notation "W"=> unmarked b g
local notation "η"=> Currency b he (J:=J)
local notation "ζ"=> warp κψ (shift Tt x) ( share Tt x )
local notation "Ξ"=> Attend.guide η W
local notation "M"=> Attend.guide η ( ζ W )
local notation "φ"=> shift Tt x
local notation "X'"=> stencil φ
local notation "σ"=> BoxOffice.view
local notation "πZ"=> Channel.coord N A c

def altered (v: Fin n→ Site N)(d:ℕ): Court (E V.F d) n Cn:= drag F (posesD V P H HI sx x d) (sameAxis F d) (( X' ).compMultilinearMap (BoxOffice.view V he b g ε v d))
variable (w:Fin n→BasisIx G d)
def look (w: Fin n→BasisIx G d)(i:Fin n): Acts (wings G) (Glyph.size (w i)):=P.fees (w i).size (w i).2
local notation "τ"=> ( Glyph.size ∘ w )
local notation "ρ" t => (↑ε:ℂ)^t
local notation "bF"=> bareReset V P -- unused
include hl
-- launch identity, then smear. `A` not analytic assumption
lemma alters (j:ℕ) : out (altered (x:=θ) (sx:= sx) V P H HI he b g πZ d (κA ∘ w)) j = (∏ i:Fin n,(ρ (τ i))⁻¹) * netE (Track.ticketRead V N (Glyph.size ∘ w) Tt x (look P w) A c Finset.univ) j := by
   unfold altered; rw [ atDrag ];
   let t := into (Track.ticketRead V N τ Tt x (look P w) A c Finset.univ ); let u:ℂ:= ∏ i:Fin n,(ρ (τ i))⁻¹;
   have hr : u • t= M (∏ i:Fin n,(ρ (τ i))⁻¹ • Track.lantern V b (J:=J) (πZ i) Tt x ((look P w) i) ):= by
       rw [ ← MultilinearMap.mkPiAlgebra_apply (R:=ℂ), MultilinearMap.map_smul_univ (m:=fun i=> Track.lantern V b (J:=J) (πZ i) Tt x ((look P w) i)) , map_smul ]; unfold t; rw [ sealFrom (he:=he) (b:=b) (g:=g) ]; rfl
   change _=u*(netE _ j); rw [Clock.out_real ];
   have hv (i:Fin n):=(acted V P H HI hl (πZ i) b (J:=J) (x:=x) P.team (Glyph.size (w i)) (w i).2 (not_under ( w i )));
   have hx (k: Fin n) : (ρ (τ k))⁻¹ • Track.lantern V b (J:=J) (πZ k) Tt x ((look P w) k)=∑ i: Glyph (wings G) d,currency κψ (style F Ω κA i ((κA ∘ w) k)) * ζ (velvet V b (πZ k) ε d (κA i)):= by
       change (ρ (Glyph.size (w k)))⁻¹ • Track.lantern V b (J:=J) (πZ k) Tt x (P.fees _ (w k).2)=_; rw [← hv k, same_up ]; rfl
   rw [ show u * Clock.out t j = Clock.out (u • t) j from Eq.symm (congr_fun ( map_smul Clock.out u t ) j),hr ]; simp_rw [hx]; apply congr_arg (fun z:Cn=> Clock.out z j); rw [ Fintype.prod_sum,map_sum ];
   refine Finset.sum_congr rfl fun i hi=> ?_; rw [ Finset.prod_mul_distrib, ← map_prod, ← map_prod ]; -- ad hoc instances
   rw [ funding η (ζ W) _, commuting η W ( hungry g b) ]; swap; rw [warp_acts, Program.pay0,hungry g b ]; rfl -- placeholder proof. maybe close
end point
variable (q:ℕ+)(m:ℕ)
abbrev ζq (p: Team)(x:ℝ) (j:ℕ):= coeff j (Clock.rate p x)
abbrev hall (ε₀ η₀:ℝ)(d:ℕ) : Word (Buffer V.F d):= posesD V P H HI ε₀ η₀ d
-- on shell before frame/coupling changes (q not a clock). V'=Shop of warehouse
abbrev shop₀ := BoxOffice.warehouse V
def bankOne (x:ℝ)(d:ℕ) := ren (ζq P.team x) ( (shop₀ V).bank q m d )
def changedWorld (x:ℝ) (d:ℕ) := predMarket (hall V P H HI (epsilon q m) x d) (bankOne V P q m x d)
local notation "L" => LatticePT.side q m
local notation "ϵ"=> LatticePT.epsilon q m
variable (x:ℝ) [Fintype U][Fintype J][DecidableEq J]
    (b:Module.Basis U ℝ (Wilson.Field G (LatticePT.side q m)))(g:Module.Basis J ℝ (Param G (LatticePT.side q m)))
    (v:Test n) (Z:Fin n→ E V.F d)
local notation "X'"=> stencil ( shift P.team x )
local notation "JΩ"=> hall V P H HI ϵ x d
lemma priceMovie (j:ℕ) : JetB F (bankOne V P q m x d j) ((X').compMultilinearMap ( shelter V q m b g d v )) v j := by
    ext1 p; let l:= lookie F ⟨n,p,v⟩; change l (ren _ _ _)=Clock.out (X' (shelter _ _ _ _ _ _ _ _) ) _; rw [ ren_clock ]; apply Eq.trans (congr_fun (ren_writes l _ _) j); obtain he: (l ∘ (shop₀ V).bank q m d)= Clock.out ( shelter V q m b g d v p ):= funext (fun i=> sheltered V v q m b g _ i); rw [he]
lemma subleading0 (P:Team)(w:Word (Bank F d)) : ren (ζq P x) w 0= w 0:= by
   funext n t; ext1 p; let L₀:= lookie F (d:=d) ⟨ n,p,t ⟩; exact (congr_fun (ren_writes L₀ (ζq P x) w) 0).trans ( Jet.ren_light (show light (ζq P x) from Clock.rooted P x) (V:=ℂ) _ )
lemma dawn (x:ℝ): changedWorld V P H HI q m x d 0= market F (bareReset V P ϵ x 0 H HI d) ( (BoxOffice.warehouse V).bank q m d 0 ) := by rw [changedWorld,pred_zero,bankOne,subleading0 ]; -- args.check
lemma plotE (j:ℕ) : (changedWorld V P H HI q m x d j n v) Z = coeff j ( ∑ z:Fin n→ Site L,∑ i∈ origins q m,(zoneμ q m z v * (((ϵ:ℂ)^4)^n)) • altered V P H HI (x:=x) (sx:=ϵ) ( side_even q m ) b g (fun i'=> z i'+i) d Z ) := by
   unfold changedWorld; rw [← drag_h F _ (sameAxis F d) v _ Z ( priceMovie V P q m x b g v ) j ]; unfold altered; apply congr_arg (coeff j); simp_rw [atDrag]; simp_rw [ LinearMap.compMultilinearMap_apply, tends V v q m b g, map_sum, map_smul, Finset.mul_sum, Finset.smul_sum, mul_smul_comm ]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro w _; rw [ Finset.sum_comm ]
end YM.FVA2.WorldJet
