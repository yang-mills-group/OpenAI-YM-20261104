import YM.SignedWilsonExpansion.MaskFoot
namespace YM.SignedWilsonExpansion.PhasePair
/-! # Contracting mark normalization and charge (continued vertices)

Use true factor `W`, obtained on the *amp* heat primitive. The high stamp perturbative insertion cost is through
 **one** normalized Ward deformation, on oriented operands before closing the shell. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Outlook MS.Emit MS.Heat MS.Rake MS.Theater
open MS.Garment MS.Motif MS.Halo MS.Arts MS.Tone MS.City
open MS.Puff MS.Osc MS.Osc.Snap MS.Latch MS.Latch.Job MS.Rake.Geo MS.Rake MS.Rock MS.Rock.Path MS.Breeze MS.Vane
open FVA2 TreeView HighRank HighScale MarkRows MassShift MarkShift Walk TreeLine
open FVA2.Lambda Area Shells
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}
local notation "Φ" => (PlanetD G)
local notation "μ" => covMeasure Axis
local notation "Ψ" => field (P:=FourP) (Landau.parity (A:=Axis) (C:=G.ColorIndex))
variable {K:Booked (Press.portDeck G)}(M:MS_Data G K)(simple:G.Simple)
local notation "E" => Energy.plane 1 2 G 0
local notation "η" => Energy.called 1 2 G
local notation "Hκ" => packet M η
local notation "V" => leap
variable (v:ℝ)
local notation "L" => wall M v -- ambiguous
local notation "α" => v*OrderHigh.kinetic G
local notation "β" => v*OrderHigh.locus G
local notation "Z" => Momentum.sq
local notation "MK" => (v* OrderHigh.kinetic G)
local notation "Fκ" => settled M η v (0,0)
abbrev rateV (h:ℝ→ℝ)(p:QP): ℝ:= 2*h p.sq*p.sq^2
abbrev rate (t:ℝ)(p:QP):= rateV (amp t) p
lemma gain (p:QP)(t:ℝ): HasDerivAt (fun t=>PhasePair.rate t p) (rateV (hot t) p) t:= by
    convert! ( ( ( amp_deriv t p.sq ).const_mul 2 ).mul_const (p.sq^2) ) using 1; unfold hot rateV; ring_nf
lemma rate_neg (h:ℝ→ℝ)(p:QP): rateV h (-p)=rateV h p:= by unfold rateV; rw [Landau.sq_neg]
lemma definition (p:QP)(t:ℝ): rate t p=1-(1+Real.exp t^2*p.sq)*Real.exp (- (Real.exp t^2*p.sq)):= by
    let r:=Real.exp t; let f(x:ℝ):= -(1+x*p.sq)*Real.exp (- (x*p.sq))
    have hp(x:ℝ): HasDerivAt f ( src (x,p.sq)*(2*p.sq^2) ) x:= by
        let L':= ( hasDerivAt_id' x ).mul_const p.sq
        convert! ( ( ( L'.const_add 1 ).neg).fun_mul (L'.neg.exp) ) using 1; unfold src; simp only [Pi.neg_apply]; ring
    unfold rate rateV amp TreeLine.gain desk; rw [ show 2 *_ * _ = ∫ x:ℝ in 0..( Real.exp t ^ (2:ℕ) ), src (x,p.sq)*(2*p.sq^2) from ?_, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun i _=>hp i) ( Continuous.intervalIntegrable ( show Continuous (fun x:ℝ=> src (x,p.sq) * ( 2*p.sq^2) ) from by unfold src; fun_prop) _ _ ) ]; · unfold f; simp only [zero_mul,add_zero,neg_zero,Real.exp_zero]; ring
    rw [ intervalIntegral.integral_mul_const ]; ring

variable {a b i j k : Axis}{A B Cc:G.ColorIndex}{p q r:QP}
include simple
lemma opening : ∃ b:ℝ, Agrees L (ranktwo (G:=G) (v*OrderHigh.kinetic G) b):= by
   obtain ⟨b,h⟩:=OrderHigh.propagation_E M simple v; refine ⟨b,?_⟩; intro w hw; by_cases he:w.length=0; · rw [List.length_eq_zero_iff.mp he]; rw [MarkShift.wall, Book.strange _ (by simp) ]; rfl
   rw [ ←h ( 0,0 ) w (fun _=> hw) (by omega), ←token M simple v (0,0) w (by omega) hw ]
lemma steady (h:ℝ→ℝ)(x:Legs (Lane4 G))(F:Law G):
    R G h L F [W i A p] x=∑ j:Axis, ((2* OrderHigh.kinetic G*v*h p.sq*p.sq* precision i j p:ℝ):ℂ)* F ( W j A p :: x ) := by
    obtain ⟨c,he⟩:= opening M simple v
    rw [Walk.chart,Area.contact L F h (-p) _ _ (by simp [W,qnote,net]), Walk.starLine]; simp only [neg_neg]
    have ht (k:Branch G Axis): L [(k,-p), W i A p]=ranktwo (G:=G) MK c [(k,-p), W i A p]:= he _ (by simp [net,W,qnote])
    simp_rw [ ht ]; simp only [ranktwo,W,qnote,Area.U₀,C₀,W₀, kinds, mul_ite,ite_mul, mul_zero,zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero] -- table may need local
    have he' (l:Axis)(a:G.ColorIndex): parity (Landau.gauge l,a)=false:= rfl
    simp only [ he',cross_false,one_mul,ite_self,add_zero ]; rw [ Finset.sum_eq_single_of_mem A (Finset.mem_univ A) ]; -- syntax
    · simp only [ ↓reduceIte,bond,k_even,Landau.sq_neg,Finset.mul_sum ]; rw [ Finset.sum_comm ]; refine Finset.sum_congr rfl fun k _=>?_
      rw [show 2*OrderHigh.kinetic G*v*h (Z p)* Z p*precision i k p= (2*OrderHigh.kinetic G*v*h (Z p))*(∑ x:Axis, precision i x p*precision x k p) from (by rw [ k_times ]; ring) ]; push_cast; simp_rw [ Finset.mul_sum, Finset.sum_mul ]; apply Finset.sum_congr rfl; intro a _; rw [realK i a]; ring
    intro j _ h; simp [h]

abbrev κZ (F:Law G) (p:QP)(k: G.ColorIndex):= ∑ i:Axis,∑ j:Axis,(precision i j p:ℂ)*F [ W i k p,W j k (-p) ]
lemma du (h:ℝ→ℝ)(F:Law G)(x y:Lane4 G): tree parity (lineL G h) L F [x,y]=R G h L F [x] [y]+cross (Ψ x) (Ψ y)*R G h L F [y] [x]:= by
   change scatter Ψ [x,y] (R G h L F)=_
   simp only [scatter_cons,scatter_nil]; have ht(l r:Legs (Lane4 G))(hz:l.length≠1): R G h L F l r=0:= by unfold R Flux.attaches; have he(i:Lane4 G): L (i::l)=0:= Book.strange _ (by simp; omega); simp [ he ]
   rw [ht [x,y] [] (by simp),ht [] _ (by simp)]; simp; abel
lemma carried (h:ℝ→ℝ)(p q:QP)(F:Law G):
    Flux.tree parity (lineL G h) L F [ W i A p,W j B q ]=
       ∑ a:Axis,((( 2*OrderHigh.kinetic G*v*h p.sq*p.sq*precision i a p:ℝ):ℂ) * F [ W a A p,W j B q ]+
         ((2*OrderHigh.kinetic G*v*h q.sq*q.sq*precision j a q:ℝ):ℂ)* F [ W a B q,W i A p ]) := by
   rw [du M simple, steady M simple, steady M simple, show cross (Ψ _) (Ψ _ )=(1:ℂ) from rfl]; simp [ Finset.sum_add_distrib ]
-- In `carried`, second term F with arguments reversed. For trc projection use BOTH oriented traces.
lemma legs (t:ℝ) (i j:Axis)(p q:QP)(A:G.ColorIndex):
    MarkShift.bridge M η v t [ W i A p,W j A q ]=
       (↑(α * (rate t p+rate t q)):ℂ)* E [ W i A p,W j A q ]:= by
    unfold MarkShift.bridge; rw [ Walk.ampL, Energy.found, carried M simple ]; simp only [Finset.sum_add_distrib,peel, ↓reduceIte, ← Complex.ofReal_mul, ← Complex.ofReal_sum, ← Complex.ofReal_add ]
    have hx (u:Axis)(p:QP)(q:QP)(j:Axis): E [W u A p, W j A q]= (( ( (-2:ℝ)*Energy.leg 1 2 u p*Energy.leg 1 2 j q):ℝ):ℂ):= by rw [ Walk.peel,if_pos rfl ]
    simp_rw [ hx, ← Complex.ofReal_mul, ← Complex.ofReal_sum, ← Complex.ofReal_add ]; apply congr_arg
    let B:=OrderHigh.kinetic G
    have he (p q:QP)(i j:Axis): (∑ k:Axis, (2*B*v*amp t p.sq*p.sq*precision i k p) * ( (-2*Energy.leg 1 2 k p)* Energy.leg 1 2 j q))= 2*B*v*p.sq*( p.sq*amp t p.sq *Energy.leg 1 2 i p)*(-2*Energy.leg 1 2 j q):= by
       rw [← Walk.projection (amp t)]; simp_rw [ Finset.mul_sum, Finset.sum_mul ]; apply Finset.sum_congr rfl; intro k _; unfold bond; ring
    unfold B at he; rw [ he p, he q ]; unfold rate rateV; ring

lemma kinetic_contract (h:ℝ→ℝ)(p:QP)(F:Law G)(A:G.ColorIndex):
    κZ (Flux.tree parity (lineL G h) L F ) p A =
       (↑( MK * rateV h p):ℂ)*( κZ F p A+κZ F (-p) A ):= by
    let f(i j a:Axis)(p:QP):ℂ:= (↑(2*OrderHigh.kinetic G*v*h p.sq*p.sq*precision i a p):ℂ)*F [ W a A p,W j A (-p) ]
    have ht(i j:Axis): Flux.tree parity (lineL G h) L F [W i A p,W j A (-p)] = (∑ a:Axis,f i j a p)+(∑ a:Axis,f j i a (-p)):= by rw [ carried M simple,Finset.sum_add_distrib ]; unfold f; simp_rw [neg_neg]
    have hv(p:QP) : (∑ i:Axis,∑ j:Axis,( precision i j p:ℂ )*∑ a:Axis,f i j a p)=(↑(MK*rateV h p):ℂ)* κZ F p A:= by
       conv_lhs=> rw [Finset.sum_comm]
       unfold κZ
       conv_rhs=> arg 2; rw [Finset.sum_comm]
       simp_rw [ Finset.mul_sum ]; apply Finset.sum_congr rfl; intro j _; rw [ Finset.sum_comm ]; apply Finset.sum_congr rfl; intro a _
       have he: ∑ i:Axis, (precision i j p:ℂ)*(precision i a p:ℂ)= ((p.sq:ℝ):ℂ)*( precision a j p:ℂ ):= by
          simp_rw [ ← Complex.ofReal_mul, ← Complex.ofReal_sum,realK _ a, mul_comm (precision _ j _), k_times ]
       let C:= ((↑(2*MK*h p.sq*p.sq):ℂ)*F [W a A p,W j A (-p)])
       rw [ show ↑(MK*rateV h p)*(( ↑(precision a j p):ℂ )*F [W a A p,W j A (-p)])= C *( (p.sq:ℂ)*(precision a j p:ℂ) ) from (by unfold C rateV; push_cast; ring), ← he, Finset.mul_sum ]; exact Finset.sum_congr rfl fun i _=> by unfold C f; push_cast; ring
    rw [κZ]; simp_rw [ ht,mul_add, Finset.sum_add_distrib ]; rw [ hv ]; congr 1; conv_lhs=> rw [ Finset.sum_comm ]
    trans ((↑(MK*rateV h (-p)):ℂ)*κZ F (-p) A); swap; · rw [rate_neg]
    rw [← hv]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; rw [Landau.k_even, Landau.realK j i p]
end
end YM.SignedWilsonExpansion.PhasePair
