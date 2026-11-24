import YM.SignedWilsonExpansion.Grid.Mercy
import YM.SignedWilsonExpansion.Radial
namespace YM.SignedWilsonExpansion.Overlap.Curtain
/-! angular quadrature at the mixed-mark port. First symmetrize the part of
this mark price; needn't average every tensor component. Uses three shifts cutting
three pair partitions, four deck moves rotating the pair. Residual cubic (signed permutation invariant) anisotropic
weight W4 removed by one 45-degree move and another partial sym. Total = 12²
(rotates integrable mark price at radial shell). No convergence
assumptions on individual monomial split.-/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Outlook MS.Emit MS.Heat MS.Rake
open MS.Garment MS.Motif MS.Halo MS.Arts MS.Tone MS.City
open FVA2 FVA2.Lambda Area Walk Bubble TreeLine TreeView HighRank HighScale MarkRows AxisChoice
open Gaussian Radial
open scoped Classical Topology ContDiff BigOperators
local notation "Z" => Momentum.sq
local notation "F" => FourP
local notation "A" => Axis
local notation "μ" => covMeasure Axis
local notation "Ψ" => Equiv.Perm Axis

def receive (σ:Ψ)(p:F) : F:= fun i=>p (σ i)
lemma receiveP (σ:Ψ) : receive σ=MeasurableEquiv.piCongrLeft (fun _=>ℝ) σ.symm:= by
    funext k i; unfold receive; obtain ⟨i,rfl⟩:= σ.symm.surjective i; rw [σ.apply_symm_apply, MeasurableEquiv.piCongrLeft_apply_apply]
lemma sameM (σ:Ψ) : MeasurePreserving (receive σ) μ μ := by
    let U:= MeasurableEquiv.piCongrLeft (fun _=>ℝ) σ.symm; rw [receiveP]; obtain he:= volume_measurePreserving_piCongrLeft (fun _=>ℝ) σ.symm
    refine ⟨ he.measurable,?_ ⟩; rw [show μ=( ENNReal.ofReal capμ ) • volume from Gaussian.land, Measure.map_smul, he.map_eq]
lemma receiveE (σ:Ψ) : MeasurableEmbedding (receive σ):= by rw [receiveP]; exact (MeasurableEquiv.piCongrLeft _ _).measurableEmbedding
lemma permute_sq (σ:Ψ)(p:F): Z (receive σ p)=Z p:= Equiv.sum_comp σ (fun i:A=> p i^2)
-- swap and compositions geometry
abbrev klein : Fin 4→ Ψ := ![
   Equiv.refl _,( Equiv.swap 0 1 ).trans ( Equiv.swap 2 3 ),(Equiv.swap 0 2).trans (Equiv.swap 1 3), (Equiv.swap 0 3).trans ( Equiv.swap 1 2 )
 ]
abbrev shiftS : Fin 3→Ψ := ![Equiv.refl _,Equiv.swap 1 2,Equiv.swap 1 3]
abbrev rail (j:Fin 3)(i:Fin 4) : Ψ:= ( klein i ).trans (shiftS j)
lemma foldab (j:Fin 3)(i:Fin 4)(p:F): receive (rail j i) p= receive (klein i) (receive (shiftS j) p):=rfl
lemma Q3 (f: Fin 3→ℝ): ∑ i,f i=f 0+f 1+f 2:= Fin.sum_univ_three ..

def meet (p:F)(v:FourP→ℝ):ℝ:= ∑ j:Fin 3, ∑ i: Axis,v (receive (rail j i) p)
variable (p:F)
lemma meet_plus (u v:F→ℝ) : meet p (fun x=>u x+v x)=meet p u+meet p v:= by unfold meet; simp_rw [ Finset.sum_add_distrib ]
lemma meet_coin (c:ℝ)(v:F→ℝ): meet p (fun x=>c*v x)=c*meet p v:= by unfold meet; simp_rw [ Finset.mul_sum ]
lemma meet_const (c:ℝ): meet p (fun _=>c)=12*c:= by unfold meet; rw [Q3]; simp_rw [qAxis]; ring
lemma meet_radius {q f:F→ℝ} (h:∀ k:F,Z k=Z p→ q k=f k): meet p q=meet p f:= by unfold meet; exact Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun i _=> h _ (permute_sq _ _)
lemma holder (σ:Fin 4)(j:A){p:F}{i:A}(he: klein σ j=i): receive (klein σ) p j=p i:=congr_arg p he
-- Klein (4), rotate through all indices. Need cost at AB and CD

set_option maxHeartbeats 400000 in
lemma seatK (j:A): (∑ i:A,( receive (klein i) p j )^2)=Z p:= by
   unfold Momentum.sq; rcases D4 j with rfl|rfl|rfl|rfl <;> simp (disch := decide) [qAxis,receive,klein,Equiv.swap_apply_def] <;> ring
abbrev duo (i j:A)(p:F): ℝ:= p i^2*p j^2
local notation "d" => duo 0 1
local notation "e" => duo 2 3
lemma coinAB : (∑ i:A,d (receive (klein i) p))=2*( d p+ e p ):= by simp (disch:=decide) [duo,receive,qAxis,klein,Equiv.swap_apply_def]; ring
lemma coinCD : (∑ i:A,e (receive (klein i) p))=2*( d p+ e p ):= by simp (disch:=decide) [duo,receive,qAxis,klein,Equiv.swap_apply_def]; ring
local notation "we" => receive
abbrev w4 (p:F):ℝ:= ∑ i:A,p i^4
lemma w4Sym (σ:Ψ)(p:F): w4 (receive σ p)=w4 p:= Equiv.sum_comp σ (fun i=>p i^4)
lemma priceAB : meet p d = (Z p)^2 - w4 p := by unfold meet; simp_rw [foldab,coinAB]; simp (disch:=decide) [Momentum.sq,duo,receive,w4,qAxis,shiftS, Q3,Equiv.swap_apply_def]; ring
lemma priceCD : meet p e= (Z p)^2 - w4 p:= by rw [← priceAB]; unfold meet; simp_rw [foldab, coinCD, coinAB]
lemma priceX (i:A): meet p (fun p=> p i^2)=3*Z p:=by unfold meet; simp_rw [ foldab, seatK,permute_sq ]; rw [ Q3 ]; ring
-- fixes unprojected mixed price salaryCross at radius Z
private abbrev ascii (h:ℝ→ℝ)(X L B C U W:ℝ):ℝ:=
   -- L B C first moments; U AB mixed, W CD. Replace (L+B+C) C by XC-W
   let f:= h X; let g:=deriv h X; let j:=deriv (deriv h) X
   (-32*X^3*f^2)*L + (-384*X^3*f^2-16*X*f-16*X^2*g)*B + (-64*X^3*f^2-64*X*f-64*X^2*g-64*X*X*g-32*X^3*j)*C+
     (96*X^2*f^2)*U + (64*X*g+32*X^2*j)*W
lemma read_salary (h:ℝ→ℝ) : salaryCross h p= ascii h (Z p) (p 0^2) (p 1^2) (p 2^2) (d p) (e p):= by
    simp only [salaryCross,ascii,duo]; generalize hx:Z p=X ; have hp:(∑ i:A,p i^2)=X:= hx; rw [qAxis] at hp
    linear_combination -(64*X*deriv h X+32*X^2*deriv (deriv h) X)*(p 2)^2*hp
private def around (h:ℝ→ℝ)(X W:ℝ):ℝ:= ascii h X (3*X) (3*X) (3*X) (X^2-W) (X^2-W)
lemma meet_salary (h:ℝ→ℝ): meet p (salaryCross h) = around h (Z p) (w4 p):= by
    apply Eq.trans (b:= meet p (fun q=>ascii h (Z p) (q 0^2) (q 1^2) (q 2^2) (d q) (e q))) (meet_radius p (fun k hk=> by rw [read_salary, hk])); unfold around
    simp only [ascii]; simp_rw [ meet_plus, meet_coin, priceX, priceAB, priceCD ] -- inspect simp_rw
-- protected move 45deg. Iso fourth eliminates after one.
local notation "T" => Radial.twist 2
lemma twist₄ : w4 (T p)= w4 p/2+3*( d p+ e p ):= by
    simp only [duo,w4,qAxis,u20,u21,u22,u23]; ring_nf; rw [power₄]; ring
lemma forth : meet p (fun k=> w4 (T k))= 6*(Z p)^2:= by
    have he : (fun k=> w4 ( T k ))= fun x:F=>(1/2:ℝ)*w4 x+3*(d x+e x):= funext (fun _=> by rw [twist₄]; ring)
    have hp : meet p w4=12*w4 p:= (Eq.trans (b:=meet p (fun _=>w4 p)) ?_ (meet_const p _) )
    · rw [ he, meet_plus,meet_coin, meet_coin, meet_plus,hp,priceAB,priceCD ]; ring
    · unfold meet; simp_rw [ w4Sym ]
private def meanQraw (h:ℝ→ℝ)(X:ℝ) :ℝ := around h X (X^2/2) / 12
def claim (h:ℝ→ℝ)(X:ℝ):ℝ:= -4*X^2*(87*X^2*(h X)^2+5*X^2*deriv (deriv h) X+25*X*deriv h X+15*h X)/3
lemma mean_claim (h:ℝ→ℝ)(X:ℝ): claim h X= meanQraw h X := by unfold claim meanQraw around ascii; ring
def west (h:ℝ→ℝ)(X:ℝ):ℝ:= around h X 1-around h X 0
lemma arena (h:ℝ→ℝ) (X W:ℝ): around h X W= around h X 0 + west h X * W := by unfold west around ascii; ring
lemma combine (h:ℝ→ℝ) : meet p (fun k=>meet (T k) (salaryCross h)) =144*claim h (Z p):= by
   rw [ show meet p _= meet p (fun k=> around h (Z p) 0+ west h (Z p)*w4 (T k)) from meet_radius (f:=fun k=> around h (Z p) 0 + west h (Z p)*w4 (T k)) p (fun k he=> ( by rw [meet_salary,Radial.same,he]; exact arena .. )) ]; rw [ meet_plus, meet_coin, meet_const,forth, mean_claim ]; unfold meanQraw; rw [ arena h (Z p) (Z p^2/2) ]; ring
-- actual normalized Haar-measure quadrature
abbrev I := Fin 3 × Fin 4
def pair (i j:I)(p:F): F:= receive (rail i.1 i.2) (T (receive (rail j.1 j.2) p))
lemma truePair (i j:I): MeasurePreserving (pair i j) μ μ:= (sameM _).comp ((money _).comp (sameM _))
lemma embedPair (i j:I): MeasurableEmbedding (pair i j):= (receiveE _).comp (( show MeasurableEmbedding (Radial.twist 2) from (Radial.LE 2).toHomeomorph.measurableEmbedding ).comp (receiveE _) )
lemma radiusPair (i j:I): Z (pair i j p)=Z p:= by unfold pair; rw [permute_sq, Radial.same,permute_sq]
lemma prices (h:ℝ→ℝ): ∑ j:I,∑ i:I,salaryCross h (pair i j p)=144*claim h ( Z p ) := by
    rw [ ← combine ]; unfold meet pair; simp_rw [Fintype.sum_prod_type]
variable {G:Gauge}{B:Land.Booked (Press.portDeck G)}(M: MS_Data G B)(η:G.Simple) (a:G.ColorIndex)(t:ℝ)
abbrev feeQ (G:Gauge)(t:ℝ)(p:F):ℂ:= ↑(G.casimir * Shells.hot t (Z p)*2*claim (amp t) (Z p))
lemma lock : ∑ j:I,∑ i:I,atBoth (pair i j p) G t=144*feeQ G t p:= by simp_rw [ atBoth,photo_cost,radiusPair p,← Complex.ofReal_sum,← Finset.mul_sum,prices p ]; unfold feeQ; push_cast; ring
include M η a
lemma rewarded : (∫ p, atBoth p G t∂μ) = ∫ p, feeQ G t p ∂μ:= by
    let v (i j:I) (p:F):ℂ:= atBoth (pair i j p) G t
    have hv (i j:I): Integrable (v i j) μ := (( truePair i j ).integrable_comp_emb (embedPair i j)).mpr ( budget_at t M η a )
    have hi(i j:I): (∫ p,v i j p∂μ)=(∫ p,atBoth p G t∂μ):= ( truePair i j ).integral_comp (embedPair i j) (fun p=> atBoth p G t)
    have he : (∫ p,∑ j:I,∑ i:I,v i j p∂μ)=∑ j:I,∑ i:I, ∫ p,v i j p∂μ := by
       have hu(j): Integrable (fun p=>∑ i:I, v i j p) μ:= integrable_finsetSum _ (fun i _=>hv i j)
       rw [ integral_finsetSum _ (fun i _=> hu i) ]; exact Finset.sum_congr rfl fun j _=> integral_finsetSum _ (fun i _=>hv i j)
    simp_rw [hi, show ∀ p, (∑ j:I,∑ i:I,v i j p)=144*feeQ G t p from fun p=> lock p t] at he; simp only [ Finset.sum_const, Finset.card_univ, I, Fintype.card_prod, Fintype.card_fin, integral_const_mul ] at he; linear_combination (-1/144:ℂ)*he
end
end YM.SignedWilsonExpansion.Overlap.Curtain
