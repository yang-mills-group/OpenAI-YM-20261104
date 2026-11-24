import YM.LocalLTE.Ballot.Pulse
import YM.LocalLTE.Dilation.Silhouette
import YM.LocalLTE.Port.Gems
/-! Root skeleton bill with independent coefficients, permits at true Path not homogeneous marker. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open FrameBox Pastel Merge Merge.Palette

open Merge.Palette Gas Ursell Bakers
open Greenbelt
set_option quotPrecheck false
attribute [local instance] Gauge.frobInner
variable {ι:Type}(M:ι → Lotus.Leaf R) (φ:ι→ Config G f→ℝ) (H:Cash W t μ L Q o a T R)(χ:Chi)
-- Every label.Energy in θ ledger same geometry.T.Z.T.Tag projection Ward.
local notation "Oz"=> Merge.Tickets (Merge.Palette.sign M S)
local notation "Y₀"=> radiusB t
variable (z:H.fragrances)(D:Captain.Oscars M z) {θ ι' J:ℕ}
local notation "Ux"=> (fun k=> z.snd k)
local notation "U₀"=> Captain.reachability (H:=H) z
local notation "M₀"=> (fun i=> East.docket H z i)
local notation "q₀"=> (fun k=> Captain.quietR M (z.2 k) (D k))
variable {α C B' v₁ d v₀ e A β κ :ℝ}(q n k :ℕ)(r₀:ℕ→ℕ)(A':ι→Prop)(hx:Candor M z D q n r₀ A')



-- Whorl.S e_a first variant C. v ~ -(1/2), power requires upper H(i,n) chosen from jumpFee grads.V.Uniform. use p length atMost.
local notation "EC"=> Directions G c
local notation "SC"=> Disk G c
open Sienna FrameBox Grove
open PhysicalNext.Repeat.East
open Daisy Daisy.Charity
-- choose at anchor0. coerces via `staff`. budget at strategy. ranks from options.
variable (w':ι→ℝ) (Y:Grove (0:Site c))
noncomputable def carryW (Y:Grove (0:Site c))(y:Site c): Grove y:= if h:y=0 then h.symm ▸ Y else FrameBox.cane y
lemma carryZero (Y:Grove (0:Site c)):Fan.carryW Y 0=Y:=by unfold Fan.carryW; split; rfl; contradiction
local notation "γ₀"=> (fun i:Stars H M=>Fan.carryW Y (Fan.originC M H i))
local notation "zb"=> (East.stagnate q Q.halo*radiusB t)
variable (κ)
variable (P₀:BudgetPoint)(hB:P₀.B=radiusB t) (i:ι)(hi:0 ∈ (M i).crest.image S.ratio.parent)
variable (l α' b₀ :ℕ) (hk:10*(l*radiusB t)< c.val)(h0:2*(2*(East.stagnate q Q.halo*radiusB t))≤ c.val)
local notation "y0"=> (Fan.sitesPC M H q n r₀ A' l)
local notation "Kt"=> neighbors (l*radiusB t) (0:Site c)
local notation "U"=> (fun j:Cash.fragrances H=>LocalLTE.Dilation.silhouette (0:Site c) P₀ l (fun _:ℕ=> locus (M i) H 0 j) 0)
local notation "u"=> Option (Fin z.fst)
local notation "p'"=> Fan.predictedC M φ H χ κ q n r₀ A' γ₀ h0 α' b₀
local notation "Z" k => (⟨z,Captain.gateP M i z k⟩:Stars H M)
variable (hm:East.stagnate q Q.halo*radiusB t < l*radiusB t) {T' E:ℝ}(ht:P₀.supportExponent+2 ≤ T')
-- levered Marker Occupancy costs. Sums at concrete radius. Grain speaking chosen by gross payment not post numerics.
noncomputable def beamP : Config G c→ ℝ:=if Charity.speaks (M i) H z then ∑ j:Option (Fin z.fst), p' (Z j) else 0
local notation "f'"=> Fan.beamP M φ H χ κ -- z order?
variable (h: Charity.speaks (M i) H z)
include h hi hm hB hk
lemma chartCase (p:Option (Fin z.fst)) : 0∈Fan.sitesPC M H q n r₀ A' l (Z p) ∧ Fan.originC M H (Z p)=0 ∧ y0 (Z p)⊆ U z∧ let X':= locus (M i) H 0 z; (Fan.fitsP M H q n r₀ A' (Z p)→ y0 (Z p) = U z ∧ U z=Kt) ∧ (¬Fan.fitsP M H q n r₀ A' (Z p) → y0 (Z p)= X'):=by
   let H':= Fan.sitesPC M H q n r₀ A' l (Z p)
   have he: locus (M i) H (0:Site c) z=reachability z:=if_pos h
   have hp: 0∈ reachability z:=he ▸ Daisy.Charity.seatY (M i) H _ hi z
   have hx: Fan.originC M H (Z p)=0:= if_pos hp
   have ha : reachability z ⊆ H':= Fan.prosperC M H q n r₀ A' l hm (Z p)
   have hh : 0∈ H':= ha hp
   by_cases hz:Fan.fitsP M H q n r₀ A' (Z p)
   · have hY : H'= neighbors (l*radiusB t) (0:Site c):=(show H'=neighbors _ (Fan.originC M H (Z p)) from if_pos hz).trans (hx ▸ rfl)
     let X':=(fun _:ℕ=>locus (M i) H 0 z); have hℓ:X' 0⊆ neighbors (l*P₀.B) 0:= by rw [show X' 0=reachability z from he,hB]; exact hY ▸ ha
     have h' : U z = Kt:= (LocalLTE.Dilation.allShoulders 0 P₀ l X' 0 hℓ (hB.symm ▸ hk)).trans (hB ▸ rfl)
     exact ⟨hh,hx,by rw [show y0 (Z p)= _ from hY,h'],fun _=> ⟨hY.trans h'.symm,h'⟩,fun H=>(H hz).elim⟩ -- rewrite syntax if `H` var
   have h' : H' = reachability z:=if_neg hz
   refine ⟨hh,hx,?_,fun h=>(hz h).elim,fun _=>h'.trans he.symm⟩
   rw [show y0 (Z p)= _ from h',← he]; exact (LocalLTE.Dilation.roomy (0:Site c) P₀ l (fun _=>locus (M i) H 0 z)).broad 0
omit h
open AnalyticBridge VerifiedReset
local notation "Sill"=> (Dilation.sill P₀.supportExponent l)
local notation "Qp"=> Fan.exactE M H χ
set_option quotPrecheck false
variable [Fintype ι]
-- eligibility from Pulse.career 
variable (hw:Fan.GrowsP M H P₀ (Fan.sitesPC M H q n r₀ A' l) w' T' E (Fan.exactE M H χ - Fan.predictedC M φ H χ κ q n r₀ A' (fun i: Stars H M=> Fan.carryW Y (Fan.originC M H i)) h0 α' b₀) (Fan.sitesPC M H q n r₀ A' l))(h':0≤w' i)
-- name order check
open Progress.DirectedRecipe
local notation "Fp" z => Fan.beamP M φ H χ z κ q n r₀ A' Y i α' b₀ h0 -- order edit
include hw h' ht
omit [Fintype ι] in
lemma mats : ∃ a: H.fragrances→ℝ, SumBudget (fun z=> w' i * Push.Local.reservedMass P₀ (U z) (a z)) (Dilation.sill P₀.supportExponent l*E)∧∀ z, P₀.Regular (U z) (Charity.matin (M i) H z χ- (Fp z)) ∧ P₀.supBounds 0 (U z) (Charity.matin (M i) H z χ- (Fp z)) (a z):=by
   obtain ⟨f,hΦ,hν,hV⟩:= hw.lights
   let S (z:H.fragrances):Prop:=Charity.speaks (M i) H z
   let U' := (U)
   let h(z:H.fragrances):=if S z then ∑ j:Option (Fin z.1), f ⟨z,Captain.gateP M i z j⟩ else 0
   refine ⟨h,?_,fun z=>?_⟩
   · have he :0 ≤ Dilation.sill P₀.supportExponent l:= Real.exp_nonneg _
     let F:= Σ z:H.fragrances,Option (Fin z.fst)
     let v (x:F): Stars H M:=⟨x.1,Captain.gateP M i _ x.2⟩
     have hp:Injective v:=by
        rintro ⟨z,p⟩ ⟨z',q1⟩ he; change Sigma.mk z _ = Sigma.mk z' _ at he; obtain ⟨eU,hV⟩:= Sigma.mk.inj he; subst z'; exact congr_arg _ ((Captain.singularPin M i z) (eq_of_heq hV))
     let g(x:F):=if S x.1 then w' i * Push.Local.reservedMass P₀ (U x.fst) (f (v x)) else 0
     have hB':SumBudget g (Dilation.sill P₀.supportExponent l*E):=by
       have hx:= budget_scale he (budget_pull v hp (hV 0)); apply budget_mono hx
       · intro j; unfold g; split; exact mul_nonneg h' (mul_nonneg (Real.exp_nonneg _) (hΦ _)); rfl
       rintro ⟨z,p⟩; unfold g; dsimp only; split
       next hh=>
          obtain ⟨hy,hx0,h0F,hQ,hQ'⟩:= Fan.chartCase M H z q n r₀ A' P₀ hB i hi l hk hm hh p -- order
          rw [if_pos hy,Captain.stampP M w' i z p]
          let c0:= w' i; let b:=f (v ⟨z,p⟩); have hc:0≤b:= hΦ _; let X:= Fan.sitesPC M H q n r₀ A' l (v ⟨z,p⟩)
          set δ:=LocalLTE.Dilation.sill P₀.supportExponent l with hδ
          change c0*Push.Local.reservedMass P₀ (U z) b ≤δ*(c0*b*Real.exp (T'*coverNumber P₀.B X))
          have hu: c0*Push.Local.reservedMass P₀ X b≤ c0*b*Real.exp (T'*coverNumber P₀.B X):=by
             unfold Push.Local.reservedMass; rw [← mul_assoc, mul_right_comm]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ht (by positivity))) (mul_nonneg h' hc)
          by_cases hv: Fan.fitsP M H q n r₀ A' (v ⟨z,p⟩)
          · rw [← show X=U z from (hQ hv).1]; exact hu.trans (le_mul_of_one_le_left (mul_nonneg (mul_nonneg h' hc) (Real.exp_nonneg _)) (LocalLTE.Dilation.roomy (0:Site c) P₀ l (fun _=>{0})).factor) -- c shadow
          have hη: Push.Local.reservedMass P₀ (U z) b ≤ δ * Push.Local.reservedMass P₀ X b:= by rw [show X=locus (M i) H 0 z from hQ' hv]; exact (LocalLTE.Dilation.roomy (0:Site c) P₀ l (fun _=>locus (M i) H 0 z)).charges 0 _ hc
          exact (mul_le_mul_of_nonneg_left hη h').trans ((mul_left_comm c0 _ _).trans_le (mul_le_mul_of_nonneg_left hu he))
       exact (hx.1 _)
     have hu(z:H.fragrances): w' i * Push.Local.reservedMass P₀ (U z) (h z)= ∑' (p:Option (Fin z.1)),g ⟨z,p⟩:=by rw [tsum_fintype]; by_cases he:S z <;> simp only [h,g,he,if_true,if_false,Push.Local.reservedMass,mul_zero,Finset.mul_sum] <;> first | rfl | simp
     simp_rw [hu]; exact ⟨fun _=>tsum_nonneg (fun _=> hB'.1 _),hB'.2.1.sigma,hB'.2.1.tsum_sigma.symm.trans_le hB'.2.2⟩
   unfold Fan.beamP; dsimp only; by_cases hx:S z; swap
   · rw [if_neg hx,Charity.quiet (M i) H χ z hx,sub_zero,show h z=0 from if_neg hx]; exact ⟨CouplingShape.reg_const _, by simpa only [abs_zero] using! (show P₀.supBounds 0 (U z) (fun _: Config G c=> (0:ℝ)) |0| from CouplingShape.sup_const 0)⟩ -- edit
   rw [if_pos hx,Captain.speaksP];
   let V (j:Option (Fin z.fst)) : Stars H M:= ⟨z,Captain.gateP M i z j⟩
   change P₀.Regular (U z) ((∑ j,Qp (V j))-(∑ j,p' (V j))) ∧ _
   have Ht(j):P₀.Regular (U z) (Qp (V j)-p' (V j))∧ P₀.supBounds 0 (U z) (Qp (V j)-p' (V j)) (f (V j)):=by
     have hη:= chartCase M H z q n r₀ A' P₀ hB i hi l hk hm hx j
     exact ⟨CouplingShape.reg_extend ((hν (V j)).1) hη.2.2.1, VerifiedReset.sup_larger ((hν (V j)).2 0 hη.1) hη.2.2.1⟩
   have hz(s:Finset (Option (Fin z.fst))):P₀.Regular (U z) (∑ j∈s,(Qp (V j)-p' (V j))) :=by
       induction s using Finset.induction_on with
       | empty=> simp only [sum_empty]; exact CouplingShape.reg_const _
       | insert j m hj ih=> rw [sum_insert hj]; have hh:= VerifiedReset.reg_sub (Ht j|>.1) (VerifiedReset.reg_sub (CouplingShape.reg_const (p:=P₀) (X:= (U z)) (0:ℝ)) ih); simpa only [show (fun _: Config G c=> (0:ℝ))=(0:Config G c→ℝ) from rfl,zero_sub,sub_neg_eq_add] using! hh
   have hp:=PhysicalNext.Repeat.Trio.sup_S (B:=P₀) (fun j:Option (Fin z.fst)=>Qp (V j)-p' (V j)) (fun j=>f (V j)) univ (U z) 0 (fun j (_:j∈univ)=> (Ht j).1) (fun j _=> (Ht j).2); rw [Finset.sum_sub_distrib] at hp
   have hβ:= hz Finset.univ; rw [Finset.sum_sub_distrib] at hβ; rw [show h z= _ from if_pos hx]; exact ⟨hβ,hp⟩
omit [Fintype ι] hw ht h'
include i hi h0
open AnalyticBridge.VerifiedReset.Collection.Price
lemma track : Replicated Y (East.stagnate q Q.halo*radiusB t) κ (b₀+1) (Fp z) ∧ ((Fp z) ≠ 0 → U z = (neighbors (l*radiusB t) 0)):=by
   unfold Fan.beamP; split
   next h=>
     have hp(j:Option (Fin z.1)):=chartCase M H z q n r₀ A' P₀ hB i hi l hk hm h j
     let f(j:Option (Fin z.fst)):= p' (Z j)
     have hf j: Replicated Y (East.stagnate q Q.halo*radiusB t) κ (b₀+1) (f j):=by
         unfold f Fan.predictedC; split; swap; · exact rp_zero _
         have h:= hp j|>.2.1
         dsimp only; rw [h,carryZero]; exact rp_raise _ (show Replicated Y _ _ b₀ _ from ⟨_,rfl⟩) (le_add_of_nonneg_right (by decide))
     have hh(v:Finset (Option (Fin z.fst))):Replicated Y (East.stagnate q Q.halo*radiusB t) κ (b₀+1) (∑ j∈v,f j):=by
         induction v using Finset.induction_on with
         | empty=> simp only [sum_empty]; exact rp_zero _
         | insert i t hi ht=> rw [sum_insert hi]; exact rp_add _ (hf i) ht
     refine ⟨hh Finset.univ,fun h=>?_⟩
     by_contra he; apply h; change ∑ i, f i=0; refine Finset.sum_eq_zero fun i _=>?_; unfold f Fan.predictedC; split; next hv=> exact (he (hp i|>.2.2.2.1 hv.1|>.2)).elim
     rfl
   exact ⟨rp_zero _,fun h=>(h rfl).elim⟩
end YM.LocalLTE.Fan
