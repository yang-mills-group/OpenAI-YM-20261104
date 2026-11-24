import YM.RemainderComparison.Fallow.Marksmanship
/-!
# Logical singleton projection on the marker-conditioned expression

Keeper runs after Passion.Both. tilts. Literal `Source.Coefficient` in the actual header and kernel conventions. Keeps `ζ` operator tests normalized before bases, connects X to Pet.R and bound. Before conversion on different bases by RG04, use representation supplying THESE commitments. No assumption chosen χ in Region matches a final stable graph.Via β conversion eventual.Se.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Fallow
open Function Filter Lattice RG Wilson MeasureTheory Push Push.AbsoluteSums Marker Finset
open Solos Mosaic Verse Serif Flues WickReps Ethereal Jolt Lacuna Lobby Passion GridRenewal.Rain PhysicalNext.Repeat WardBin.Crest
open Source Labels Next.Foundations Local Work.G08 AnalyticBridge VerifiedReset VerifiedReset.Seat
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {θ ι:Type}{Q:θ→Type*} [∀ i,NormedAddCommGroup (Q i)][∀ i,NormedSpace ℝ (Q i)]
variable {α:Type*}{G:Gauge}{n:Side}{I:Type}
variable (T:Manor G n ι (Audited Q) I)(p:BudgetPoint)(R:ι→Support n)(Z:Set ι)
variable [Fintype θ][DecidableEq θ](J:Census θ)
variable {i:θ}{D:ι→Finset θ}{z:ι→ Poly J}(X: Hol G) (F:Plane G n θ) (a:Audited Q)
local notation "L"=>F.visor i
set_option quotPrecheck false
local notation "F₀"=>(L).basis
local notation "τ"=> (L).sectionQ
local notation "o'"=>(L).origin
local notation "A" => Roll T R Z D
local notation "A₁"=> cash T p R Z F X SeatD.MaskType.exactM z D

-- Unit projection data. Before α layout tests as all marker packs.V No continuity α on arbitrary OFFMASK required. Need physical test evaluation before operator size. 
local notation "R₀" => players T R Z F D i
local notation "M"=>SeatD.MaskType.exactM
local notation "Wq" => salary T R Z J F z i
local notation "δp" => crowns T p R Z J X F a z i
local notation "Rφ" => kernels T p R Z J X F a z i
variable (hp:Passion.Oriented D J Z z)(he:F.exam i)
variable {σ b t e wA:ℝ}{l k:ℕ}
variable (h:Precepts T p R Z D σ b)(hr:AxisG p F X t l e) (hQ : Placed R F D)
variable (w:θ→ℝ) (x:players T R Z F D i)
local notation "Y₁"=> area T R Z F (D:=D)
local notation "Q₁" => PairAt T p R Z F X x.val a i
local notation "P" => p.threshold
variable (V:Rep G n) (r:ℕ→ Config G n →ℂ)(hκ: Lodge T p R Z F X SeatD.MaskType.exactM D wA) -- shadow w
open Progress.DirectedRecipe
-- raw lower f grant assumptions.Flow band & Forms
variable {c d' δ:ℝ} (κ':players T R Z F D i↪ℕ)
def homing(D:ι→Finset θ)(i:θ) (e:players T R Z F D i↪ℕ):ℕ→Support n:= Function.extend e (fun x:players T R Z F D i=> area T R Z F x.val) (fun _=>{(F.visor i).origin})
local notation "pa"=> homing T R Z F D i κ'
omit [Fintype θ][DecidableEq θ] in
lemma sizeSum {X:Type}(v:X→ (F.visor i).basis.Coeff)(h:SumBudget (fun j=> (F₀).coeffSize (v j)) c): Summable v ∧ (F₀).coeffSize (∑' i,v i) ≤ c:=by
    have hv:Summable fun i=> ‖v i‖:= h.2.1.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=> norm_le_size _ (v i)); have hS:Continuous (F₀).coeffSize:= by unfold Labels.Frame.coeffSize; fun_prop
    refine ⟨hv.of_norm,le_of_tendsto (hS.continuousAt.tendsto.comp hv.of_norm.hasSum) (Eventually.of_forall fun I=>?_ )⟩
    have hh (x:Finset X): (F₀).coeffSize (∑ i∈x,v i) ≤ ∑ j∈x,(F₀).coeffSize (v j):=by
        induction x using Finset.induction_on with
        | empty=> simp [Labels.Frame.coeffSize]
        | insert k s hi he=> simp only [Finset.sum_insert hi]; have ht:= Work.G08.size_triangle F₀ (v k+(∑ j∈s,v j)) (v k); rw [add_sub_cancel_left] at ht; exact ht.trans (add_le_add_right he _)
    exact (hh I).trans (budget_sum h I)
def music (z:ι→ Poly J)(i:θ) (e:players T R Z F D i ↪ ℕ): Coefficient (F.visor i).basis n:= ⟨∑' b:players T R Z F D i,Fallow.crowns T p R Z J X F a z i b, homing T R Z F D i e, Progress.DirectedRecipe.stuff e (Fallow.kernels T p R Z J X F a z i),r⟩
local notation "μ"=> music T p R Z J X F a r z i κ'
variable (hW : Serif.Chorus J w Z z k)
include h hr hQ hκ hW -- define
variable (hc : 0< d')(hv:V.p=p)(hR:ForceFormat p V.activities (F.visor i).origin r)
variable {pQ:ℝ} (hD: ForceCost p V.activities r (d'*pQ))(hP:0≤ pQ)
variable {qP:ℝ} -- hκ uses wF : ℝ
include hR hc hv hD hP
-- cost in SER. Void on unavailable labels no reoptimizations
local notation "wp"=> (w i)⁻¹
local notation "pay"=>wA
omit [Fintype θ] in
lemma eulogy : let Y:= music T p R Z J X F a r z i κ';
                           ((F₀).coeffSize Y.x ≤ wp*pay) ∧ Y.Format o' X V ∧ Y.remBound o' V d' (wp*pay+pQ):=by
    intro Y; obtain ⟨f,hf,hB⟩:= Fallow.merit T p R Z J X F h hr hQ w hW hκ (i:=i)
    have he : ∀ i,0≤ f i:= fun i=> (hB i a).1.1; have hg:= Local.sumBudget_uncharge he hf
    have hx:= (sizeSum F δp (budget_mono hg (fun i=> Work.G08.size_nonneg ..) (fun i=> (hB i a).2))).2
    let g:= stuff κ' f; have hh i : p.Regular ((Y).support i) (Y.regular i) ∧ o'∈Y.support i∧ Reads X o' (Y.support i) (0:Labels.Label G (L).degree) (Y.regular i)∧ p.supBounds o' (Y.support i) (Y.regular i) (g i):=by
       by_cases hm:i∈ Set.range κ'
       · obtain ⟨s,rfl⟩:=hm; obtain ⟨_,hz⟩:= issued T R Z F hQ s
         obtain ⟨h,hk⟩:= survey T p R Z J X F a h hr hQ s
         rw [show Y.support (κ' s)= area T R Z F s.val from κ'.injective.extend_apply (fun (i:R₀)=> Y₁ i.val) (fun _=>{o'}) s, show Y.regular (κ' s)=Rφ s from stuffed .., show g (κ' s)=f s from stuffed ..]; exact ⟨h,hz,hk,(hB s a).1⟩
       rw [show Y.support i={o'} from Function.extend_apply' (fun (i:R₀)=> Y₁ i.val) (fun _=>{o'}) _ hm,show Y.regular i=0 from Progress.DirectedRecipe.blank _ _ hm,show g i=0 from Progress.DirectedRecipe.blank _ _ hm]
       have hv : p.Regular {o'} (0: Config G n →ℝ):= VerifiedReset.reg_const 0
       exact ⟨regular_mapped Complex.ofRealCLM hv, Finset.mem_singleton_self _,(reads_null_iff ..).mpr ⟨rfl,fun _ _=>⟨contDiffAt_const,fun k _=>by simp⟩⟩,(sup_real hv).2 (by simpa only [abs_zero,show (0:Config G n→ℝ)=(fun _=>0) from rfl] using VerifiedReset.sup_const 0 (G:=G) (o:=o') (X:={o'}) (p:=p))⟩ -- presentation
    have hp i:= (reads_null_iff ..).mp ((hh i).2.2.1); have hw: Y.forced=r:=rfl
    refine ⟨hx,⟨fun i=>hv ▸ (hh i).1,fun i=> (hh i).2.1,fun i=> (hp i).1,fun i=> (hp i).2,hv.symm ▸ hR.forcing,hR.carried,hR.invariant,hv.symm ▸ hR.supported,hR.borel⟩,⟨wp*pay,pQ,budget_nonneg hf,hP,le_rfl,hc,?_,?_⟩⟩
    · rw [hv]; refine ⟨g, Local.sumBudget_pass κ' _ ?_ (fun i hi=> ?_),fun i=> (hh i).2.2.2⟩
      · simp_rw [show ∀ i,Y.support (κ' i)= area T R Z F i.val from fun j=> κ'.injective.extend_apply (fun (k:R₀)=>Y₁ k.val) (fun _=>{o'}) j,show ∀ i,g (κ' i)= f i from fun i=>stuffed ..]; exact hf
      rw [show g i=0 from Progress.DirectedRecipe.blank _ _ hi]; simp [BudgetPoint.mass]
    rw [hv]; exact hD
end YM.RemainderComparison.Fallow
