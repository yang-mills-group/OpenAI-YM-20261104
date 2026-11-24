import YM.FVA2.Stilling
/-!
# Reflected Gram: actually establish the limit of bare-frame T0 (may be nonzero at regulator)
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 760000
set_option quotPrecheck false
namespace YM.FVA2.Counterpart
open Function Filter Set MeasureTheory
open Pert Pert.Position Maxwell Maxwell.Free PositionX
open PositionX.Jet
open Wilson Lattice Gauge PertExtension PertExtension.Chart PertExtension.LatticePT
open MS MS.Menus MS.Land MS.Theater MS.Tone MS.Book MS.Book.Program MS.Book.Convolve MS.Orbit MS.Tide MS.Rake
open Clock Score Based PairCoords Modes Paper Trans ColorCode Attend BoxOffice Blaze Frost ArchTurn
open PowerSeries WorldJet Metric Pond Fountain Rigidity.Positive
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius ComplexOrder
variable {G:Gauge} {Q: Booked (wings G)}(V:Warehouse G)(P: Prescription (wings G))(M:MS_Data G Q)
variable (H:ExactSpin V P)(HI:Trusted P) (he: MixedStory.AllProfiles M V P)
variable (d:ℕ)(q:ℕ+)(hq:1 < q.val) (j:ℕ) (μ:ℝ)
local notation "Y"=> V.F
local notation "ϵ"=> epsilon q
local notation "ΠP" k=>μ-Pond.clock q k
local notation "W"=> E V.F d
def mother (k:ℕ) : Buffer V.F d:= bareReset V P (ϵ k) (ΠP k) 0 H HI d
local notation "r"=> mother V P H HI d q μ
local notation "F₀"=> bareD V P (ϵ j) (ΠP j) 0 d
local notation "L"=> ( buffers V.F d ).subtype
-- placement Gram demand
abbrev pictures : Points 2:= Extra.FD.couple (_root_.YM.basis 0) 0
private lemma valid : pictures∈conf 2:= Extra.FD.couple_ok (by intro e; simpa [basis_norm] using congr_arg norm e)
local notation "Adj"=> (Model Y).adj (hierarchy Y).spin d 0
private lemma reflected_add (k:ℝ)(p:W) : Adj (k • p)=k • (Adj p):= by rw [RCLike.real_smul_eq_coe_smul (K:=ℂ), map_smulₛₗ,starRingEnd_apply]; simp
include H in
lemma mirrorD (p:W) : F₀ (Adj p)= Adj (F₀ p):= by
   let K(x):=(Model Y).conj ( hierarchy Y ).spin d x; have hm(s:Signed)(p:W):= (show (Model Y).mirror ( hierarchy Y ).spin d s p=spin Y s.ortho d p from Pert.Rigid.wear_ride .. ); unfold Table.adj; simp_rw [LinearMap.comp_apply, hm, D_turn V P _ _ _ H, D_real ]
private def gram2 (F:MultilinearMap ℂ (fun _:Fin 2=> E V.F d) ℂ) : LinearMap.BilinForm ℝ W:= by
   let R:= Complex.reCLM.toLinearMap.compMultilinearMap (F.restrictScalars ℝ);
   let f (x y:E V.F d):= R ![y,Adj x]; let P(y:W):= ( R.toLinearMap ![y,0] (1:Fin 2)); let Q (x:W):= ( R.toLinearMap ![0,Adj x] (0:Fin 2)); have h0(x y:W):Q x y=f x y:= by change R (Function.update ![_,_] _ y)=_; unfold f; congr! 1; ext1 i; fin_cases i <;> simp
   have h1(x y:W):P y (Adj x)=f x y := by change R (Function.update ![_,_] _ _)=_; unfold f; congr! 1; ext1 i; fin_cases i <;> simp
   refine LinearMap.mk₂ ℝ f (fun a b c=> ?_) (fun a b c=> ?_) (fun a b c=>?_) (fun a b c=>?_ )
   · rw [ ← h1,← h1, ← h1,map_add,map_add ]
   · rw [ ← h1,← h1,reflected_add,map_smul ]
   · rw [ ← h0,← h0, ← h0,map_add ]
   rw [ ← h0,← h0,map_smul ]
private lemma gram_v (x y: E Y d) : gram2 V d (visible Y d pictures) x y=(gramC Y (hierarchy Y) (d:=d) 0 x y).re := by
   have he: gram2 V d (visible Y d pictures) x y=Complex.re (visible Y d pictures ![y,Adj x]):= rfl; rw [he, visible_eq ]; change Complex.re _ = Complex.re ( Extra.FD.readsTwo Y d ( _root_.YM.basis 0 ) 0 y (Adj x) ); unfold Extra.FD.readsTwo; rw [LinearMap.BilinForm.comp_apply, Extra.FD.joinLin_apply ]; apply congr_arg _; unfold Extra.FD.join; apply congr_arg; funext i; fin_cases i <;> exact Eq.symm (common_L V d _)
private lemma junta {f:ℕ→ LinearMap.BilinForm ℝ W}{R:LinearMap.BilinForm ℝ W}(h:∀ p q,Tendsto (fun k=>f k p q) atTop (𝓝 (R p q)))(z:ℕ→ℕ)(hz:Tendsto z atTop atTop)(p: W) (x:ℕ→ W)(hx:Tendsto x atTop (𝓝 p)) : Tendsto (fun i=> f (z i) (x i) (x i) ) atTop (𝓝 (R p p)):= by
    let J:= Fin (Module.finrank ℝ W); let e:= Module.finBasis ℝ W; have ℓ (i:J): Tendsto (fun j:ℕ=> e.coord i (x j)) atTop (𝓝 (e.coord i p)):= (LinearMap.toContinuousLinearMap (𝕜:=ℝ) (E:=E V.F d) (e.coord i)).continuous.continuousAt.tendsto.comp hx
    have he (F: LinearMap.BilinForm ℝ W)(p:W): F p p=∑ i:J, ∑ j:J,e.coord i p * e.coord j p * ( F (e i) (e j) ) := by
       conv_lhs=> rw [← e.sum_repr p]
       simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul ]; -- see
       simp_rw [Finset.mul_sum ]; rw [Finset.sum_comm ]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; rw [mul_left_comm, ← mul_assoc ]; rfl
    rw [he R p]; nth_rw 1 [funext fun k=> he (f (z k)) (x k) ]; exact tendsto_finsetSum _ (fun i _=> tendsto_finsetSum _ (fun j _=> ((ℓ i).mul (ℓ j)).mul ((h ..).comp hz)))
include hq he
set_option maxRecDepth 5000 in
lemma rent_calm : Tendsto (mother V P H HI d q μ) atTop (𝓝 0):= by
   choose u hu using hasOrigin q;
   let x:=pictures; let v:= fun i=> Grid.signal q i pictures;
   let S(i:ℕ): Court W 2 ℂ:= (coeff (R:=ℂ) 0).compMultilinearMap ( rawL V q i (v i) (u i) d ); let F(i):= gram2 V d (S i); let K:= (gram2 V d ( visible Y d pictures ));
   let p(i):= bareD V P (ϵ i) (ΠP i) 0 d; apply GramB.quiet (X:= E Y d) L ( buffers Y d|>.subtype_injective ) r (d+1) _ K _ F -- maybe shape
   · refine junta V d (R:= K) (fun a b=> ?_); exact Complex.reCLM.continuous.continuousAt.tendsto.comp ( Z_real V q hq ![b,Adj a] u v hu valid ( Grid.choose_sample hq x ) ) -- swirl order args?
   · intro a; let g(i:ℕ):= a+ (r i).val a; have h (i:ℕ): g i=p i a:= by change a+(p i a-a)=p i a; abel
     change Tendsto (fun n=> F n (g n) (g n)) _ _; simp_rw [h]; obtain ht:= Fountain.density V P M H HI he q hq μ 0 ![a,Adj a] u (Eventually.of_forall hu) x valid v (Grid.choose_sample hq x); rw [ vintage V M μ _ valid ] at ht; simp_rw [ born_eff ] at ht; let X(i):=![p i a, Adj (p i a)]; have hv (i): p i ∘ ![a,Adj a]=X i:= by unfold X; ext1 t; fin_cases t; rfl; exact mirrorD V P H d q i μ a -- params missing
     unfold p at hv; simp_rw [hv ] at ht; exact Complex.reCLM.continuous.continuousAt.tendsto.comp ht
   · intro i; let Q:= projectionD V P (epsilon q i) (μ-Pond.clock q i) 0 d; have h(k:ℕ)(t:W): ((r i).val ^ k) t=(Q^k) t:= by
        induction k with
        | zero=> rfl -- pow_zero CLM not rfl?
        | succ k ih=> rw [pow_succ', pow_succ', Module.End.mul_apply]; change (r i).val _= _; exact congr_arg ( (r i).val ) ih
     apply ContinuousLinearMap.ext; intro x; change ((r i).val^_) x= _; rw [ h (d+1) x, show Q^(d+1)=0 from Counterpart.nilpotent V P (epsilon q i) _ (epsilon_pos q i).ne' d ]; rfl
   intro t ht; by_contra hb; rw [ show K t t=_ from gram_v V d t t ] at ht; exact ( Complex.lt_def.mp ( gramC_pos Y (hierarchy Y) 0 hb )|>.1 ).ne ht.symm
end YM.FVA2.Counterpart
