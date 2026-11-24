import YM.LocalTaylorR2.Mesh.Allowance

/-! # As in I, but with distinguished models inside each Taylor log. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Mesh
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Port Channel Next.Foundations Itinerary Reserves
variable {Ñ:ChartRatio G} {i p:ℕ} {v d A a y r B D C' θ α M ζ ρ:ℝ} {U:Molecule S} {χ:Chi}
variable (g:LogIndex c f→Port.Test T)
variable (Ξ:Utopia H i v d r C' χ) (Y:LocalBookingsR2 ζ B Ξ)
open Charge
structure Crib (g:LogIndex c f→Port.Test T)(Ξ:Utopia H i v d r C' χ)(p : ℕ)(ρ : ℝ):Prop where
   kept (j): Kept H (H.supportP (identityLog j)) (g j)
   mark (j): Sees H i v d χ (error g H j) (Ξ.goalsL j*(ρ⁻¹)^p) (r*spanW T R (radiusB s) Q.halo (identityLog (S:=S) j))
include Y in
lemma bamboo (hp:1≤betaF G s L)(hh:0≤ζ)(hz:0≤ρ) {w:LogIndex c f→ℝ} (he: Meter (H:=H) g p ζ r v d ρ D i χ w) (hv:B+D≤ Q.goal L s):
    ∃ U:Utopia H i v d r C' χ, LocalBookingsR2 ζ (B+D) U ∧ Crib g U p ρ :=by
  obtain ⟨I,hQ,hK⟩:= increasing Ξ Y g hp hh he hv
  refine ⟨I,hK,he.keptP,fun j=>?_⟩
  apply (he.tick j).climb H _ le_rfl; rw [inv_pow,hQ]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (Tender.logN ..)) (by positivity)

lemma plusTest {s:Support c} {g h:Port.Test T} (hg: Kept H s g)(hh: Kept H s h): Kept H s (fun F X w=>g F X w+h F X w):=by
  -- PI operator universal, not assuming either sector by this property
  exact ⟨fun F X Y w v ht hk Z he hp hA=> congr_arg₂ (·+·) (hg.links F X Y w v ht hk Z he hp hA) (hh.links F X Y w v ht hk Z he hp hA),fun E _ F X hx hK v y w hv hy hw=> (hg.borel E F X hx hK v y w hv hy hw).add (hh.borel E F X hx hK v y w hv hy hw),fun F X hx hk hz z w=>congr_arg₂ (·+·) (hg.rotate F X hx hk hz z w) (hh.rotate F X hx hk hz z w),fun F X hx hk h j b A E _ _ _ V x he hM hz=> (hg.clutch F X hx hk h j b A E V x he hM hz).together (hh.clutch F X hx hk h j b A E V x he hM hz)⟩
lemma sumTest {s:Support c}{ι:Type*} (x:Finset ι)(f:ι→Port.Test T)(h:∀ i∈x,Kept H s (f i)): Kept H s (fun F X v=>∑ i∈x,f i F X v):=by
  induction x using Finset.induction_on with
  | empty=>simp_rw [sum_empty]; exact Kept.fixed _
  | insert i a hi ih=> simp_rw [sum_insert hi]; exact plusTest (h i (mem_insert_self ..)) (ih fun i' hi=>h _ (mem_insert_of_mem hi))

def warm (H:Cash W s μ L Q o C T R)(g:LogIndex c f→Port.Test T)(q:Paint U p): Port.Test T:=fun F X w => ∏ i:↥(logs U), absorb (q i) (weightLog H i.val F X w) (g i.val F X w)
lemma runs (g) (k:ℕ) (F : Forest S.ratio)(V:Coat T F)(w:Air f G): compound H U F V w=∑ q:Paint U k,warm H g q F V w:= by
  unfold compound; rw [← prod_attach (logs U)]
  have he (i:↥(logs U)):Series.mellow (weightLog H i.val F V w)=∑ j:Series.Letter k, absorb j (weightLog H i.val F V w) (g i.val F V w):= by rw [absorb_last, Series.allLetters k]
  simp_rw [he]; exact Fintype.prod_sum (f:=fun i:↥(logs U)=>fun j:Series.Letter k=> absorb j (weightLog H i.val F V w) (g i.val F V w))
lemma mantle {g} (q: Paint U p)(hK:∀ j:↥(logs U),Kept H (H.supportP (identityLog j.val)) (g j.val)) (O:Support c)(h:H.unionP U⊆O):Kept H O (warm H g q):= by
  apply Kept.product; intro i _; have hp:= (Finset.subset_biUnion_of_mem H.supportP ((log_occ i.val).mp i.property)).trans h; apply Kept.mono _ hp
  unfold absorb; split
  · apply plusTest ((logTest H _).smooth _ (Series.smooth _)); apply sumTest; intro j _
    simp_rw [sub_eq_add_neg]; apply plusTest ((logTest H _).smooth _ (by unfold Series.mono; fun_prop))
    exact ((hK _).smooth _ (by unfold Series.mono; fun_prop)).smooth (fun x=> -x) (by fun_prop)
  exact (hK _).smooth _ (Series.smooth _)

open Tender
variable (hK:Crib g Ξ p ρ)
include hK
variable (hp:1≤betaF G s L)(hh:0≤ζ)(hθ:1≤θ) (he:1≤ρ)(hr:ρ*B≤1)(hM:Carry p i θ)

def intricate (θ ρ:ℝ)(p':Paint U p): ℝ:=∏ i: ↥(logs U), θ*(Ξ.goalsL i.val*(ρ⁻¹)^(p' i).val)
omit hK
lemma intricate_pos (q:Paint U p)(hθ :0≤ θ)(hr:0≤ρ) :0≤ intricate Ξ θ ρ q:= prod_nonneg fun i _=> mul_nonneg hθ (mul_nonneg (logN _ i.val) (pow_nonneg (inv_nonneg.mpr hr) _))
include hp hh he Y hK hr hM
lemma sumWarm (q:Paint U p) {U':Molecule S} (hu: U⊆U')(hx:troupe T R Q.halo (radiusB s) U'): Sees H i v d χ (warm H g q) (intricate Ξ θ ρ q) (2*r*(p+3:ℝ)*(1+H.shapeW U')):=by
  let f := spanW T R (radiusB s) Q.halo
  have hY (i':↥(logs U)): Sees H i v d χ (fun F X w=> absorb (q i') (weightLog H i'.val F X w) (g i'.val F X w)) (θ*(Ξ.goalsL i'.val*(ρ⁻¹)^(q i').val)) (r*f (identityLog i'.val)*(p+3:ℝ)):= by
    intro E _ _ _ F X V u z x w h hX hT hQ hf hu
    apply hM.2 (q i') E (fun x=> weightLog H _ F (vary X (V x)) (z x)) (fun x=>g _ F (vary X (V x)) (z x)) x (Ξ.goalsL i'.val) _ _ (logSees Y _ E F X V u z x w h hX hT hQ hf hu) (hK.mark _ E F X V u z x w h hX hT hQ hf hu) (inv_nonneg.mpr (zero_le_one.trans he)) (inv_le_one_of_one_le₀ he)
    refine (le_mul_of_one_le_left (logN ..) (logHigh hp hh i'.val)).trans ((rim _ Y i'.val).trans ?_)
    rw [← one_div]; exact (le_div_iff₀ (zero_lt_one.trans_le he)).2 ((mul_comm _ _).trans_le hr)
  let Z j:= f (identityLog (S:=S) (j:LogIndex c _))
  have hle: (logs U).image identityLog ⊆ U':= image_subset_iff.mpr (fun i hi=> hu ((log_occ i).1 hi))
  apply (Sees.collect H univ (fun j (_:j∈univ)=> hY j)).climb H le_rfl
  have hf (i:Head S) : 0≤ f i:= by
    rcases i with i|i; exact zero_le_one
    exact add_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hk : ∑ i∈logs U, f (identityLog i) ≤ 2*H.shapeW U':= by
    rw [← sum_image (f:=f) (fun _ _ _ _ he=> scenic_inj he)]
    exact (sum_le_sum_of_subset_of_nonneg hle (fun i _ _=> hf i)).trans (Utopia.worthy _ hx)
  have hr:1≤r:= Ξ.active
  refine le_trans (b:= r*(p+3:ℝ)* (∑ i∈logs U,Z i)) ?_ ?_
  · refine le_of_eq ?_; rw [← Finset.sum_attach (logs U), Finset.mul_sum]; exact sum_congr rfl fun i _=> by unfold Z; ring
  exact le_trans (mul_le_mul_of_nonneg_left hk (by positivity)) (by nlinarith only [mul_nonneg (b:=((p:ℝ)+3)) (zero_le_one.trans hr) (by positivity)])

omit hK hr hM Y
include hθ
lemma inflates (h:Pure U): (∑ q:Paint U p, intricate Ξ θ ρ q*ρ^(inserts q)) ≤ ∏ i∈U, entry Ξ ((p+1:ℝ)*θ*ρ) ζ i := by
  let g (i:↥(logs U)):= θ*(Ξ.goalsL i.val*ρ)
  have ht := zero_lt_one.trans_le he
  have hg (i:↥(logs U)) (q:Series.Letter p): θ*(Ξ.goalsL i.val*(ρ⁻¹)^q.val)*ρ^Series.rank q = g i:=by unfold g Series.rank; rw [inv_pow,pow_succ]; field_simp
  have hv (q:Paint U p): intricate Ξ θ ρ q*ρ^(inserts q)=∏ i,(fun _:(Series.Letter p) =>g i) (q i):=by
    unfold intricate inserts; rw [← Finset.prod_pow_eq_pow_sum,← Finset.prod_mul_distrib]; exact prod_congr rfl fun i _=> hg i (q i)
  let v:=entry Ξ ((p+1:ℝ)*θ*ρ) ζ
  have hx i : v (identityLog i)=((p+1:ℝ)*θ*ρ)*(perLog (G:=G) L ζ s i*Ξ.goalsL i):= entryO Ξ _ _ _
  have hd: (∏ i∈U,v i)= ∏ i: ↥(logs U), v (identityLog i.val):= by
    conv_lhs=> arg 1; rw [allPure h]
    rw [prod_image (fun _ _ _ _ h=> scenic_inj h), ← prod_attach (logs U)]; rfl
  change _ ≤ ∏ i∈U,v i; rw [hd]; calc
    _ = ∑ q:Paint U p,∏ i,(fun (_:Series.Letter p)=> g i) (q i):= Finset.sum_congr rfl fun i _=> hv i
    _ = ∏ j: ↥(logs U),∑ _:(Series.Letter p), g j := (Fintype.prod_sum (f:=fun i:↥(logs U)=> fun _:Series.Letter p=>g i)).symm
    _ ≤ _:= by
      simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin,Series.Letter,Nat.cast_add,Nat.cast_one,hx]
      refine Finset.prod_le_prod (fun i _=> ?_) (fun i _=> ?_)
      · unfold g; have hp:= logN Ξ i.val; positivity
      unfold g; rw [← mul_assoc,← mul_assoc, mul_right_comm _ (Ξ.goalsL i.val) ρ]; exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (logN ..) (logHigh hp hh _)) (by positivity)
end YM.LocalTaylorR2.Mesh
