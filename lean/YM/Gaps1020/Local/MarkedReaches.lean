import YM.Gaps1020.Local.MarkedRung
import YM.RG01.Survive.Leaves
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open March Next.Foundations YM.GapsLocal.ExpShares
open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n k M : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Bond f)} {η r q Y W A B A' a β b p v d t γ C s C' μ g ρ ℓ : ℝ} {l:ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi} {Ñ : ChartRatio G}
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {z : Air f G} {V:E→ Config G c}{x:E}

variable {H : Cash W s μ L Q o C T R}

open PhysicalNext.Repeat.Lotus

open YM.RG01.Survive
variable {ι:Type}[Fintype ι]
open Merge Palette PhysicalNext.Repeat.Daisy
open Push.AbsoluteSums.Mixed Push.AbsoluteSums.Reserves
variable (N:Captain H j C' d v Y A b r B q k χ)(U:ι→Team R)(M':ι→Leaf R)
    (rA:ι→ℝ)(X:Utopia H j v d r C' χ)
local notation "I'" => Tickets (Palette.sign M' S)
open Marker Merge.Switch Gas Ursell Captain Push.GridApprox.Nil
-- Assemble *all* angular derivative costs, including every mark mode, on
-- the actual E dictionary at the same support exponent. Each Forecast basis
-- carries shared ticket/marker indices. (proof model as RG01.Survive.LeafReady.)
open Trees
variable (rV:ι→ℝ) {V':Type}[DecidableEq V']{E':Marker.Census V'} (g:ι→Poly E')
    (z:H.fragrances) (sP:ℕ→Prop)

local notation "R0" => horizonRadius G L s
local notation "Lℓ" => reachability z
abbrev costsAt (p:H.ThinP)(ρ:ℝ)(M:ℕ)(i:Sections (M:=M) (S:=S) M'):= scalarWeight rA i.1 * slotMix N p (Palette.team M' i.1) ρ (ρ^(M+1)) M i.2
def cen (ρ:ℝ)(M:ℕ) (i:Requests M' z (M:=M)):= ‖coefficient H.seam z.snd / ↑(z.fst+1).factorial‖ * ∏ j':Option (Fin z.fst),2^j * costsAt N M' rA (z.2 j') ρ M (i j')
def sidecost (p:H.fragrances)(b:ℕ)(P:BudgetPoint) := (shiftG s*(1+ (coverNumber P.B (reachability p):ℝ)))^(P.power*b)
def priceAt (ρ:ℝ)(M:ℕ)(p:BudgetPoint)(u:E'.Mode):=
     ∑ i ∈ (univ : Finset (Requests M' z (M:=M))).filter (fun i=>sP (aggregateGrade M' z i)),
        ‖(letter M' g z i).part u‖ * (sidecost z j p * cen N M' rA z ρ M i)

omit [Fintype ι] in
lemma sidecost0 (D:BudgetPoint) (p:H.fragrances)(b:ℕ): 0 ≤ sidecost p b D:= by unfold sidecost shiftG; positivity
variable (w:V'→ℝ) (hv:∀ i,0<w i)(hx:∀ i, Poly.price w (g i) ≤ 1) (h : Thermal.BuysMix M' H rA)
include h
lemma costs0 (p:H.ThinP)(M:ℕ)(i:I'× Orders M)(hρ:0≤ρ) : 0≤ costsAt N M' rA p ρ M i :=
  mul_nonneg (scalarWeight0 _ i.1 h.nonnegative) (mul_nonneg (reserve0 N _ _ _ hρ (pow_nonneg hρ _) _) (by positivity))
lemma cen0 (M:ℕ)(i:Requests M' z (M:=M))(hρ:0≤ρ) : 0≤ cen N M' rA z ρ M i:= mul_nonneg (norm_nonneg _) (prod_nonneg fun j _=> mul_nonneg (by positivity) (costs0 _ _ _ h _ _ _ hρ))
lemma price0 (M:ℕ)(p:BudgetPoint)(u:E'.Mode)(hρ:0≤ρ): 0≤ priceAt N M' rA g z sP ρ M p u:= sum_nonneg fun i _=> mul_nonneg (norm_nonneg _) (mul_nonneg (sidecost0 ..) (cen0 N M' rA z h M i hρ))

variable (hf: Flock H N.conduit A B k) (hp: HasClutch N.conduit A)(hρ:2≤ρ)(ht:Thermal1020.charge Q L s r j (till s) ≤ ρ⁻¹)
include hf hp hρ ht
lemma earnIt (p:H.ThinP)(M:ℕ)(i:Sections M' (M:=M) (S:=S))(U:Config G c)(hU:Healthy (Pressure.temp s) (H.smallAt p) U): Ore U (rung M' rA χ p i) v (costsAt N M' rA p ρ M i) j:=by
   intro X _ _ _ V x hV hM; subst U; let A:= Palette.team M' i.1; have hZ:= (debts N p A hU hM hp ht hρ le_rfl hf i.2).smul (scalarWeight rA i.1); rw [Real.norm_of_nonneg (scalarWeight0 rA i.1 h.nonnegative)] at hZ; exact hZ
lemma localPrice (M:ℕ)(i:Requests M' z (M:=M)):
    LocalOn (Lℓ) (quantity M' rA χ z i) ∧ Measurable (quantity M' rA χ z i) ∧ GaugeInvariant (quantity M' rA χ z i) ∧ ∀ U, Healthy (Pressure.temp s) (Lℓ) U → Ore U (quantity M' rA χ z i) v (cen N M' rA z ρ M i) j:=by
   let L i:=H.smallAt (z.2 i)
   have he (i): (L i) ⊆ Lℓ:= Finset.subset_biUnion_of_mem (H.smallAt ∘ z.2) (mem_univ i)
   let c:ℝ := coefficient H.seam z.2 / ↑(z.1+1).factorial
   have hh(j):= globalMix (χ:=χ) (z.2 j) (Palette.team M' (i j).1) (i j).2
   exact ⟨fun U V hv=> congr_arg (c*·) (Finset.prod_congr rfl fun j _=> congr_arg (_*·) ((hh j).2.2 U V (agrees_mono hv (Finset.coe_subset.mpr (he j))))),measurable_const.mul (Finset.measurable_fun_prod _ fun j _=> measurable_const.mul (hh j).2.1),fun z U=> congr_arg (c*·) (Finset.prod_congr rfl fun j _=> congr_arg (_*·) ((hh j).1 z U)), fun U hU X _ _ _ V x hV hM=> (Products.earns (x:=x) (g:=fun i p u=> rung M' rA χ (z.2 i) p (V u)) _ (fun j p=> earnIt N M' rA h hf hp hρ ht _ M p U (Finset.disjoint_of_subset_left (he j) hU) _ V x hV hM) i).smul c⟩
variable (P':BudgetPoint)(hs:P'.threshold=Pressure.temp s)(hj:P'.order≤ j)(hb:P'.B=radiusB s)(hS:Sailor G P'.threshold q j)
include hs hj hb hS
lemma cents (U:Site c)(hU:U∈ Lℓ)(M:ℕ)(i:Requests M' z (M:=M)) : let Z:= quantity M' rA χ z i
    P'.Regular (Lℓ) Z ∧ P'.supBounds U (Lℓ) Z (sidecost z j P'*cen N M' rA z ρ M i):=by
   intro Z
   obtain ⟨hL,hM,hG,hP⟩:= localPrice N M' rA z h hf hp hρ ht M i
   have hh u (hu:Healthy P'.threshold (Lℓ) u): ContDiffAt ℝ (↑P'.order) (Z ∘ increment u) 0:= (charted (hP u (hs ▸ hu)) N.position).of_le (by exact_mod_cast hj)
   let d:ℝ := shiftG s*(1+ ↑(coverNumber P'.B (Lℓ)))
   have hK : 1 ≤ d:= by unfold d; unfold shiftG; nlinarith [Nat.cast_nonneg (α:=ℝ) (coverNumber P'.B (Lℓ)), Nat.cast_nonneg (α:=ℝ) (radiusB s)]
   refine ⟨⟨hL,hM,hG,hh,fun U h a ℓ e=> Next.Foundations.left_has a e (hh U h)⟩,⟨mul_nonneg (sidecost0 ..) (cen0 N M' rA z h M i (by linarith)),fun V h ℓ he' hD=>?_⟩⟩
   have h0 : ∀ y∈Lℓ, 1+(separation y U :ℝ)≤d:= by
     intro y hy
     have hf := Corona.extent (Lℓ) P'.B hy hU
     unfold d shiftG; rw [← hb]
     exact le_trans (show _ ≤ 1+(((coverNumber P'.B (Lℓ))*(4*P'.B+2) +2*P'.B:ℕ):ℝ) by exact add_le_add_right (by exact_mod_cast hf) _) (by push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) (coverNumber P'.B (Lℓ)),Nat.cast_nonneg (α:=ℝ) P'.B])
   exact costsD (p:=P') (Y:=d) hL hS N.income U _ N.near (hP _ (hs ▸ h)) h0 hK ℓ (he'.trans hj) hD
lemma premium (U:Site c)(hU:U∈Lℓ)(M:ℕ)(u:E'.Mode): P'.Regular (Lℓ) (forecast M' rA g χ z (M:=M) sP u) ∧ P'.supBounds U (Lℓ) (forecast M' rA g χ z (M:=M) sP u) (priceAt N M' rA g z sP ρ M P' u):=by
   apply regular_bound_sum; intro i hi; obtain ⟨he,hV⟩:= cents N M' rA z h hf hp hρ ht P' hs hj hb hS U hU M i; exact ⟨regular_smul _ (Blush.ornate he), bound_smul _ (Blush.pricingG he hV)⟩
omit hs hj hS hf hb hp ht
omit h in
lemma summedSlot (p:H.ThinP)(M:ℕ):
    ∑ i:Sections M' (S:=S) (M:=M), (costsAt N M' rA p ρ M i)*ρ^i.2.val= combined N M' rA M ρ (ρ^(M+1)) p:=by
   let A (i:I'):= reserveBy N p (Palette.team M' i) ρ (ρ^(M+1)) M; let a i:= scalarWeight rA (w:=Palette.sign M' S) i * A i
   have h (i:Sections M' (S:=S) (M:=M)): (costsAt N M' rA p ρ M i)*ρ^i.2.val=a i.1:= by
        unfold costsAt a A slotMix; rw [mul_assoc, mul_assoc,inv_mul_cancel₀ (by positivity), mul_one]
   rw [Finset.sum_congr rfl (fun i _=> h i),Fintype.sum_prod_type]; unfold combined sumWeight; rw [Finset.mul_sum]; apply sum_congr rfl; intro i _; simp [a,A,Orders]
set_option maxHeartbeats 700000 in
lemma bookedCosts (M:ℕ):
   ∑ i:Requests M' z (M:=M),(cen N M' rA z ρ M i)*ρ^(aggregateGrade M' z i) ≤ clusters H.seam (fun p=> 2^j*combined N M' rA M ρ (ρ^(M+1)) p) z.2 :=by
   let U j i:= costsAt N M' rA (z.snd j) ρ M i; let V j:= combined N M' rA M ρ (ρ^(M+1)) (z.2 j); let g (_:Option (Fin z.1)) (i:Sections M' (M:=M) (S:=S)):= (i.2.val:ℕ); let Φ:= coefficient H.seam z.2
   have hv:= Products.booked U V ρ g j (by linarith) (fun i q=> costs0 N M' rA h (z.2 i) M q (by linarith)) (fun i=> (summedSlot N M' rA hρ (z.2 i) M).le)
   unfold cen; simp_rw [mul_assoc]; rw [← Finset.mul_sum];
   have hp : ∑ i:Requests M' z (M:=M), Products.atPrices U j i*ρ^Products.order g i≤ ∏ i:Option (Fin z.fst),2^j*V i:= by
     have h (F F':Fintype (Requests M' z (M:=M))) (g : Requests M' z (M:=M) → ℝ) (a:ℝ) (h: (@Finset.univ _ F).sum g ≤ a): (@Finset.univ _ F').sum g ≤ a := by rwa [Subsingleton.elim F' F]
     exact h _ _ _ _ hv
   let t:ℝ:= (z.1+1).factorial; let a:ℝ:= ∏ i:Option (Fin z.fst),2^j*V i
   -- force dense inference at small log arity
   change ‖Φ/t‖*(∑ i:Requests M' z (M:=M),Products.atPrices U j i * ρ^Products.order g i) ≤ |Φ| *a/t
   refine (mul_le_mul_of_nonneg_left hp (norm_nonneg (Φ/t))).trans_eq ?_; rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) (z.fst+1).factorial)]; change _/t*a= _; ring
include hv hx hρ
lemma amortized (M a:ℕ) (hh:∀ i,sP i→a≤ i) : let Z u:= priceAt N M' rA g z sP ρ M P' u
    wordsPrice w Z ≤ sidecost z j P' * ((ρ^a)⁻¹ * clusters H.seam (fun p=> 2^j*combined N M' rA M ρ (ρ^(M+1)) p) z.2):=by
   intro f
   let y:= ∏ i:Option (Fin z.fst),Poly.price w (1:Poly E')
   have ht (i:Requests M' z (M:=M)): Marker.Poly.price w (letter M' g z i) ≤ 1:=by
      have h p : Poly.price w (∏ i∈p,g i) ≤ 1:=by
         apply le_trans (Poly.multiple hv p g) ((prod_le_prod (fun i _=> Poly.nonnegative hv _) (fun i _=>hx _)).trans_eq (Finset.prod_const_one))
      exact (Poly.multiple hv ..).trans ((prod_le_prod (fun i _=> Poly.nonnegative hv _) (fun i _=>h _)).trans_eq Finset.prod_const_one) -- notation implicit f
   let U:= (univ : Finset (Requests M' z (M:=M))).filter (fun i=>sP (aggregateGrade M' z i)); let c i:=cen N M' rA z ρ M i; let a':=sidecost z j P'; unfold wordsPrice f priceAt; simp_rw [Finset.mul_sum, ← mul_assoc]; rw [sum_comm]; simp_rw [← Finset.sum_mul]
   have ha:0<ρ:=by linarith
   have hA:=bookedCosts N M' rA z h hρ M
   simp_rw [mul_assoc];
   have hc i : 0 ≤ c i:=cen0 N M' rA z h M i ha.le
   have hB:0 ≤ a':=sidecost0 P' z j
   apply le_trans (b:= ∑ i∈ U,a'*c i) (Finset.sum_le_sum (s:=U) (fun i _=> mul_le_of_le_one_left (mul_nonneg hB (hc i)) (ht i)))
   rw [← Finset.mul_sum]; refine mul_le_mul_of_nonneg_left ?_ hB
   rw [mul_comm, ← div_eq_mul_inv,le_div_iff₀ (pow_pos ha _), sum_mul];
   apply le_trans _ hA
   exact le_trans (Finset.sum_le_sum (s:=U) (fun i hi=> mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (show 1≤ρ by linarith) (hh (aggregateGrade M' z i) (mem_filter.mp hi).2)) (hc i))) (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U) fun i _ _=> mul_nonneg (hc i) (by positivity))
end YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
