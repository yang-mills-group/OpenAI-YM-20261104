import YM.Gaps1020.Local.Moment
import YM.RG01.Survive.Leaves
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Thermal1020
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

-- local Taylor coefficients for LeafReady. Total ASCENT in exponent orders,
-- NOT number of selected heads. Pure warning carriers spend exceptional slot.
open YM.RG01.Survive
variable (H)
def powerLeaf (χ:Chi)(p:H.ThinP)(π:Assign p.val M)(V:Config G c):=
    Pond.likely fun i : Greenbelt.Reserve S =>
      weightedFringe (prism T s χ o.K V (Greenbelt.allot i)) p.val (assignment p.val π) R Q.table W o.a Q.halo

def thermal (χ:Chi)(M:ℕ)(p:H.ThinP)(k:ℕ)(V:Config G c):=
    if blaze p.val=∅ then ∑ π∈ (univ : Finset (Assign p.val M)).filter (fun π=> Thermal1020.degree p.val π=k), powerLeaf H χ p π V
    else 0

def basis (χ:Chi) (M:ℕ) : Expansions H M:= fun p k V=> if k.val=M+1 then leaflet H χ V p-∑ i∈range (M+1), thermal H χ M p i V else thermal H χ M p k.val V

variable {H}
lemma arrived (p:H.ThinP) (π:Assign p.val M) : Measurable (powerLeaf H χ p π) ∧ LocalOn (H.smallAt p) (powerLeaf H χ p π) ∧ GaugeInvariant (powerLeaf H χ p π):= by
  let X i := prism T s χ o.K 1 (Greenbelt.allot (S:=S) i); let f i V:=weightedFringe (vary (X i) V) p.val (assignment p.val π) R Q.table W o.a Q.halo
  have he i := seamWeighted (H:=H) (X:=X i) p.val (assignment p.val π) rfl rfl (fun _=> (share_contDiff 0 ..).continuous.measurable)
  change Measurable (fun V=> likely (fun i=> f i V)) ∧ LocalOn (H.smallAt p) (fun V=>likely (fun i=> f i V)) ∧ GaugeInvariant (fun V=> likely (fun i=> f i V))
  exact ⟨measurable_const.mul (Finset.measurable_fun_sum _ fun i _=> (he i).1),fun U V h=>congr_arg likely (funext fun i=> (he i).2 U V h), fun z V=>congr_arg likely (funext fun i=> weightedFrieze (X i) W o.a p.val _ R Q.table Q.halo z V)⟩

lemma thermal_global (p:H.ThinP)(k:ℕ) : Measurable (thermal H χ M p k) ∧ LocalOn (H.smallAt p) (thermal H χ M p k) ∧ GaugeInvariant (thermal H χ M p k):=by
  unfold thermal; split
  · exact ⟨Finset.measurable_fun_sum _ fun i _=> (arrived p i).1, fun U V h=> sum_congr rfl fun i _=> (arrived p i).2.1 U V h,fun z V=> sum_congr rfl fun i _=> (arrived p i).2.2 z V⟩
  exact ⟨measurable_const,fun _ _ _=>rfl,fun _ _=>rfl⟩
lemma basis_global (p:H.ThinP)(k:Orders M) : GaugeInvariant (basis H χ M p k) ∧ Measurable (basis H χ M p k) ∧ LocalOn (H.smallAt p) (basis H χ M p k) := by
  unfold basis; split
  next h=>
    obtain ⟨hm,hL,hG⟩:= Captain.arrived (H:=H) (χ:=χ) p
    refine ⟨fun z U=>congr_arg₂ (·-·) (hG z U) (Finset.sum_congr rfl (fun i _=> (thermal_global (M:=M) p i).2.2 z U)), ?_,fun U V h=>congr_arg₂ (·-·) (hL U V h) (Finset.sum_congr rfl (fun i _=> (thermal_global (M:=M) p i).2.1 U V h))⟩
    exact hm.sub (Finset.measurable_fun_sum _ fun i _=> (thermal_global p i).1)
  next=> exact ⟨(thermal_global p k.val).2.2, (thermal_global p k.val).1,(thermal_global p k.val).2.1⟩

lemma basisLiteral (p:H.ThinP)(M:ℕ)(V:Config G c): ∑ k:Orders M,basis H χ M p k V=leaflet H χ V p:=by
  rw [Fin.sum_univ_castSucc]
  have h (k: Fin (M+1)):basis H χ M p k.castSucc V=thermal H χ M p k.val V:= if_neg k.isLt.ne
  rw [sum_congr rfl fun i _=> h i, Fin.sum_univ_eq_sum_range (fun k=>thermal H χ M p k V),basis,Fin.val_last,if_pos rfl]; ring

section price
variable {K:ℕ} (N:Captain H j C' d v Y A b r B q k χ) {p:H.ThinP}(hN:Narrow K ℓ p) (hu:V x ∈ Set.univ)
    (hP : Healthy (Pressure.temp s) (H.smallAt p) (V x))(hM : Mode V x j v)
include hN hP hM N
omit hN in
private lemma lev (M:ℕ) : (fun i=>∑ π:Assign p.val M,powerLeaf H χ p π (V i))=ᶠ[𝓝 x] fun i=> leaflet H χ (V i) p:=by
  let X k := prism T s χ o.K (V x) (Greenbelt.allot (S:=S) k)
  have h k:= fringeTogether (X:=X k) p.val N.oboe rfl rfl rfl hM rfl p.2.2 hP M
  filter_upwards [eventually_all.mpr h] with y hy
  unfold powerLeaf leaflet; simp only [Pond.likely]; rw [← mul_sum,Finset.sum_comm]; apply congr_arg; apply sum_congr rfl; intro i hi; exact hy i

variable (h:HasClutch N.conduit A)(hρ: charge Q L s r j ℓ ≤ ρ⁻¹) (h2:2 ≤ ρ)
include h hρ h2
lemma momentCost (he:blaze p.val=∅) (π:Assign p.val M): Brush j (ratesheet p.val π j ρ*(B*N.conduit.meant p.val k)) 1 (powerLeaf H χ p π ∘ V) x:= by
  let X i := prism T s χ o.K (V x) (Greenbelt.allot (S:=S) i); let f i y:= weightedFringe (vary (X i) (V y)) p.val (assignment p.val π) R Q.table W o.a Q.halo
  letI : Nonempty (Tree.Forest S.ratio) := Tree.select S.ratio S.patch.odd_side
  exact Captain.avgBrush f _ x (fun i=> fringePower (X:=X i) p.val h N.oboe rfl rfl rfl hM rfl p.2.2 hP (Thermal1020.notWarning_isLog hN.unmaskedLetters he) hN.enters hN.connected hN.setPrice.le hρ h2 π)

omit h hρ h2 hN hP hM N in
private lemma below {ι:Type} [Fintype ι] (f:ι→ℝ) (g:ι→ℕ)(M:ℕ):
    (∑ i∈ (Finset.univ.filter (fun i=> ¬ M≤g i)), f i)=∑ k∈range M,∑ i∈ (univ.filter (fun i=>g i=k)), f i:= by
  simp_rw [sum_filter]; rw [sum_comm]; apply sum_congr rfl; intro i hi
  symm; rw [Finset.sum_ite_eq]; simp [mem_range, not_le]

-- Upper bound in preweighted cost: each grade pays at full coarse R and
-- all order assignments simultaneously. Summing all such at each output
-- grade costs `M+2`, deliberately rough at an internal finite M.
def packets (j K M:ℕ) : ℝ := (((M+2:ℕ):ℝ)* overhead j M)^K*(1+(1+K:ℝ))^j
omit h hρ h2 hN hP hM N in
lemma package (j K M:ℕ):1≤ packets j K M:= by
  apply one_le_mul_of_one_le_of_one_le
  · exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le (by push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) M]) (overhead_bound ..))
  exact one_le_pow₀ (by linarith only [Nat.cast_nonneg (α:=ℝ) K])

omit hN hP hM h N hρ h2
include hN h2
lemma allCharges (F:Finset (Assign p.val M))(m:ℕ)(he:∀ π∈ F,m≤ Thermal1020.degree p.val π) :
     ∑ π∈ F,ratesheet p.val π j ρ ≤ (packets j K M*ρ^p.val.card)*(ρ^m)⁻¹:=by
  have hpos:0<ρ:=by linarith
  have hp:1≤ρ:=by linarith
  let r:= overhead j M; have hr:1≤r:= overhead_bound ..
  let w:= p.val.card; have hK:w≤K:= hN.size'
  let i (x:ℕ):=(1+(1+(x:ℝ)))^j
  have hu : i w ≤ i K:=by unfold i; gcongr
  have h : ∀ π∈F, ratesheet p.val π j ρ*ρ^m≤ r^w * i w * ρ^w:= by
    intro π hπ
    let d:= ∑ i:↥p.val,((π i).val-1);
    have hD: m ≤ d+w:=le_trans (he _ hπ) (le_trans (Finset.sum_le_sum (s:= (univ:Finset (↥p.val))) (g:=fun i=> (π i).val-1+1) (fun i _=>by omega)) (by rw [sum_add_distrib]; simp [d,w]))
    calc
      _= r^w* i w * ((ρ^d)⁻¹ * ρ^m):=by unfold ratesheet; rw [Finset.prod_mul_distrib, Finset.prod_const,card_univ,Fintype.card_coe,Finset.prod_pow_eq_pow_sum,inv_pow]; unfold r i d w; ring
      _≤ _ := mul_le_mul_of_nonneg_left (by
        rw [mul_comm,← div_eq_mul_inv,div_le_iff₀ (pow_pos hpos _),← pow_add]; exact pow_le_pow_right₀ hp (by omega)) (by unfold i; positivity)
  rw [← div_eq_mul_inv,le_div_iff₀ (pow_pos hpos _),sum_mul]
  have hf : F.card ≤ (M+2)^w:= Finset.card_le_card (Finset.subset_univ F) |>.trans (by rw [card_univ]; unfold Assign; simp [w])
  apply le_trans (Finset.sum_le_sum h)
  rw [sum_const,nsmul_eq_mul]; calc
    _≤ ((M+2)^w:ℝ)*(r^w*i w*ρ^w):=mul_le_mul_of_nonneg_right (by exact_mod_cast hf) (by unfold i; positivity)
    _=(((M+2:ℕ):ℝ)*r)^w*i w*ρ^w:=by push_cast; rw [mul_pow]; ring
    _ ≤ _ := by unfold packets; unfold r i at *; gcongr; first | exact overhead_bound _ _|exact one_le_mul_of_one_le_of_one_le (by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) M]) (overhead_bound _ _)

def reserve (N:Captain H j C' d v Y A b r B q k χ) (K M:ℕ) (p:H.ThinP) (ρ Z :ℝ) :=
    (packets j K M*ρ^p.val.card * Z^(blaze p.val).card) * (B*N.conduit.meant p.val k)
def slot (N:Captain H j C' d v Y A b r B q k χ) (K M:ℕ) (ρ Z:ℝ)(p:H.ThinP) (i:Orders M):= reserve N K M p ρ Z * (ρ^i.val)⁻¹
def total (N:Captain H j C' d v Y A b r B q k χ) (K M:ℕ) (ρ Z:ℝ)(p:H.ThinP):= (M+2:ℝ)*reserve N K M p ρ Z

include N
omit hN h2
variable {Z:ℝ}
lemma reserve₀ (p:H.ThinP)(Z:ℝ)(he:0 ≤ Z)(M:ℕ)(ρ:ℝ)(hu:0≤ρ)(K:ℕ) : 0≤ reserve N K M p ρ Z := by
  unfold reserve
  exact mul_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans (package j K M)) (pow_nonneg hu _)) (pow_nonneg he _)) (mul_nonneg N.balance (N.conduit.meant_nonneg k _))

include h2
variable (hZ:ρ^(M+1) ≤ Z)

lemma covers (p:H.ThinP) (K:ℕ): (∑ i:Orders M, slot N K M ρ Z p i*ρ^i.val)=total N K M ρ Z p := by
  unfold slot
  have h (k:ℕ): (ρ^k)⁻¹*ρ^k=1:=by
    have hz:0<ρ:=by linarith
    exact inv_mul_cancel₀ (pow_ne_zero _ hz.ne')
  simp_rw [mul_assoc,h,mul_one,sum_const,card_univ]; unfold total Orders; rw [nsmul_eq_mul,Fintype.card_fin]; push_cast; rfl
include hN hZ hP hM h hρ
lemma account (i:Orders M) : Brush j (slot N K M ρ Z p i) 1 (basis H χ M p i ∘ V) x := by
  have hpos:0<ρ:=by linarith
  have hp:1≤ρ:=by linarith
  have hv:1≤Z:= (one_le_pow₀ hp)|>.trans hZ
  have ht := mul_nonneg N.balance (N.conduit.meant_nonneg k p.val)
  by_cases he: blaze p.val=∅
  swap; · have hY:∀ V d, thermal H χ M p d V=0:= fun V d=> if_neg he
          by_cases hI:i.val=M+1
          · have h0:= ((N.collective p (V x)).2 hP) E V x rfl hM
            refine Brush.shimmy (h0.climb ?_ le_rfl) ?_
            · unfold slot reserve; rw [hI]
              let t:=B*N.conduit.meant p.val k
              have hR:1≤packets j K M*ρ^p.val.card:= one_le_mul_of_one_le_of_one_le (package j K M) (one_le_pow₀ hp)
              rw [← div_eq_mul_inv,le_div_iff₀ (pow_pos hpos _)]
              rw [mul_comm _ (ρ^_)]
              refine mul_le_mul_of_nonneg_right ?_ ht; apply hZ.trans
              have hh:= Finset.card_pos.mpr (nonempty_iff_ne_empty.mpr he); exact (le_self_pow₀ hv (by omega)).trans (le_mul_of_one_le_left (by positivity) hR)
            refine Eventually.of_forall fun i=>?_ ; simp_rw [Function.comp_def,basis,if_pos hI,hY,Finset.sum_const_zero,sub_zero]
          apply Brush.zi _ (mul_nonneg (reserve₀ N p Z (zero_le_one.trans hv) M ρ hpos.le K) (by positivity)) zero_le_one
          exact Eventually.of_forall (fun v=> (show basis H χ M p i _=_ from if_neg hI).trans (hY _ _)) -- annotate
  let f π u:= powerLeaf H χ p (π:Assign p.val M) (V u)
  let g : Assign p.val M →ℕ:= Thermal1020.degree p.val; let d:=i.val
  have hx (T:Finset (Assign p.val M))(hF:∀ i∈ T,d ≤ g i): Brush j (slot N K M ρ Z p i) 1 (fun t=>∑ i∈T,f i t) x:= by
    apply (Brush.spree _ f _ zero_le_one (fun π (_:π∈ T)=> momentCost N hN hP hM h hρ h2 he π)).climb _ le_rfl
    rw [← Finset.sum_mul]; unfold slot reserve
    have ha:= allCharges (j:=j) hN h2 T d hF
    rw [he,card_empty,pow_zero,mul_one]; apply le_trans (mul_le_mul_of_nonneg_right ha ht) (le_of_eq ?_)
    unfold d; ring
  by_cases hI:d=M+1
  · let F:=univ.filter (fun i=>d ≤ g i)
    apply (hx F (fun i h=> (mem_filter.mp h).2)).shimmy
    filter_upwards [lev N hP hM M] with v hv; change basis H χ M p i _ = _
    rw [basis,if_pos hI]; simp_rw [thermal,if_pos he]; rw [← hv]
    change (∑ j,f j v) - (∑ k∈range (M+1),∑ i∈ (univ.filter (fun i=>g i=k)), f i v)=_; rw [← below (fun j=>f j v) g (M+1)]; unfold F; rw [hI]; apply sub_eq_of_eq_add; exact (Finset.sum_filter_add_sum_filter_not ..).symm
  exact (hx (univ.filter (fun j=>g j=d)) (fun i hi=>((mem_filter.mp hi).2 : g i=d).symm.le)).shimmy (Eventually.of_forall fun v=> by change basis H χ M p i _ = _; rw [basis,if_neg hI,thermal,if_pos he])

omit hN hP hM
lemma leafReady : LeafReady χ K ℓ (basis H χ M) v j (slot N K M ρ Z) (total N K M ρ Z) ρ := by
  have hp:0<ρ:=by linarith
  refine ⟨fun i p _=>basis_global i p,fun i p hp' U hU E _ _ _ V x he hV=> by
            subst U; exact account N hp' hU hV h hρ h2 hZ p, by linarith, fun i p _=> ?_,fun i _=>(covers N h2 i K).le,fun i _ V=>(basisLiteral ..).symm⟩
  have hh:0≤Z:= (pow_nonneg hp.le _).trans hZ
  exact mul_nonneg (reserve₀ N i Z hh M ρ hp.le K) (by positivity)
end price
end YM.ConnectedActivityE6.Blaze.Thermal1020
