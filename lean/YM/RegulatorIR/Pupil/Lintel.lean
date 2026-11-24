import YM.RegulatorIR.Pupil.Roof

/-!
# Pay just the divergent W1 fan: one link probe difference

Leads plus base stake (s=0). Earlier cost units all requiring exponent rank+order
for this correction. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Pupil
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Momentum Laurent WOne
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {G:Gauge}{I:Type}{p k u m r n:ℕ}
variable {H C d b:ℝ≥0∞}

-- all anchors (make reusable for source array lifts)
def Keeps (T:Packet (Long I) r) (u:ℕ)(c:ℝ≥0∞):Prop:=∀ i:Fin r,∀ x:Long I,quota (fun p:Hold i x=>T p.val) (fun p=> wall (area x) 1 u p.val) ≤ c

def holding0 (i:I)(r:ℕ) : Tuple I r ≃ Hold (0:Fin (r+1)) i:= ⟨fun z=>⟨Fin.cons i z, Fin.cons_zero ..⟩, fun x=>Fin.tail x.val,fun _=>rfl, fun x=>Subtype.ext ((congr_arg (fun a=>Fin.cons a (Fin.tail x.val)) x.property.symm).trans (Fin.cons_self_tail _))⟩
lemma keep_here (T:Packet (Long I) (r+1))(x) : quota (fun p:Hold (0:Fin (r+1)) x=>T p.val) (fun p=>wall (area x) 1 u p.val)=quota (Momentum.anchored x T) (wall (area x) 1 u):=by unfold quota;rw [← (holding0 x r).tsum_eq];apply tsum_congr;intro i; exact congr_arg (‖T (Fin.cons x i)‖ₑ*·) (price_held ..)
lemma keeps_r {T:Packet (Long I) (r+1)}(h:IsSym T)(hv:Held T u C): Keeps T u C:=by
 intro i x;let e:= Equiv.swap 0 i; let f:= heldPerm e 0 x; specialize hv x; rw [← keep_here T x] at hv -- dependent
 apply le_trans _ hv; apply le_of_eq
 unfold quota;have hh:e 0=i:=Equiv.swap_apply_left ..
 rw [←hh, ← f.tsum_eq];apply tsum_congr;intro p; have hx: wall (area x) 1 u (p.val ∘ e)=wall (area x) 1 u p.val:=by unfold Momentum.wall; apply congr_arg (fun i:ℝ≥0∞=> (1+i)^u); exact Equiv.sum_comp e (fun i=>awayZ (area x) (p.val i) 1)
 exact congr_arg₂ (·*·) (congr_arg (fun t:ℝ=>‖t‖ₑ) (h e p.val).symm) hx.symm

lemma tight_add {a b:BEdge G}{x:Cover}{P Q:ℝ≥0∞}(h:TightF x P a)(hk:TightF x Q b): TightF x (P+Q) (a+b):=fun i=> by rw [Pi.add_apply,add_mul]; exact (enorm_add_le ..).trans (add_le_add (h i) (hk i))
lemma tight_setsum (v:Finset (Fin r))(A:Fin r→ BEdge G){p:Cover}{H:ℝ≥0∞}(h:∀ i,TightF p H (A i)): TightF p ((r:ℝ≥0∞)*H) (∑ i∈v,A i):=by
 intro x;rw [Finset.sum_apply];apply (enorm_sum_le ..).trans;apply le_trans (sum_le_sum (fun i (_:i∈v)=> h i x))
 simp_rw [sum_const,nsmul_eq_mul];rw [← mul_assoc];apply mul_le_mul_left; apply mul_le_mul_left; exact_mod_cast (show v.card≤ r by simpa using Finset.card_le_card (subset_univ v)) -- names
lemma peak_f {x:Foot G} (p:Cover) : TightF p 1 (pointA x) := by
 intro i; unfold pointA lone; split_ifs
 · have hr(j:G.ColorIndex): singleR j=EuclideanSpace.basisFun G.ColorIndex ℝ j:=by ext i; simp [singleR,eq_comm]
   rw [hr];rw [← ofReal_norm,(EuclideanSpace.basisFun _ ℝ).norm_eq_one];simp [St]
 rw [enorm_zero];exact bot_le

-- finite support compact correction path ensures both sums are absolute
lemma pledgeR {A:BEdge G}{σ:Cover→G.Color}(h:GivesT A)(hv:(Function.support σ).Finite) : (Function.support (vow (shadowU A σ))).Finite:=by
 let P:= h.union (gives_reg hv) -- doesn't imply support of σ star; use Finset stars
 let t:=hv.toFinset×ˢ (univ:Finset Axis);let S:= h.toFinset ∪ t ∪ t.image fun i=> (i.1-step i.2,i.2)
 have hs: (Function.support (vow (shadowU A σ)))⊆ Set.range (wire S):= (scriptK (f:=4) A σ (by decide) (even_two_mul 2) S (fun i hi=> mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (h.mem_toFinset.mpr hi))))) (fun i h v=> mem_union.mpr (Or.inl (mem_union.mpr (Or.inr (mem_product.mpr ⟨hv.mem_toFinset.mpr h,mem_univ v⟩))))) (fun i h v=> mem_union.mpr (Or.inr (mem_image_of_mem _ (show (i,v)∈t from mem_product.mpr ⟨hv.mem_toFinset.mpr h,mem_univ v⟩))))).suited
 exact (Set.finite_range _).subset hs
lemma pledge {X:I→ PowerSeries ℝ}(T:Packet I p)(h:(Function.support X).Finite): Summable fun z:Tuple I p=> T z*coeff k (pip X z) := summable_of_hasFiniteSupport ((Set.Finite.pi (t:=fun _:Fin p=> Function.support X) (fun _=>h)).subset (fun z hz=> fun i _ H=> hz (by change T z*_=0; rw [show pip X z=0 from Finset.prod_eq_zero (mem_univ i) H,map_zero,mul_zero])))

section Costs
-- sum of first occurrences (prefer any but canonical ambiguity not needed). Counting factor p*card color. budget at held length ν: no tails volume. Generic. finite or infinite color only. New Anchor Pay criterion.
variable (x:Foot G)
lemma touched {T:Packet (Foot G) p}{F:Tuple (Foot G) p→ℝ} (P:Keeps T u C)(Hn:∀ z,F z ≠0→∃ i,(z i).1=x.1) (Hc:∀ z, ‖F z‖ₑ≤ H * ‖T z‖ₑ * wall (area x) 1 u z):
    quota F 1 ≤ p*(Fintype.card G.ColorIndex :ℝ≥0∞) * H * C:=by
 let f(i: Fin p)(j:G.ColorIndex) (z:Tuple (Foot G) p):ℝ≥0∞:= if z i=(x.1,j) then ‖F z‖ₑ else 0
 have hz(z:Tuple (Foot G) p): ‖F z‖ₑ≤ ∑ (i:Fin p),∑ j:G.ColorIndex,f i j z:=by
    by_cases h:F z=0
    · rw [h,enorm_zero];exact bot_le
    obtain ⟨i,hi⟩:=Hn z h; let t:= z i; let j:=t.2
    rw [show ‖F z‖ₑ=f i j z from Eq.symm (if_pos (show z i=(x.1,j) from Prod.ext hi rfl))]; apply le_trans (single_le_sum (fun j (_:j∈Finset.univ)=> bot_le (a:=f i j z)) (mem_univ j)); exact Finset.single_le_sum (fun j _=> show 0 ≤ ∑ k,f j k z from bot_le) (mem_univ i)
 have hh(i:Fin p)(j:G.ColorIndex): ∑' z,f i j z≤ H*C:=by
    let t:Foot G:=(x.1,j)
    have hl:(∑' z,f i j z)=∑' z:Hold i t, ‖F z.val‖ₑ:=by
       convert (tsum_subtype ({z:Tuple (Foot G) p| z i=t}) (fun z=> ‖F z‖ₑ)).symm using 1 <;> first|rfl | exact tsum_congr fun k=> by simp [f,Set.indicator,t]
    rw [hl]; apply le_trans _ (mul_le_mul_right (P i t) H); unfold quota; rw [← ENNReal.tsum_mul_left];apply ENNReal.tsum_le_tsum; intro z; exact (Hc z.val).trans_eq (mul_assoc ..)
 rw [quota_base]; apply le_trans (ENNReal.tsum_le_tsum hz); rw [Summable.tsum_finsetSum (s:=Finset.univ) (f:=fun i z=>∑ j:G.ColorIndex,f i j z) (fun i _=> ENNReal.summable)]; simp_rw [fun i=> Summable.tsum_finsetSum (s:=Finset.univ) (f:=f i) (fun i _=> ENNReal.summable)]; apply le_trans (Finset.sum_le_sum (fun i (_:i∈Finset.univ)=> Finset.sum_le_sum (fun j (_:j∈Finset.univ)=>hh i j))); simp_rw [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin];apply le_of_eq;ring
end Costs
-- approximate helpers
variable {A B:BEdge G}{σ:Cover→ G.Color}
lemma morphs (z:Foot G)(h:A z.1=B z.1): vow (shadowU A σ) z=vow (shadowU B σ) z:= congr_arg (fun i: G.Color=> routeS _ z.2 (i,σ z.1.1,σ (z.1.1+step z.1.2))) h

lemma link_fee (x:Foot G) (h:TightF (area x) H A)(hk:TightF (area x) H B)(ht:TightS (area x) H σ)(ha:GivesT A)(hb:GivesT B)(hv:(Function.support σ).Finite) (hl:∀ z,z≠x.1→A z=B z){T:Packet (Foot G) r}(hc:Keeps T u C)(hp:r+k≤u):
 ‖rhyme (vow (shadowU A σ)) T k-rhyme (vow (shadowU B σ)) T k‖ₑ ≤ r*(Fintype.card G.ColorIndex:ℝ≥0∞)*(2*billow G H k r)*C:=by
 let v:=vow (shadowU A σ); let w:=vow (shadowU B σ); let f(z:Tuple (Foot G) r):= T z* (coeff k (pip v z)-coeff k (pip w z))
 have ht' z : f z ≠0 → ∃ i,(z i).1=x.1:=by
    intro hz; by_contra! h; apply hz
    unfold f;rw [show pip v z=pip w z from Finset.prod_congr rfl (fun i _=> morphs (z i) (hl _ (h i))),sub_self,mul_zero] -- f let
 have hx(z): ‖f z‖ₑ≤ 2*billow G H k r* ‖T z‖ₑ * wall (area x) 1 u z :=by
    let M:= billow G H k r; let N:=wall (area x) 1 u z
    have hb:billow G H k r * wall (area x) 1 (r+k) z ≤ M*N:= mul_le_mul_right (olderW (area x) _ _ hp z) _
    unfold f; rw [enorm_mul];apply le_trans (mul_le_mul_right (le_trans (enorm_sub_le ..) (add_le_add ((wave_fee h ht z k).trans hb) ((wave_fee hk ht z k).trans hb))) ‖T z‖ₑ)
    apply le_of_eq; change _ = 2*M* _ *N; ring
 unfold rhyme; rw [← (pledge T (k:=k) (pledgeR ha hv)).tsum_sub (pledge T (k:=k) (pledgeR hb hv))]; simp_rw [← mul_sub]; apply enorm_tsum_le_tsum_enorm.trans; rw [← quota_base]; exact touched x hc ht' hx
end YM.RegulatorIR.Pupil
