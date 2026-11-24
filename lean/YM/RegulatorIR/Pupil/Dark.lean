import YM.RegulatorIR.Pupil.Extent

/-!
# Take cut-star radius to infinity
Needed only for the moment equations. Support credit must go away; weigh the
*output of the variation* before estimating. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Pupil
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Momentum Laurent WOne
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {G:Gauge}{I:Type}{p k u m e n r:ℕ}
variable {T : Packet (Foot G) (r+1)}
variable {H C d a:ℝ≥0∞}

lemma match_h (T:Packet (Foot G) (r+1))(A:Fin r→BEdge G)(x:Foot G) : matchT T (Fin.cons (pointA x) A)=chargeT (Momentum.anchored x T) (fun i=> hue (A i)):=by
 unfold matchT chargeT; let f(t:Tuple (Foot G) r):Tuple (Foot G) (r+1):=Fin.cons x t
 let v:Fin (r+1)→BEdge G:= Fin.cons (pointA x) A;let g(z:Tuple (Foot G) (r+1)):=T z*∏ i,hue (v i) (z i)
 have he: Function.support g⊆ Set.range f:=by
    intro z (hz:g z≠0); unfold g at hz; rw [Fin.prod_univ_succ] at hz; rw [show v 0=pointA x from rfl,one_point] at hz; split at hz
    next h=> exact ⟨_,(congr_arg (fun s=>Fin.cons s (Fin.tail z)) h.symm).trans (Fin.cons_self_tail _)⟩
    next h=> simp at hz
 rw [← (show Injective f from fun p q h=>congr_arg Fin.tail h).tsum_eq he];apply tsum_congr;intro p;unfold g;rw [Fin.prod_univ_succ]; rw [show v 0=pointA x from rfl,one_point,if_pos (show f p 0=x from rfl),one_mul]; rfl

lemma hue_t (x:Foot G)(z:Cover){A:BEdge G}(h:TightF z H A): ‖hue A x‖ₑ≤ H*St z (area x):=by unfold hue; rw [← ofReal_norm]; exact le_trans (ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le _ _)) ((ofReal_norm _).trans_le (h x.1))

-- sequence of cutoffs tends to potentially unbounded fields; keep original
-- row moment only. F infinite polynomial functions; no sums over all roots.
variable {x:Foot G} {A:Side→Fin r→BEdge G}{P:Fin r→ BEdge G}
lemma glide_m (hv:a ≠⊤)(hC:H≠⊤)(hx: r ≤u)(ht:Held T u a)(F:∀ z i,TightF (area x) H (A z i))(L:∀ i u, Tendsto (fun z=>hue (A z i) u) atTop (𝓝 (hue (P i) u))) : Tendsto (fun z=>matchT T (Fin.cons (pointA x) (A z))) atTop (𝓝 (matchT T (Fin.cons (pointA x) P))):=by
 simp_rw [match_h]
 let g:= Momentum.anchored x T
 let f(y:Tuple (Foot G) r):ℝ≥0∞:= ‖g y‖ₑ*wall (area x) 1 u y * H^r
 have hz(p): f p ≠ ⊤:= by refine ENNReal.mul_ne_top ?_ (ENNReal.pow_ne_top hC); have hh:= ht x; apply ne_top_of_le_ne_top hv ((term_le (Momentum.anchored x T) (wall (area x) 1 u) p).trans hh)
 have hh:(∑' p,f p)≠⊤:= by unfold f; rw [ENNReal.tsum_mul_right]; exact ENNReal.mul_ne_top (ne_top_of_le_ne_top hv (ht x)) (ENNReal.pow_ne_top hC)
 let R(z:Side)(p:Tuple (Foot G) r):=g p * ∏ i,hue (A z i) (p i)
 have he: Summable fun p=> (f p).toReal := ENNReal.summable_toReal hh -- name
 unfold chargeT; apply tendsto_tsum_of_dominated_convergence he (fun b=> Tendsto.const_mul (g b) (tendsto_finsetProd Finset.univ (fun j _=> L j (b j)))) (Eventually.of_forall ?_)
 intro z p; change ‖R z p‖≤ (f p).toReal; apply (ENNReal.ofReal_le_iff_le_toReal (hz p)).mp; rw [ofReal_norm] ; unfold R; rw [enorm_mul]
 let v(i:Fin r):= hue (A z i) (p i);let b:= wall (area x) 1 1 p; have hp(i:Fin r): ‖v i‖ₑ≤ H*b:=le_trans (hue_t _ _ (F z i)) (mul_le_mul_right (st_w p (area x) i) _)
 have hr (s:Finset (Fin r)): ‖∏ i∈s,v i‖ₑ≤(H*b)^s.card:=by
    induction s using Finset.induction_on with
    | empty=>simp
    | insert i s h ih=> rw [card_insert_of_notMem h,prod_insert h,pow_succ, mul_comm ((H*b)^_),enorm_mul]; exact mul_le_mul' (hp i) ih
 unfold f; rw [mul_assoc]; apply mul_le_mul_right; apply le_trans (hr Finset.univ); rw [card_univ,Fintype.card_fin,mul_pow,mul_comm _ (b^r),show b^r= _ from w_imp (u:=r) (area x) p]; apply mul_le_mul_left (olderW _ _ _ hx p)

-- explicit plateau

def lamps (b:CapG G)(p:Cover) (x:Cover): G.Color := (-(↑((x-p) b.1)):ℝ) • singleR b.2
def scarf (p:Cover)(b:CapG G)(t:Cover→ℝ)(x:Edge Cover): G.Color:= if x.2=b.1 then t (x.1-p) • singleR b.2 else 0
lemma lighting (b:CapG G)(p:Cover) : regalia (lamps b p)=scarf p b 1:=by
 ext1 i;unfold regalia lamps scarf; rw [← sub_smul]; by_cases hh:i.2=b.1
 · simp [hh]
 simp only [Pi.sub_apply,Pi.add_apply, Lattice.step_apply, if_neg (Ne.symm hh)];simp [hh]
variable (c:CapG G)(z:Cover)
lemma oneRateR (k:G.ColorIndex): ‖singleR k‖ₑ=1:=by rw [show singleR k=EuclideanSpace.basisFun _ ℝ k from PiLp.ext (fun i=>by simp [singleR,eq_comm]),← ofReal_norm,(EuclideanSpace.basisFun _ ℝ).norm_eq_one k,ENNReal.ofReal_one] -- name
lemma sky_pay (i: Axis) (x:Cover): ‖(x i:ℝ)‖ₑ≤1+Momentum.extent x:=by
 unfold Momentum.extent; apply le_trans _ (le_add_self);rw [← ofReal_norm,← norm_natAbs,Real.norm_natCast,ENNReal.ofReal_natCast]; exact_mod_cast Finset.single_le_sum (f:=fun i:Axis=>(x i).natAbs) (fun _ _=>Nat.zero_le _) (mem_univ i)
lemma cost_l : TightS z 1 (lamps c z):=by
 intro i; unfold lamps; rw [enorm_smul,oneRateR,mul_one,enorm_neg,one_mul]; exact sky_pay ..
variable {A':Cover→ G.Color}{P':BEdge G}
lemma tall_m (h:TightS z H A') : TightF z (H+H*2) (regalia A'):=by intro i; unfold regalia; apply (enorm_sub_le ..).trans;rw [add_mul]; apply add_le_add (h _); apply le_trans (h _);rw [mul_assoc];exact mul_le_mul_right (st_step ..) _
lemma shine_s (t:Cover→ℝ) (H:∀ v, ‖t v‖ₑ≤1+Momentum.extent v): TightF z 1 (scarf z c t):=by
    intro i;unfold scarf;split
    next h=> rw [enorm_smul,oneRateR,mul_one,one_mul]; exact H _
    next=>simp
-- gap reference infinity

def bonnet (A:Cover→ G.Color) (z:Side) : Cover→ G.Color:= fun i=> if inside z i then A i else 0
lemma bonnet_v (A:Cover→G.Color)(z:Side) : (Function.support (bonnet A z)).Finite:= (Lattice.box z.val).finite_toSet.subset (fun i hi=> (show inside z i from Classical.byContradiction (fun h=> hi (by rw [bonnet,if_neg h]))))
lemma bonnet_h (h:TightS z H A')(v:Side): TightS z H (bonnet A' v):=by intro i; unfold bonnet; split; exact h _; simp
lemma rises_h (A:Cover→G.Color) i: ∀ᶠ z:Side in atTop, regalia (bonnet A z) i= regalia A i:=by filter_upwards [included i.1, included (i.1+step i.2)] with z hz h;unfold regalia bonnet;rw [if_pos hz, if_pos h]

def sachet (A:BEdge G) (z:Side): BEdge G:= fun i=>if inside z i.1 then A i else 0
lemma sachet_s (A:BEdge G)(z:Side): GivesT (sachet A z):= ((Lattice.box z.val).finite_toSet.prod (Set.toFinite (Set.univ:Set Axis))).subset (fun i hi=> ⟨(show inside z i.1 from Classical.byContradiction (fun h=> hi (by rw [sachet,if_neg h]))),Set.mem_univ _⟩)
lemma sachet_h (h:TightF z H P')(v:Side) : TightF z H (sachet P' v):=by intro i; unfold sachet;split;exact h _;simp
lemma rises_v (A:BEdge G) i: ∀ᶠ z:Side in atTop,sachet A z i=A i:= by filter_upwards [included i.1] with z hz; rw [sachet,if_pos hz]
end YM.RegulatorIR.Pupil
