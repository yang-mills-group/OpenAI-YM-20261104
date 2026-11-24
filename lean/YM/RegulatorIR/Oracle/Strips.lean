import YM.RegulatorIR.Oracle.Keel

/-! Quarry bounds. Native lengths here in quarry coordinates. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry
open Pert.Bulk (Market sep)
open scoped Topology ENNReal NNReal BigOperators Classical Matrix
variable {X Y A B C V J K :Type} {S T U:Side→Type}
variable (W:Quarry X A S) (F:Quarry Y B T) (D:Quarry V C U) {p:Side} {σ v:ℝ}

def liftsE (x y:Cover)(σ:ℝ):= ENNReal.ofReal (Real.exp (σ*sep x y))
lemma lifts_pos (x y:Cover){σ:ℝ}(h:0≤σ): 1 ≤ liftsE x y σ:=by unfold liftsE; rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg h (Pert.Bulk.sep_nonneg ..)))
def slateE (σ:ℝ)(h:0≤σ): Tariff Cover where
 road x y:= liftsE x y σ
 unit x y:=lifts_pos x y h
 own x:=by simp [liftsE,Pert.Bulk.sep_self]
 symm x y:=by unfold liftsE;rw [Pert.Bulk.sep_comm]
 tri x y z:=by
    unfold liftsE;rw [← ENNReal.ofReal_mul (by positivity),← Real.exp_add,← mul_add]; exact ENNReal.ofReal_le_ofReal (Real.exp_monotone (mul_le_mul_of_nonneg_left (Pert.Bulk.sep_triangle ..) h))

variable {L M: Layer X Y} {R:Layer Y V}
def chestE (W:Quarry X A S)(F:Quarry Y B T)(σ:ℝ)(K:Layer X Y)(c:ℝ≥0∞):Prop:= ∀ i,quota (K i) (fun j=>liftsE (W.boom i) (F.boom j) σ)≤c
namespace chestE
variable {W F D}{σ:ℝ}{c d:ℝ≥0∞}
lemma billed (h:chestE W F σ L c) (hP:0≤σ)(hv:c≠⊤): Billed L:=billed_supp (x:=W.boom) (y:=F.boom) (q:=slateE σ hP) h hv
lemma toll (h:chestE W F σ L c)(hh:d≥c):chestE W F σ L d:=fun i=>(h i).trans hh
lemma fewer (h:chestE W F σ L c)(hh:v≤σ): chestE W F v L c:=fun i=>(quota_mono _ (fun _=> ENNReal.ofReal_le_ofReal (Real.exp_monotone (mul_le_mul_of_nonneg_right hh (Pert.Bulk.sep_nonneg ..))))).trans (h i)
lemma add (h:chestE W F σ L c)(hh:chestE W F σ M d): chestE W F σ (L+M) (c+d):=fun i=> (quota_add (L i) (M i) _).trans (add_le_add (h i) (hh i))
lemma sub (h:chestE W F σ L c)(hh:chestE W F σ M d): chestE W F σ (L-M) (c+d):=fun i=> (quota_sub (L i) (M i) _).trans (add_le_add (h i) (hh i))
lemma smul (h:chestE W F σ L c)(a:ℝ):chestE W F σ (a • L) (‖a‖ₑ*c):=fun i=> (quota_times (L i) _ a).trans_le (mul_le_mul_right (h i) _)
lemma lapB (h:chestE W F σ L c)(hh:chestE F D σ R d)(hp:0≤σ): chestE W D σ (lap L R) (c*d):=by
 let C:= slateE σ hp
 intro i
 let f(y:Y)(z:V):=L i y*R y z
 let t(z):=C.road (W.boom i) (D.boom z)
 let s (y):=C.road (W.boom i) (F.boom y)
 let u(y z):=C.road (F.boom y) (D.boom z)
 apply le_trans (inside_quota (X:=V) (Function.swap f) t)
 unfold quota;rw [ENNReal.tsum_comm]
 let a(y):= R y; let v(y z):= liftsE (F.boom y) (D.boom z) σ
 have hx(y:Y): (∑' z,‖f y z‖ₑ * t z) ≤ ‖L i y‖ₑ*s y * d:=by
    calc
       _ ≤ ∑' z, (‖L i y‖ₑ*s y)* (‖R y z‖ₑ * v y z):=by
              apply ENNReal.tsum_le_tsum; intro z;unfold f; rw [enorm_mul,mul_mul_mul_comm]; exact mul_le_mul_right (C.tri ..) _
       _ ≤ _:=by rw [ENNReal.tsum_mul_left]; exact mul_le_mul_right (hh y) _
 apply (ENNReal.tsum_le_tsum hx).trans;rw [ENNReal.tsum_mul_right]; exact mul_le_mul_left (h i) _
lemma bright :chestE W W σ (ID X) 1:=by
 intro i; rw [quota,tsum_eq_single i]; simp [Quadratic.ID,liftsE,Pert.Bulk.sep_self]; exact fun z hz=>by simp [Quadratic.ID,hz.symm]
end chestE

def FundE (W:Quarry X A S)(F:Quarry Y B T)(σ:ℝ)(K:Layer X Y):= ∃ c≠⊤, chestE W F σ K c ∧ chestE F W σ (Function.swap K) c
variable {W F D}
lemma FundE.buys (h:FundE W F σ L)(hx:0≤σ): Billed L ∧ Billed (Function.swap L):=by obtain ⟨c,hc,H,h⟩:=h; exact ⟨H.billed hx hc,h.billed hx hc⟩
lemma lap_flip {P:Layer X Y}{U:Layer Y V}: Function.swap (lap P U)= lap (Function.swap U) (Function.swap P):=by ext1 i;ext1 j; exact tsum_congr fun _=> mul_comm ..
lemma FundE.forw (h:FundE W F σ L)(hh:FundE F D σ R)(hp:0≤σ): FundE W D σ (lap L R):=by
 obtain ⟨c,hc,h₁,h₂⟩:=h; obtain ⟨d,hd,h,h'⟩:=hh; refine ⟨c*d,by finiteness,h₁.lapB h hp,?_⟩; rw [lap_flip,mul_comm];exact h'.lapB h₂ hp

-- anchor sum billing at fixed positions can be paid with finite cost for post-step trunc patches
lemma finiteFund  [Fintype A](h:Albedo W F L)(hc: ∀ i, (support (L i)).Finite)(σ:ℝ): ∃ c≠⊤,chestE W F σ L c:=by
 let Q(x:X):= quota (L x) (fun j=>liftsE (W.boom x) (F.boom j) σ)
 have hp(x:X): Q x ≠ ⊤:=by
    unfold Q quota;rw [tsum_eq_sum (s:=(hc x).toFinset)]; exact ENNReal.sum_ne_top.mpr (fun _ _=> ENNReal.mul_ne_top (by finiteness) (by unfold liftsE;finiteness)); intro i hi; have ht: L x i=0:=notMem_support.mp (fun hh=>hi ((hc x).mem_toFinset.mpr hh));simp [ht]
 let p(i:A):= W.toFull.symm (0,i); let c:= Finset.univ.sup (fun i=>Q (p i))
 refine ⟨c,lt_top_iff_ne_top.mp (Finset.sup_lt_iff (by simp)|>.mpr fun i _=>lt_top_iff_ne_top.mpr (hp _)),fun i=>le_trans ?_ (Finset.le_sup (f:=fun i=>Q (p i)) (Finset.mem_univ (W.cabin i)))⟩
 let x:= p (W.cabin i); let d:= W.boom i; have he:W.shiftB d x=i:= W.toFull.injective (by rw [W.to_shift];simp [x,p,boom,cabin];rfl) -- proof simp field notation
 change Q i≤Q x;apply le_of_eq; unfold Q
 rw [← quota_perm (F.shiftB d) _ _]
 apply tsum_congr; intro j
 dsimp only [Function.comp_apply]
 rw [show L i (F.shiftB d j)=_ from he ▸ h x j d]; rw [places]
 apply congr_arg; have hl:W.boom i=d+W.boom x:=by nth_rw 1 [← he]; exact W.places _ _
 rw [hl]; unfold liftsE; rw [add_comm d,add_comm d,Pert.Bulk.sep_shift]

lemma columns_paid (h: Albedo W F L) [Fintype A] (hv:∀ i,(support (L i)).Finite): ∀ i,(support (Function.swap L i)).Finite:=by
 intro i; let p(t:A) := W.toFull.symm (0,t)
 let s:Finset (A×Y):=Finset.univ.biUnion fun t=> (hv (p t)).toFinset.image (fun q=>(t,q))
 let f (v:A×Y):= W.shiftB (F.boom i-F.boom v.2) (p v.1)
 apply Set.Finite.subset (Finset.finite_toSet (s.image f)); intro x hx
 let y:= W.cabin x;let z:= F.shiftB (-(W.boom x)) i
 have hs:W.shiftB (-(W.boom x)) x=p y:= W.toFull.injective (by rw [W.to_shift]; simp [p,y])
 have hh: z∈ support (L (p y)):=by change L _ _ ≠0;rw [← hs]; exact (h ..).trans_ne (show L x i≠0 from hx)
 refine Finset.mem_image.mpr ⟨(y,z),Finset.mem_biUnion.mpr ⟨y,Finset.mem_univ _,Finset.mem_image.mpr ⟨z,(hv _).mem_toFinset.mpr hh,rfl⟩⟩, W.toFull.injective ?_⟩; change W.toFull (W.shiftB (F.boom i - F.boom z) _) = _; rw [W.to_shift]; unfold z;rw [places]; simp [boom,cabin,p,y]

lemma FundE.bill_s [Fintype A][Fintype B](h:Albedo W F L)(hv:∀ i,(support (L i)).Finite)(σ:ℝ): FundE W F σ L:=by
 obtain ⟨c,hc,h₀⟩:=finiteFund h hv σ; obtain ⟨r,hr,hq⟩:= finiteFund h.swap (columns_paid h hv) σ; exact ⟨c⊔r,ne_of_lt (sup_lt_iff.mpr ⟨lt_top_iff_ne_top.mpr hc, lt_top_iff_ne_top.mpr hr⟩),h₀.toll le_sup_left,hq.toll le_sup_right⟩
end YM.RegulatorIR.Oracle
