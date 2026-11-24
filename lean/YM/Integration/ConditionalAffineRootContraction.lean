import YM.Integration.ConditionalCovarianceRoots
import YM.Integration.WilsonWalkMatrixSecant
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Carrier
import YM.Next.STATIONARY.Level.SliceGate
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Charges
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Bore

/-! The literal minimum number of nearest-neighbor physical links joining all
named torus sites. A minimizing connected set has no removable link. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ConditionalPhysicalSpan
open Function Finset Lattice Wilson RG FreeResolvent FreeResolvent.Stars
open ConnectedActivityE6.SliceRows WilsonWalkMatrixSecant
open scoped Classical BigOperators
variable {c : Side} {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]

omit [Fintype ι] in
def Connects (E : Finset (Edge (Site c))) (o : Site c) (p : ι→Site c) :=
  ∀ i, ∃ w : Walk, stop o w=p i ∧ (occurrences o w).toFinset⊆E

def routed (o : Site c) (p : ι→Site c) : Finset (Edge (Site c)) :=
  Finset.univ.biUnion (fun i => (occurrences o (carriage o (p i))).toFinset)

theorem routed_connects (o : Site c) (p : ι→Site c) : Connects (routed o p) o p := by
  intro i
  refine ⟨carriage o (p i),deposits ..,?_⟩
  intro a ha
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,ha⟩

private theorem exists_set (o : Site c) (p : ι→Site c) :
    ∃ n : ℕ, ∃ E : Finset (Edge (Site c)), E.card=n ∧ Connects E o p :=
  ⟨_,routed o p,rfl,routed_connects o p⟩

/-- Auxiliary vertices and all periodic nearest-neighbor paths are allowed.
The set contains physical positive links; repeated traversals have one cost. -/
def span (o : Site c) (p : ι→Site c) : ℕ := Nat.find (exists_set o p)

theorem realized (o : Site c) (p : ι→Site c) :
    ∃ E : Finset (Edge (Site c)), E.card=span o p ∧ Connects E o p := Nat.find_spec (exists_set o p)

theorem least {E : Finset (Edge (Site c))} {o : Site c} {p : ι→Site c} (h : Connects E o p) :
    span o p ≤ E.card := Nat.find_min' (exists_set o p) ⟨E,rfl,h⟩

theorem irredundant {E : Finset (Edge (Site c))} {o : Site c} {p : ι→Site c}
    (h : E.card=span o p) {e : Edge (Site c)} (he : e∈E) : ¬Connects (E.erase e) o p := by
  intro hh
  have hm := least hh
  rw [←h] at hm
  exact (Nat.not_le_of_gt (Finset.card_erase_lt_of_mem he)) hm

omit [Fintype ι] [Fintype κ] in
private theorem relabel {o : Site c} {p : ι → Site c} {q : κ → Site c}
    (h : Set.range p = Set.range q) {H : Finset (Edge (Site c))} (hc : Connects H o p) :
    Connects H o q := by
  intro z
  have hz : q z ∈ Set.range p := h.symm ▸ Set.mem_range_self z
  obtain ⟨i, hi⟩ := hz
  rw [←hi]
  exact hc i

theorem same_sites (o : Site c) (p : ι → Site c) (q : κ → Site c) (h : Set.range p = Set.range q) :
    span o p = span o q := by
  obtain ⟨P, hP, cp⟩ := realized o p
  obtain ⟨Q, hQ, cq⟩ := realized o q
  apply le_antisymm
  · exact (least (relabel h.symm cq)).trans_eq hQ
  · exact (least (relabel h cp)).trans_eq hP

theorem routed_price (o : Site c) (p : ι→Site c) :
    (span o p:ℝ)≤∑ i, (taxi c).d o (p i) := by
  have hc : (routed o p).card ≤ ∑ i, ((occurrences o (carriage o (p i))).toFinset).card :=
    Finset.card_biUnion_le
  have hl (i : ι) : ((occurrences o (carriage o (p i))).toFinset).card ≤ Laurent.size (lift (p i-o)) := by
    calc
      _ ≤ (occurrences o (carriage o (p i))).length := List.toFinset_card_le _
      _ = _ := by rw [length_occurrences,carriage,Stationary.route_length,sub_zero]
  change (span o p : ℝ) ≤ ∑ i, (Laurent.size (lift (p i - o)) : ℝ)
  exact_mod_cast (least (routed_connects o p)).trans (hc.trans (Finset.sum_le_sum fun i _ => hl i))

def sites (i j : Site c) {n : ℕ} (l : Fin n→Site c) : Fin (n+2)→Site c := Fin.cons i (Fin.cons j l)

theorem cost (v i j : Site c) {n : ℕ} (l : Fin n→Site c) :
    (span v (sites i j l):ℝ) ≤ costs (taxi c) v i j l := by
  have H := routed_price v (sites i j l)
  simpa [sites,Fin.sum_univ_succ,costs,rays,add_assoc] using H

structure Rooted (n : ℕ) (a : ι→Site c) (b : κ→Site c) (p : τ→Site c) (v : Site c)
    (W : ι→κ→(Fin n→τ)→Bool) (γ M : ℝ) (F : ι→κ→(Fin n→τ)→ℝ) : Prop where
  limit : ∑ i,∑ j,∑ l : Fin n→τ,
    (if W i j l then Real.exp (γ*(span v (sites (a i) (b j) (p∘l)):ℝ))* |F i j l| else 0) ≤ M

/-- Sum two independently priced tensors at the same genuine retained position. -/
theorem Rooted.add {n : ℕ} {a : ι→Site c} {b : κ→Site c} {p : τ→Site c} {v : Site c}
    {W : ι→κ→(Fin n→τ)→Bool} {γ M N : ℝ} {F H : ι→κ→(Fin n→τ)→ℝ}
    (hF : Rooted n a b p v W γ M F) (hH : Rooted n a b p v W γ N H) :
    Rooted n a b p v W γ (M+N) (fun i j l => F i j l+H i j l) := by
  constructor
  apply le_trans _ (add_le_add hF.limit hH.limit)
  simp only [←Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => ?_
  by_cases h : W i j l=true
  · simp only [h,ite_true,←mul_add]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (Real.exp_pos _).le
  simp [h]

/-- Exponential surplus pays an arbitrary fixed power of the actual shortest
connected span, including tuples with repeated field or root addresses. -/
def momentFee (γ : ℝ) (k : ℕ) := (k.factorial:ℝ)*(γ/2)⁻¹^k*Real.exp (γ/2)

theorem momentFee_nonneg {γ : ℝ} (hγ : 0<γ) (k : ℕ) : 0 ≤ momentFee γ k := by
  unfold momentFee; positivity

theorem absorb {γ s : ℝ} (hγ : 0<γ) (hs : 0 ≤ s) (k : ℕ) :
    (1+s)^k*Real.exp (γ/2*s) ≤ momentFee γ k*Real.exp (γ*s) := by
  let a := γ/2
  have ha : 0<a := div_pos hγ (by norm_num)
  have hh := (div_le_iff₀ (by positivity : 0<(k.factorial:ℝ))).mp
    (Real.pow_div_factorial_le_exp (a*(1+s)) (mul_nonneg ha.le (by linarith : 0≤1+s)) k)
  have hscl : (1+s)^k=a⁻¹^k*(a*(1+s))^k := by
    rw [←mul_pow,←mul_assoc,inv_mul_cancel₀ ha.ne',one_mul]
  calc
    _ ≤ (a⁻¹^k*(Real.exp (a*(1+s))*(k.factorial:ℝ)))*Real.exp (a*s) := by
      rw [hscl]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by positivity)) (Real.exp_pos _).le
    _ = momentFee γ k*Real.exp (γ*s) := by
      change _ = (k.factorial:ℝ)*a⁻¹^k*Real.exp a*Real.exp (γ*s)
      rw [show γ*s=a*s+a*s by dsimp [a]; ring,show a*(1+s)=a+a*s by ring,Real.exp_add,Real.exp_add]
      ring

theorem Rooted.moment {n : ℕ} {a : ι→Site c} {b : κ→Site c} {p : τ→Site c} {v : Site c}
    {W : ι→κ→(Fin n→τ)→Bool} {γ M : ℝ} {F : ι→κ→(Fin n→τ)→ℝ}
    (h : Rooted n a b p v W γ M F) (hγ : 0<γ) (k : ℕ) :
    (∑ i,∑ j,∑ l : Fin n→τ, if W i j l then
      let s : ℝ := span v (sites (a i) (b j) (p∘l))
      (1+s)^k*Real.exp ((γ/2)*s)* |F i j l| else 0) ≤ momentFee γ k*M := by
  apply le_trans _ (mul_le_mul_of_nonneg_left h.limit (momentFee_nonneg hγ k))
  simp only [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => ?_
  by_cases hw : W i j l=true
  · simp only [hw,ite_true,←mul_assoc]
    exact mul_le_mul_of_nonneg_right (absorb hγ (Nat.cast_nonneg _) k) (abs_nonneg _)
  simp [hw]

/-- Any of the original retained-position estimates immediately prices the
actual shortest connected physical link span with the very same constants. -/
theorem original {n : ℕ} {a : ι→Site c} {b : κ→Site c} {p : τ→Site c} {v : Site c}
    {W : ι→κ→(Fin n→τ)→Bool} {γ M : ℝ} {F : ι→κ→(Fin n→τ)→ℝ}
    (hγ : 0≤γ) (h : NearStar n (taxi c) a b p v W γ M F) : Rooted n a b p v W γ M F := by
  constructor
  apply le_trans _ h.limit
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => ?_
  by_cases hw : W i j l=true
  · simp only [hw,ite_true]
    exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left (cost ..) hγ)) (abs_nonneg _)
  simp [hw]

end YM.Integration.ConditionalPhysicalSpan

/-! Absolute paired half-logarithm on the authentic uncut conditional tree Gram. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ConditionalAffineIdealLog
open Function Set Filter Lattice RG Wilson Tree Precision Matrix MeasureTheory Bloch
  FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Lever FreeResolvent.Mark FreeResolvent.Stars
  PhysicalNext.Repeat.Greenbelt AnalyticBridge.RelativeLogdet AnalyticBridge.RelativeLogdet.Ink
  AnalyticBridge.RelativeLogdet.Differential ConditionalTreeCovarianceJets ConditionalTreeCovarianceSums
  ConditionalCovarianceCutoff
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {t : S.Choices} {p : Clip} {W : PathData G}
variable {n : ℕ} {σ A : ℝ}
local notation "V" => ray G c

def diagonal (r : Reserve S) (t : S.Choices) (p : Clip) (W : PathData G) (i : raw G f) (B : Vec G c 1) :=
  (logKernel (whole S (allot r) t p W all 0) i i - logKernel (whole S (allot r) t p W all B) i i)/2

theorem flat (r : Reserve S) (i : raw G f) : diagonal r t p W i 0=0 := by simp [diagonal]

private theorem sharp (hs : 0<σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (F U : Forest S.ratio) (z : Site c) (h : changed S F U z) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) 1)
    {u : ℝ} (hu : 0 ≤ u) (l : List (Option (raw G c))) (hl : l.length ≤ n) (hz : l≠[]) :
    let d := width G S.patch S.kernel p n A σ
    let H := crest S t (W:=W) (T:=F) (U:=U) (p:=p) all
    (park (native c) hearth d z).Bill (native c) (home S) (home S) l (4*(n+1:ℕ)*d)
      (earnings G S.patch S.kernel p n A σ * attenuation u^2) (jet (guides V) (action H u) l (0,θ)) := by
  intro d H
  have P := gauged G S.patch S.kernel p n hs ha
  have hh := (mast S t hs ha hW he h all hθ).cost l hl P hu (position_move _ _ P.pos.le) (home_volume S 1 _ P.pos)
  simpa only [earnings,charges,if_neg (ne_of_gt (List.length_pos_iff.mpr hz)),mul_one,attenuation,drain,sq,mul_assoc]
    using hh

private theorem regular (hs : 0<σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (r : Reserve S) {u : ℝ} (hu : 0 ≤ u) (l : List (raw G c)) (hl : l.length ≤ n) (hz : l≠[]) (i : raw G f) :
    let d := width G S.patch S.kernel p n A σ
    (marks G c d).pay l (home S i)* |jet V (action (whole S (allot r) t p W all) u) l 0 i i|≤
      earnings G S.patch S.kernel p n A σ*attenuation u^2 := by
  intro d
  let F := allot r
  let H := crest S t (W:=W) (T:=F) (U:=F) (p:=p) all
  have h := change_draw r r (0:Site c) (fun _ _ => rfl)
  have hy : (0:ℝ)∈Icc (0:ℝ) 1 := Set.left_mem_Icc.mpr zero_le_one
  have hn : l.map some ≠ [] := by simpa using hz
  have hh := (sharp (t:=t) (p:=p) hs ha hW he F F 0 h hy hu (l.map some) (by simpa using hl) hn).row.entry i i
  have sm := (mast S t (p:=p) (n:=n) hs ha hW he h all hy).sees hu (gum_pos G S.patch S.kernel p)
  have hq : (fun B => action H u (B,0))=action (whole S F t p W all) u := by
    funext B; exact congrArg (fun C => resolve C u) (now F F t p all B)
  rw [restriction V l 0 (smooth_of_le sm hl),hq,parks,(native c).weight_self,one_mul] at hh
  exact hh

private theorem changed_resolvent (hs : 0<σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (r s : Reserve S) (z : Site c) (hc : ∀ w, w≠z → r w=s w) {u : ℝ} (hu : 0 ≤ u)
    (l : List (raw G c)) (hl : l.length<n) (i : raw G f) :
    let d := width G S.patch S.kernel p n A σ
    let J r := jet V (action (whole S (allot r) t p W all) u) l 0 i i
    (native c).weight d (home S i) z*(marks G c d).pay l (home S i)* |J s-J r|≤
      earnings G S.patch S.kernel p n A σ*attenuation u^2 := by
  intro d J
  let F := allot r
  let U := allot s
  let H := crest S t (W:=W) (T:=F) (U:=U) (p:=p) all
  have hd := change_draw r s z hc
  have M := recovers (v:=V) (F:=action H u) (γ:=4*(n+1:ℕ)*d) (d:=d) (x:=z) (a:=home S) (p:=hearth) l
    (fun θ hθ => smooth_of_le ((mast S t (p:=p) (n:=n) hs ha hW he hd all hθ).sees hu (gum_pos G S.patch S.kernel p)) (Nat.succ_le_of_lt hl))
    (fun θ hθ => sharp (t:=t) (p:=p) hs ha hW he F U z hd hθ hu (none::l.map some) (by simpa using Nat.succ_le_of_lt hl) (List.cons_ne_nil _ _)) i i
  have h0 (B : Vec G c 1) : action H u (B,0)=action (whole S F t p W all) u B :=
    congrArg (fun C => resolve C u) (now F U t p all B)
  have h1 (B : Vec G c 1) : action H u (B,1)=action (whole S U t p W all) u B :=
    congrArg (fun C => resolve C u) (thenAt F U t p all B)
  simpa only [h0,h1,(native c).weight_self,one_mul,Matrix.sub_apply] using M.1


private theorem gram (hs : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (r : Reserve S) (q : Admit) :
    let Q := whole S (allot r) t p W q
    ContDiffAt ℝ n Q 0 ∧ ∀ᶠ y in 𝓝 0, (Q y).PosDef := by
  intro Q
  have h := mast S t (p:=p) (n:=n) hs ha hW he (change_draw r r 0 (fun _ _ => rfl)) q
    (Set.left_mem_Icc.mpr zero_le_one)
  have hc : ContDiffAt ℝ n Q 0 := by
    apply (h.smooth.comp (0:Vec G c 1) (contDiffAt_id.prodMk (contDiffAt_const (c:=(0:ℝ))))).congr_of_eventuallyEq
    exact Eventually.of_forall fun y => (now (allot r) (allot r) t p q y).symm
  have hg : Gap (Q 0) (gum G S.patch S.kernel p) := by simpa only [now] using h.gap
  have hr := gum_pos G S.patch S.kernel p
  have hy := holds hc.continuousAt hg _ (half_lt_self hr) (native c) (home S)
  exact ⟨hc,hy.mono fun y hQ => AnalyticBridge.LocalGaussianLaws.gap_positive (whole_symm _ _ y) hQ (half_pos hr)⟩

private theorem density_jet (hs : 0<σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (r : Reserve S) (i : raw G f) (l : List (raw G c)) (hl : l.length ≤ n) (hz : l≠[]) {u : ℝ} (hu : 0 ≤ u) :
    let Q := whole S (allot r) t p W all
    jet V (fun B => density (Q B) u i i) l 0 = -(jet V (action Q u) l 0 i i) := by
  intro Q
  have H := gram (t:=t) (p:=p) (n:=n) hs ha hW he r all
  have sm : ContDiffAt ℝ l.length (TestD.action Q u) 0 :=
    action_smooth (IsUnit.mk0 _ (shift_posDef H.2.self_of_nhds hu).det_pos.ne') (smooth_of_le H.1 hl)
  change jet V (fun B => (attenuation u • (1:Matrix (raw G f) (raw G f) ℝ)) i i-(action Q u B) i i) l 0=_
  rw [jet_sub V l contDiffAt_const (typed sm i i),jet_const V l hz,zero_sub,TestD.entry V l sm]

theorem spectral (hs : 0<σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (r : Reserve S) (i : raw G f) :
    ContDiffAt ℝ n (diagonal r t p W i) 0 ∧ ∀ (l : List (raw G c)), l.length ≤ n → l≠[] →
      let J u := jet V (fun B => density (whole S (allot r) t p W all B) u i i) l 0
      IntegrableOn J (Ioi 0) ∧ jet V (diagonal r t p W i) l 0 = -(1/2:ℝ)*(∫ u in Ioi 0,J u) := by
  let Q := whole S (allot r) t p W all
  let F := fun B => logKernel (Q B) i i
  have hg := gram (t:=t) (p:=p) (n:=n) hs ha hW he r all
  have hx := annotated_log V hg.1 hg.2 i i
  have hA : diagonal r t p W i = fun y => (1/2:ℝ) • (F 0-F y) := by
    funext y; simp [diagonal,F,Q,smul_eq_mul,div_eq_mul_inv,mul_comm]
  have sm : ContDiffAt ℝ n (fun y => F 0-F y) 0 := contDiffAt_const.sub hx.1
  refine ⟨hA.symm ▸ sm.const_smul _,?_⟩
  intro l hl hz J
  obtain ⟨hi,hj⟩ := hx.2 l hl
  refine ⟨hi,?_⟩
  rw [hA,jet_const_smul V l _ (smooth_of_le sm hl),jet_sub V l contDiffAt_const (smooth_of_le hx.1 hl),
    jet_const V l hz,zero_sub,smul_eq_mul]
  change (1/2:ℝ)*(-jet V F l 0)=_
  rw [hj]; ring

/-- Both absolute charged entries of the paired full physical log on any flat
ordered field list.  Its relative spectral density is integrated before taking
the norm, with no torus trace or positive-power loss. -/
theorem entries (hs : 0<σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (r s : Reserve S) (z : Site c) (hc : ∀ y, y≠z → r y=s y) (i : raw G f) (l : List (raw G c)) (hl : l.length<n) :
    let d := width G S.patch S.kernel p n A σ
    let P := (marks G c d).pay l (home S i)
    let M := earnings G S.patch S.kernel p n A σ
    let K (t₀ : Reserve S) := jet V (diagonal t₀ t p W i) l 0
    P* |K r| ≤ M/2 ∧ (native c).weight d (home S i) z*P* |K s-K r| ≤ M/2 := by
  intro d P M K
  have hM : 0 ≤ M := (gauged G S.patch S.kernel p n hs ha).meter_abs
  by_cases hz : l=[]
  · subst l
    simpa [K,zeroth,flat] using And.intro (div_nonneg hM (by norm_num : (0:ℝ)≤2)) (div_nonneg hM (by norm_num : (0:ℝ)≤2))
  let J (r : Reserve S) u := jet V (fun B => density (whole S (allot r) t p W all B) u i i) l 0
  let R (r : Reserve S) u := jet V (action (whole S (allot r) t p W all) u) l 0 i i
  have K₀ (r : Reserve S) := (spectral (t:=t) (p:=p) (n:=n) hs ha hW he r i).2 l hl.le hz
  have score (r : Reserve S) : K r= -(1/2:ℝ)*(∫ u in Ioi 0,J r u) := (K₀ r).2
  have X (r : Reserve S) {u : ℝ} (hu : 0 ≤ u) : J r u = -R r u :=
    density_jet hs ha hW he r i l hl.le hz hu
  have hP : 0 ≤ P := (FreeResolvent.Mark.pay_pos ..).le
  have hq := Differential.Speech.judge hP (K₀ r).1 (C:=M) (by
    intro u hu
    change P * |J r u| ≤ M * attenuation u ^ 2
    rw [X r hu.out.le, abs_neg]
    exact regular hs ha hW he r hu.out.le l hl.le hz i)
  have ht := Differential.Speech.judge (mul_nonneg ((native c).weight_nn ..) hP) ((K₀ s).1.sub (K₀ r).1) (C:=M) (by
    intro u hu
    change (native c).weight d (home S i) z*P* |J s u-J r u|≤_
    rw [X s hu.out.le,X r hu.out.le,show -R s u - -R r u=-(R s u-R r u) by ring,abs_neg]
    exact changed_resolvent hs ha hW he r s z hc hu.out.le l hl i)
  constructor
  · rw [score,abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
    linarith only [hq.2]
  rw [score,score,←mul_sub,←integral_sub (K₀ s).1 (K₀ r).1,abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  have hb : (native c).weight d (home S i) z*P* |∫ u in Ioi 0,J s u-J r u| ≤ M := ht.2
  linarith only [hb]

local notation "Slot" => Co S.patch.L (PAC G 1)

def key (D : StepData c f) (o : Site c) (j : Co D.patch.L (PAC G 1)) : raw G f :=
  (splitCo D.ratio (PAC G 1)).symm (o,j)

theorem home_key (o : Site c) (j : Slot) : home S (key S o j)=o := by
  let E := splitCo S.ratio (PAC G 1)
  have h : home (G:=G) (r:=1) S=Prod.fst ∘ E := funext fun i => by simp only [home,E,Function.comp_apply,split_co]
  rw [h]
  change (E (E.symm (o,j))).1 = o
  rw [Equiv.apply_symm_apply]

theorem collect_root (o : Site c) (w : raw G f → ℝ) :
    (∑ i : raw G f, if home S i=o then w i else 0) = ∑ j : Slot, w (key S o j) := by
  let E := splitCo S.ratio (PAC G 1)
  rw [←E.symm.sum_comp (fun i : raw G f => if home S i=o then w i else 0),Fintype.sum_prod_type]
  change (∑ a : Site c, ∑ j : Slot, if home S (key S a j)=o then w (key S a j) else 0) = _
  rw [Finset.sum_eq_single o]
  · simp [home_key]
  · intro a _ hne; simp [home_key,hne]
  · simp

private lemma uniform_sum {ι : Type} [Fintype ι] {p C : ℝ} (hp : 0 ≤ p) (a : ι → ℝ)
    (ha : ∀ i, p * |a i| ≤ C) : p* |∑ i, a i| ≤ (Fintype.card ι:ℝ)*C := by
  calc _ ≤ p * ∑ i, |a i| := mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hp
       _ = ∑ i, p* |a i| := Finset.mul_sum ..
       _ ≤ ∑ _ : ι, C := Finset.sum_le_sum fun i _ => ha i
       _ = _ := by simp



def root (r : Reserve S) (t : S.Choices) (p : Clip) (W : PathData G) (o : Site c) (B : Vec G c 1) :=
  ∑ i : raw G f, if home S i=o then diagonal r t p W i B else 0

theorem represented (r : Reserve S) (o : Site c) :
    root r t p W o = fun B => ∑ j : Slot, diagonal r t p W (key S o j) B := by
  funext B; exact collect_root o _

theorem root_flat (r : Reserve S) (o : Site c) : root r t p W o 0=0 := by simp [represented,flat]

theorem rooted_entries (hs : 0<σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (r s : Reserve S) (z : Site c) (hc : ∀ y, y≠z → r y=s y) (o : Site c) (l : List (raw G c)) (hl : l.length<n) :
    let d := width G S.patch S.kernel p n A σ
    let P := (marks G c d).pay l o
    let M := (Fintype.card Slot:ℝ)*(earnings G S.patch S.kernel p n A σ/2)
    let K (u : Reserve S) := jet V (root u t p W o) l 0
    P* |K r| ≤ M ∧ (native c).weight d o z*P* |K s-K r| ≤ M := by
  intro d P M K
  let H (r : Reserve S) (j : Slot) := diagonal r t p W (key S o j)
  have hk (r : Reserve S) : K r=∑ j : Slot, jet V (H r j) l 0 := by
    change jet V (root r t p W o) l 0=_
    rw [represented,jet_sum]
    intro j _
    exact smooth_of_le (spectral (t:=t) (p:=p) (n:=n) hs ha hW he r (key S o j)).1 hl.le
  have hM (j : Slot) := entries (t:=t) (p:=p) hs ha hW he r s z hc (key S o j) l hl
  have hp : 0 ≤ P := (Mark.pay_pos ..).le
  constructor
  · rw [hk]; apply uniform_sum hp; intro j; simpa only [H,home_key] using (hM j).1
  rw [hk,hk,←Finset.sum_sub_distrib]
  apply uniform_sum (mul_nonneg ((native c).weight_nn ..) hp)
  intro j; simpa only [H,home_key] using (hM j).2

def Scalar {j : ℕ} (o : Site c) (W : Site c→(Fin j→ raw G c)→Bool) (γ C : ℝ) (F : Site c→(Fin j→ raw G c)→ℝ) :=
  ∑ a,∑ l : Fin j→ raw G c, (if W a l then
    Real.exp (γ*(ConditionalPhysicalSpan.span o (ConditionalPhysicalSpan.sites a a (hearth∘l)):ℝ))* |F a l| else 0) ≤ C

theorem Scalar.moment {j : ℕ} {o : Site c} {W : Site c→(Fin j→ raw G c)→Bool} {γ C : ℝ}
    {F : Site c→(Fin j→ raw G c)→ℝ} (h : Scalar o W γ C F) (hγ : 0<γ) (k : ℕ) :
    (∑ a,∑ l : Fin j→ raw G c, if W a l then
      let s : ℝ := ConditionalPhysicalSpan.span o (ConditionalPhysicalSpan.sites a a (hearth∘l))
      (1+s)^k*Real.exp ((γ/2)*s)* |F a l| else 0) ≤ ConditionalPhysicalSpan.momentFee γ k*C := by
  apply le_trans _ (mul_le_mul_of_nonneg_left h (ConditionalPhysicalSpan.momentFee_nonneg hγ k))
  simp only [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun l _ => ?_
  by_cases hw : W a l=true
  · simp only [hw,ite_true,←mul_assoc]
    exact mul_le_mul_of_nonneg_right (ConditionalPhysicalSpan.absorb hγ (Nat.cast_nonneg _) k) (abs_nonneg _)
  simp [hw]

private theorem trace_diagonal {j : ℕ} {o : Site c} {W : Site c→(Fin j→ raw G c)→Bool}
    {γ C : ℝ} {F : Site c→(Fin j→ raw G c)→ℝ}
    (h : ConditionalPhysicalSpan.Rooted j id id hearth o (fun a _ l => W a l) γ C
      (fun a b l => if a=b then F a l else 0)) : Scalar o W γ C F := by
  apply le_trans _ h.limit
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hne; simp [Ne.symm hne]
  · simp


def price (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (n j : ℕ) (A σ : ℝ) :=
  let μ := together G P K p n A σ
  let M := (Fintype.card (Co P.L (PAC G 1)):ℝ)*(earnings G P K p n A σ/2)
  crowd j M (max (torusPay Unit μ) (torusPay (PAC G 1) μ))

/-- All field positions and the actual coarse output root are summed. A
changed physical tree site is retained for the second coefficient norm. -/
theorem positions (hs : 0<σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (j : ℕ) (hj : j<n) :
    let μ := together G S.patch S.kernel p n A σ/4
    let C := price G S.patch S.kernel p n j A σ
    let K (r : Reserve S) (a : Site c) (l : Fin j→ raw G c) := jet V (root r t p W a) (List.ofFn l) 0
    (∀ (r : Reserve S) (o : Site c) (v : Site c→(Fin j→ raw G c)→Bool),
      (∀ a l, v a l=true → o=a ∨ ∃ z, o=hearth (l z)) → Scalar o v μ C (K r)) ∧
    ∀ (r s : Reserve S) (o : Site c), (∀ z, z≠o → r z=s z) →
      Scalar o (fun _ _ => true) μ C (fun a l => K s a l-K r a l) := by
  intro μ C K
  let d := width G S.patch S.kernel p n A σ
  let γ := together G S.patch S.kernel p n A σ
  let V₀ := max (torusPay Unit γ) (torusPay (PAC G 1) γ)
  let M := (Fintype.card Slot:ℝ)*(earnings G S.patch S.kernel p n A σ/2)
  obtain ⟨hγ,hd,_,_,_⟩ := sum_schedule (G:=G) (S:=S) (p:=p) hj.le hs ha
  have hV : 0 ≤ V₀ := (torusPay_nn Unit _ hγ).trans (le_max_left ..)
  have hM : 0 ≤ M := mul_nonneg (Nat.cast_nonneg _) (div_nonneg (gauged G S.patch S.kernel p n hs ha).meter_abs (by norm_num))
  have hi : Function.Injective (fun a : Site c => (a,())) := fun a b h => congrArg Prod.fst h
  have hu : (native c).Volume id γ V₀ := ((volume c Unit γ hγ).comp hi).le (le_max_left ..)
  have hv : (native c).Volume (hearth (G:=G) (c:=c) (r:=1)) γ V₀ := (volume c (PAC G 1) γ hγ).le (le_max_right ..)
  have weight (a : Site c) (q : Fin j→ raw G c) : (marks G c d).pay (List.ofFn q) a =
      Real.exp (d*costs (native c) a a a (hearth∘q)) := by
    change (FreeResolvent.Mark.positions (native c) hearth d).pay (List.ofFn q) a = _
    simpa only [id_eq, Cost.weight_self, one_mul, mul_one] using
      anchor_weight (native c) (id : Site c→Site c) (hearth (G:=G) (c:=c) (r:=1)) a a q d (1:ℝ)
  have hlen (q : Fin j→ raw G c) : (List.ofFn q).length<n := by simpa using hj
  have hp : 0≤μ := div_nonneg hγ.le (by norm_num)
  constructor
  · intro r o v h
    apply trace_diagonal
    apply ConditionalPhysicalSpan.original hp
    apply ConditionalCovarianceLayers.nearest_neighbor hγ.le
    apply sums_no_mark hγ.le hM hd hV _ (fun a b l hv => (h a l hv).imp_right Or.inr) hu hu hv
    intro a b l
    by_cases h' : a=b
    · subst b
      change Real.exp (d * costs (native c) a a a (hearth ∘ l)) *
        |if a = a then K r a l else 0| ≤ M
      rw [←weight a l, if_pos rfl]
      exact (rooted_entries (t:=t) (p:=p) hs ha hW he r r o (fun _ _ => rfl) a _ (hlen l)).1
    simpa only [if_neg h',abs_zero,mul_zero] using hM
  intro r s o hc
  apply trace_diagonal
  apply ConditionalPhysicalSpan.original hp
  apply ConditionalCovarianceLayers.nearest_neighbor hγ.le
  apply sums_tagged hγ.le hM hd hV _ hu hu hv
  intro a b l
  by_cases h' : a=b
  · subst b
    change (native c).weight d a o * Real.exp (d * costs (native c) a a a (hearth ∘ l)) *
      |if a = a then K s a l - K r a l else 0| ≤ M
    rw [←weight a l, if_pos rfl]
    exact (rooted_entries (t:=t) (p:=p) hs ha hW he r s o hc a _ (hlen l)).2
  simpa only [if_neg h',abs_zero,mul_zero] using hM

end YM.Integration.ConditionalAffineIdealLog

/-! The original bond-end panels of the curved conditional mean. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ConditionalAffinePanelWindow
open Lattice Wilson RG Precision Tree Matrix FreeResolvent FreeResolvent.Affine
  FreeResolvent.Mark FreeResolvent.TestD FreeResolvent.Lever FreeResolvent.Stars
  PhysicalNext.Repeat.Greenbelt ConditionalTreeCovarianceJets ConditionalTreeCovarianceSums
  SelectedOrderedKernels.Sector Function Filter Set ConditionalCovarianceCutoff
  AnalyticBridge.GaussianFieldAlignment AnalyticBridge.RelativeLogdet
  Pressure Pressure.Tube Pressure.Stores Next.SectorChange Next.SectorChange.Rows Bid
  Push.SectorMeasure Push.SectorMeasure.Oriented Next.Fluctuations.Sector
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {t : S.Choices}
  {p : Clip} {W : PathData G} {σ A u : ℝ} {n : ℕ}

variable (G S) in
def survey (x : ℝ) (hx : 120 ≤ radiusB x) := view (endsAt (G:=G) S x) (ends_self x hx)

variable (G S) in
theorem near (x : ℝ) (hx : 120 ≤ radiusB x) :
    (survey G S x hx).Near (native c) (home S) (radiusB x / 60 : ℕ) := by
  intro i j hj
  by_contra! h
  have hdist : (separation (home S i) (home S j) : ℝ) ≤ (radiusB x / 60 : ℕ) := h.le
  have H := endsAt_bars (G:=G) (S:=S) x hx i j (by exact_mod_cast hdist)
  exact hj ⟨⟨j,H⟩,rfl⟩

private abbrev vacant (S : StepData c f) : Stores S := ⟨∅,∅,∅⟩

theorem same_rim (F : Forest S.ratio) (x : ℝ) :
    Shell.rim (address (G:=G) (vacant S) F x) = Shell.rim (freeTo G S F) := by
  let e := (Native.every F x).symm.prodCongr (Equiv.refl G.ColorIndex)
  ext i j
  exact e.sum_comp (fun z => insertion (freeTo G S F) i z * insertion (freeTo G S F) j z)

/-- The original independently true curved Gram fills to the original cut whole matrix, on the flat germ. -/
theorem physical_fill (F : Forest S.ratio) (x : ℝ) (T : Tube G S) (k : S.Choices)
    (h : S.patch.Branches S.kernel G) {Λ : ℝ} (hT : T.up.Bounds T.high σ A Λ) :
    ∀ᶠ B : Gaussian.Vec (Raw G c) in 𝓝 0,
      fill (address (vacant S) F x) (Rows.gram T x (represent (decode B)) k (shots S x) (vacant S) F) =
        whole S F k T.high T.up (shorter (till x)) B := by
  filter_upwards [affine_near (vacant S) F x T k h hT] with B hb
  rw [hb]
  change fill _ ((block S k T.high T.up (shorter (till x)) B).submatrix _ _) = _
  rw [show (block S k T.high T.up (shorter (till x)) B).submatrix (fun i => plant F (live (vacant S) F x i))
      (fun i => plant F (live (vacant S) F x i)) = (block S k T.high T.up (shorter (till x)) B).submatrix
      (address (vacant S) F x) (address (vacant S) F x) from rfl, fill_pad]
  simp only [whole,Function.comp_apply,Shell.pad,Shell.slice,Shell.off,same_rim]

/-- At the actual curved field the endpoint panel is the stored sector panel in the same vacuum chart.
The half-gap is bought from the canonical coarse precision soundness at zero. -/
theorem physical (F : Forest S.ratio) (x : ℝ) (hx : 120 ≤ radiusB x) (T : Tube G S) (k : S.Choices)
    (h : S.patch.Branches S.kernel G) (he : Bid.Larger (G:=G) S) (hs : 0<σ) (ha : 0 ≤ A)
    {Λ : ℝ} (hT : T.up.Bounds T.high σ A Λ) :
    ∀ᶠ B : Gaussian.Vec (Raw G c) in 𝓝 0,
      (survey G S x hx).inspect (whole S F k T.high T.up (shorter (till x)) B) 0 =
        fill (address (vacant S) F x) (Schur.per (panels (vacant S) F)
          (Rows.gram T x (represent (decode B)) k (shots S x) (vacant S) F)) := by
  let r := shorter (till x)
  let η := headGap G S.patch S.kernel T.high
  have hη : 0<η := headGap_pos ..
  have K := knows F k hs ha (path_sheet T hT) he T.high 0 r
  have hh := Differential.holds K.smooth.continuousAt K.gap (η/2) (by dsimp [η]; linarith)
    (native c) (theta S.ratio F)
  filter_upwards [hh,physical_fill F x T k h hT,affine_near (vacant S) F x T k h hT] with B hB hF hG
  let Q := Rows.gram T x (represent (decode B)) k (shots S x) (vacant S) F
  have hg : Gap Q (η/2) := by rw [show Q=_ from hG]; exact hB.submatrix _ (live (vacant S) F x).injective
  have hQ : Q.IsSymm := by
    rw [show Q=_ from hG]; exact ((block_symm T k r B).submatrix (plant F)).submatrix _
  change (view (endsAt S x (G:=G)) (ends_self x hx)).inspect _ 0 = _
  rw [←hF, per_view,
    Completed.per_fill' _ _ (ends_self x hx) Q hQ (half_pos hη) (AnalyticBridge.LocalGaussianLaws.gapped_iff.mpr hg)]
  congr 2; exact funext fun i => (panels_eq (vacant S) F x i).symm

private theorem sym_fill {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : κ ↪ ι) (Q : Gaussian.Table κ) :
    ColumnMode.symmetric.matrix (fill e Q) = fill e (ColumnMode.symmetric.matrix Q) := by
  exact Completed.symPart_fill e Q

/-- The literal symmetrized ordered window is the stored positive sector covariance
on its original active keys. In the ambient coordinates remove precisely their
permanent inactive identity. -/
theorem covariance (F : Forest S.ratio) (x : ℝ) (hx : 120 ≤ radiusB x) (T : Tube G S) (k : S.Choices)
    (h : S.patch.Branches S.kernel G) (he : Bid.Larger (G:=G) S) (hs : 0<σ) (ha : 0 ≤ A)
    {Λ : ℝ} (hT : T.up.Bounds T.high σ A Λ) :
    let e := address (G:=G) (vacant S) F x
    ∀ᶠ B : Gaussian.Vec (Raw G c) in 𝓝 0,
      ColumnMode.symmetric.matrix ((survey G S x hx).inspect (whole S F k T.high T.up (shorter (till x)) B) 0) -
        Shell.off (freeTo G S F) =
      insertion e * fog (vacant S) F T x (represent (decode B)) k * (insertion e).transpose := by
  intro e
  filter_upwards [physical F x hx T k h he hs ha hT] with B hB
  rw [hB,sym_fill,fill]
  change _ + Shell.off e - Shell.off (freeTo G S F) = _
  rw [show Shell.off e=Shell.off (freeTo G S F) from congrArg (fun D => 1-D) (same_rim F x),add_sub_cancel_right]
  rfl

private theorem fill_action {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : κ ↪ ι) (Q : Gaussian.Table κ) (b : Gaussian.Vec κ) :
    -(fill e Q).transpose *ᵥ (insertion e *ᵥ b) = insertion e *ᵥ (-Q.transpose *ᵥ b) := by
  have h : (fill e Q).transpose * insertion e = insertion e * Q.transpose := by
    unfold fill
    rw [transpose_add,transpose_mul,transpose_mul,transpose_transpose,Shell.undo,
      Matrix.add_mul,Shell.barred,add_zero,Matrix.mul_assoc,Matrix.mul_assoc,Shell.pin,Matrix.mul_one]
  rw [Matrix.neg_mulVec,Matrix.neg_mulVec,Matrix.mulVec_neg,Matrix.mulVec_mulVec,
    h,←Matrix.mulVec_mulVec]

/-- This is the original sector mean acting on the stored nonlinear load in the physical chart, for every shell input. -/
theorem mean (F : Forest S.ratio) (x : ℝ) (hx : 120 ≤ radiusB x) (T : Tube G S) (k : S.Choices)
    (h : S.patch.Branches S.kernel G) (he : Bid.Larger (G:=G) S) (hs : 0<σ) (ha : 0 ≤ A)
    {Λ : ℝ} (hT : T.up.Bounds T.high σ A Λ) (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen (vacant S) x F)) :
    ∀ᶠ B : Gaussian.Vec (Raw G c) in 𝓝 0,
      let e := address (G:=G) (vacant S) F x
      let V := represent (decode B)
      (-((survey G S x hx).inspect (whole S F k T.high T.up (shorter (till x)) B) 0).transpose) *ᵥ
        (insertion e *ᵥ Rows.blame T x V k (shots S x) (vacant S) F q d Y) =
          insertion e *ᵥ meanLog (vacant S) F T x V k q d Y := by
  filter_upwards [physical F x hx T k h he hs ha hT] with B hB
  dsimp only
  rw [hB]
  exact fill_action _ _ _

private theorem read_bound {ι E X τ : Type*} [Fintype ι] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {v : τ → E} {C : Mark τ X} {D : Cost X} {a : ι → X}
    {s M : ℝ} {k : ℕ} {Q : E → Matrix ι ι ℝ} {x : E}
    (mode : ColumnMode) (h : Bundle v C D a a Q x k s M) :
    Bundle v C D a a (mode.field Q) x k s M := by
  cases mode with
  | direct => exact h
  | adjoint => exact h.transpose
  | symmetric => exact polarize_cost h

def columns (mode : ColumnMode) (x : ℝ) (hx : 120 ≤ radiusB x) (L : ℕ)
    (r : Reserve S) (t : S.Choices) (p : Clip) (W : PathData G) (u : ℝ) :=
  mode.field (glimpse (survey G S x hx) (whole S (allot r) t p W (shorter L)) u -
    action (whole S (allot r) t p W all) u)

theorem adjoint_columns (θ : ℝ) (hθ : 120 ≤ radiusB θ) (L : ℕ) (r : Reserve S) (x : Vec G c 1) :
    columns .adjoint θ hθ L r t p W u x =
      ((survey G S θ hθ).inspect (whole S (allot r) t p W (shorter L) x) u).transpose -
      resolve (whole S (allot r) t p W all x) u := by
  have h : (resolve (whole S (allot r) t p W all x) u).IsSymm := by
    apply Matrix.IsSymm.inv
    unfold Matrix.IsSymm
    rw [Matrix.transpose_add,Matrix.transpose_smul,Matrix.transpose_one,(whole_symm (allot r) all x).eq]
  exact (Matrix.transpose_sub _ _).trans (congrArg (fun Q => _ - Q) h.eq)

theorem symmetric_columns {θ : ℝ} (hθ : 120 ≤ radiusB θ) (L : ℕ) (r : Reserve S) (B : Vec G c 1) :
    columns .symmetric θ hθ L r t p W u B =
      ColumnMode.symmetric.matrix ((survey G S θ hθ).inspect (whole S (allot r) t p W (shorter L) B) u) -
      resolve (whole S (allot r) t p W all B) u := by
  have hh : (resolve (whole S (allot r) t p W all B) u).IsSymm := by
    apply Matrix.IsSymm.inv
    unfold Matrix.IsSymm
    rw [Matrix.transpose_add,Matrix.transpose_smul,Matrix.transpose_one,(whole_symm (allot r) all B).eq]
  let X := (survey G S θ hθ).inspect (whole S (allot r) t p W (shorter L) B) u
  let Y := resolve (whole S (allot r) t p W all B) u
  change (1/2:ℝ) • ((X - Y) + (X - Y).transpose) = (1/2:ℝ) • (X + X.transpose) - Y
  rw [Matrix.transpose_sub, hh.eq]
  module

private theorem family (mode : ColumnMode) (hs : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (hu : 0 ≤ u) (x : ℝ) (hx : 120 ≤ radiusB x) (L : ℕ) {T U : Forest S.ratio} {v : Site c} (hTU : changed S T U v)
    {θ : ℝ} (hθ : θ ∈ Icc (0:ℝ) 1) :
    let d := width G S.patch S.kernel p n A σ
    let Z := survey G S x hx
    let F := crest S t (W:=W) (T:=T) (U:=U) (p:=p)
    Bundle (guides (ray G c)) (park (native c) hearth d v) (native c) (home S) (home S)
      (mode.field (glimpse Z (F (shorter L)) u - action (F all) u)) (0,θ) n d
      (windowPrice G S.patch S.kernel p n A σ u (radiusB x / 60 : ℕ) + diminish G S.patch S.kernel p n L A σ u) := by
  intro d Z F
  have P := gauged G S.patch S.kernel p n hs ha
  have hfull := mast S t (p:=p) (n:=n) hs ha hW he hTU all hθ
  have hcut := mast S t (p:=p) (n:=n) hs ha hW he hTU (shorter L) hθ
  have V := home_volume (G:=G) S 1 _ P.pos
  have hm := position_move (native c) (fun i : Option (raw G c) => i.elim v hearth) P.pos.le
  have hw := hcut.discrepancy P hu hm V (near G S x hx)
  have hr := roll S t (p:=p) (n:=n) hs ha hW he hTU L hθ
  let C := phasePrice G S.patch S.kernel n A σ
  have hC : 0 ≤ C := phase_nn G S.patch S.kernel hs ha
  have ht : 0 ≤ 3*(Real.exp (-(σ/4)*L)*(2*tagPrice 1 n C C)) :=
    mul_nonneg (by norm_num) (mul_nonneg (Real.exp_pos _).le (mul_nonneg (by norm_num) (tag_nn hC hC)))
  have hd : (2*(n+1:ℕ)+1)*d ≤ tier σ n / 2 := by
    refine le_trans ?_ (P.roomEnough.trans P.roomTop)
    apply mul_le_mul_of_nonneg_right _ P.pos.le
    push_cast
    linarith [show (0:ℝ) ≤ n by positivity]
  have hc := hfull.change hcut P hu hm V ht (hr.mono hd le_rfl)
  apply read_bound mode
  apply (hw.one_add hc).glue
  exact Eventually.of_forall fun z => by simp only [Pi.sub_apply]; abel

theorem regular (hs : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (hu : 0 ≤ u) (x : ℝ) (hx : 120 ≤ radiusB x) (L : ℕ) (r : Reserve S) (mode : ColumnMode := .symmetric) :
    let d := width G S.patch S.kernel p n A σ
    Bundle (ray G c) (marks G c d) (native c) (home S) (home S) (columns mode x hx L r t p W u) 0 n d
      (windowPrice G S.patch S.kernel p n A σ u (radiusB x / 60 : ℕ) + diminish G S.patch S.kernel p n L A σ u) := by
  intro d
  have hf := family mode (t:=t) (p:=p) (n:=n) hs ha hW he hu x hx L
    (change_draw r r (0:Site c) (fun _ _ => rfl)) (Set.left_mem_Icc.mpr zero_le_one)
  let Z := survey G S x hx
  refine (restricted 0 hf).glue (Eventually.of_forall fun x => ?_)
  exact congrArg₂ (fun Q R => mode.matrix (Z.inspect Q u - resolve R u))
    (now (allot r) (allot r) t p (shorter L) x) (now (allot r) (allot r) t p all x)

theorem tagged (hs : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (hu : 0 ≤ u) (x : ℝ) (hx : 120 ≤ radiusB x) (L : ℕ) (r s : Reserve S) (v : Site c) (h : ∀ w, w ≠ v → r w = s w)
    (l : List (raw G c)) (hl : l.length < n) (mode : ColumnMode := .symmetric) :
    let d := width G S.patch S.kernel p n A σ
    Here (ray G c) (native c) (home S) hearth d d v l
      (windowPrice G S.patch S.kernel p n A σ u (radiusB x / 60 : ℕ) + diminish G S.patch S.kernel p n L A σ u)
      (columns mode x hx L r t p W u) (columns mode x hx L s t p W u) := by
  intro d
  let Z := survey G S x hx
  let F := crest S t (W:=W) (T:=allot r) (U:=allot s) (p:=p)
  refine paid (G:=mode.field (glimpse Z (F (shorter L)) u - TestD.action (F all) u)) ?_ ?_ hl ?_
  · intro x
    exact congrArg₂ (fun Q R => mode.matrix (Z.inspect Q u - resolve R u))
      (now (allot r) (allot s) t p (shorter L) x) (now (allot r) (allot s) t p all x)
  · intro x
    exact congrArg₂ (fun Q R => mode.matrix (Z.inspect Q u - resolve R u))
      (thenAt (allot r) (allot s) t p (shorter L) x) (thenAt (allot r) (allot s) t p all x)
  exact fun θ hθ => family mode hs ha hW he hu x hx L (change_draw r s v h) hθ

theorem position_sum (hs : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S)
    (hu : 0 ≤ u) (x : ℝ) (hx : 120 ≤ radiusB x) (L j : ℕ) (hj : j < n) (mode : ColumnMode := .symmetric) :
    let γ := together G S.patch S.kernel p n A σ
    let V := totalFoot G S.patch S.kernel p n A σ
    let M := windowPrice G S.patch S.kernel p n A σ u (radiusB x / 60 : ℕ) + diminish G S.patch S.kernel p n L A σ u
    let K (r : Reserve S) (i z : raw G f) (k : Fin j → raw G c) :=
      iteratedFDeriv ℝ j (columns mode x hx L r t p W u) 0 (ray G c ∘ k) i z
    (∀ (r : Reserve S) (v : Site c) (g : raw G f → raw G f → (Fin j → raw G c) → Bool),
      (∀ i z k, g i z k = true → v = home S i ∨ v = home S z ∨ ∃ m, v = hearth (k m)) →
      NearStar j (native c) (home S) (home S) hearth v g γ (crowd j M V) (K r)) ∧
    ∀ (r s : Reserve S) (v : Site c), (∀ w, w ≠ v → r w = s w) →
      NearStar j (native c) (home S) (home S) hearth v (fun _ _ _ => true) γ (crowd j M V)
        (fun i z k => K s i z k - K r i z k) := by
  apply summed hj hs ha (add_nonneg (window_price_nonneg hs ha hu) (cut_nonneg hs ha hu L))
      (fun r => columns mode x hx L r t p W u)
  · exact fun r _ => regular hs ha hW he hu x hx L r mode
  exact fun r s v h l hl => tagged hs ha hW he hu x hx L r s v h l hl mode

theorem funded (hs : 0 < σ) (ha : 0 ≤ A) (B : ℕ) (hB : 100000 ≤ B) :
    let d := width G S.patch S.kernel p n A σ
    let rate := min (((n+1:ℕ):ℝ)*d/120) (σ/800000)
    let C := windowPrice G S.patch S.kernel p n A σ 0 0 + diminish G S.patch S.kernel p n 0 A σ 0
    0 < rate ∧ windowPrice G S.patch S.kernel p n A σ u (B/60:ℕ) +
      diminish G S.patch S.kernel p n (B/100000) A σ u ≤ C*Real.exp (-rate*B)*drain u^2 := by
  intro d μ C
  have hd : 0 < d := (gauged G S.patch S.kernel p n hs ha).pos
  have hN : (B:ℝ) ≤ 200000*(((B/100000:ℕ):ℝ)) := by
    exact_mod_cast (show B ≤ 200000*(B/100000) from by omega)
  have hr : 0<μ := lt_min (by positivity) (by positivity)
  have hW : (B:ℝ) ≤ 120*(((B/60:ℕ):ℝ)) := by
    exact_mod_cast (show B ≤ 120*(B/60) from by omega)
  have h₁ : Real.exp (-(n+1:ℕ)*d*(B/60:ℕ)) ≤ Real.exp (-μ*B) := by
    apply Real.exp_monotone
    have hμ : μ*120 ≤ ((n+1:ℕ):ℝ)*d := (le_div_iff₀ (by positivity)).1 (min_le_left ..)
    nlinarith only [mul_le_mul_of_nonneg_left hW hr.le,
      mul_le_mul_of_nonneg_right hμ (show 0≤((B/60:ℕ):ℝ) by positivity)]
  have h₂ : Real.exp (-(σ/4)*(B/100000:ℕ)) ≤ Real.exp (-μ*B) := by
    apply Real.exp_monotone
    have hμ : μ ≤ σ/800000 := min_le_right ..
    nlinarith only [mul_le_mul_of_nonneg_right hμ (Nat.cast_nonneg B),mul_le_mul_of_nonneg_left hN hs.le]
  have wh := window_price_nonneg (G:=G) (S:=S) (p:=p) (n:=n) (R:=0) hs ha (le_refl 0)
  have dh := cut_nonneg (G:=G) (S:=S) (p:=p) (n:=n) hs ha (le_refl 0) 0
  refine ⟨hr,?_⟩
  rw [window_price,cut_price,←add_mul]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact (add_le_add (mul_le_mul_of_nonneg_left h₁ wh) (mul_le_mul_of_nonneg_left h₂ dh)).trans_eq
    (add_mul _ _ _).symm

end YM.Integration.ConditionalAffinePanelWindow

/-! A changed physical inverse line acting on a genuine independent-field jet column. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ConditionalAffineRootContraction
open Function Filter Set Matrix FreeResolvent FreeResolvent.TestD FreeResolvent.Mark FreeResolvent.Lever
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {E τ X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
variable {v : τ→E} {D : Cost X} {p : τ→X} {a : ι→X} {z : X} {δ d γ M C V : ℝ}
variable {A B : E→Matrix ι ι ℝ} {f : E→Matrix ι Unit ℝ} {n : ℕ}

theorem pay_le (h : δ ≤ d) (l : List τ) (x : X) :
    (positions D p δ).pay l x ≤ (positions D p d).pay l x := by
  induction l with
  | nil => exact le_rfl
  | cons t l ih =>
    exact mul_le_mul (D.weight_mono h x (p t)) ih ((positions D p δ).pay_pos l x).le (D.weight_nn ..)

/-- A split of a field derivative transfers every source mark and keeps one radial decay for the summation key. -/
theorem component (l : List τ) (m : Masks l) (i j : ι) (hδ : 0≤δ) (hd : δ ≤ d)
    (hγ : (hi l m).length*δ+δ≤γ) (hM : 0 ≤ M)
    (hA : Here v D a p d γ z (lo l m) M A B)
    (hF : (positions D p δ).pay (hi l m) (a j)* |(jet v f (hi l m) 0) j ()| ≤ C) :
    D.weight δ (a i) z*(positions D p δ).pay l (a i)*
      |(jet v B (lo l m) 0-jet v A (lo l m) 0) i j*(jet v f (hi l m) 0) j ()| ≤
      (M*C)*D.weight (-δ) (a i) (a j) := by
  let u := (jet v B (lo l m) 0-jet v A (lo l m) 0) i j
  let w := (jet v f (hi l m) 0) j ()
  let H := positions D p δ
  let J := positions D p d
  have hm := ((position_move D p hδ).transfer (zero_le_one) (hi l m) (a i) (a j))
  simp only [one_pow,one_mul] at hm
  have ha := (hA.test i j).1
  have h : D.weight δ (a i) z*H.pay l (a i)* |u*w| *D.weight δ (a i) (a j) ≤ M*C := by
    rw [H.pay_masks l m,abs_mul]
    calc
      _ = (D.weight δ (a i) z*H.pay (lo l m) (a i))*
          (H.pay (hi l m) (a i)*D.weight δ (a i) (a j))*(|u| * |w|) := by ring
      _ ≤ (D.weight d (a i) z*J.pay (lo l m) (a i))*
          ((D.weight ((hi l m).length*δ) (a i) (a j)*H.pay (hi l m) (a j))*D.weight δ (a i) (a j))*
          (|u| * |w|) := by
        have h1 := D.weight_mono hd (a i) z
        have h2 := pay_le (D:=D) (p:=p) hd (lo l m) (a i)
        have hx := H.pay_pos (lo l m) (a i)
        have hy := H.pay_pos (hi l m) (a i)
        have hz := J.pay_pos (lo l m) (a i)
        have hw := D.weight_pos δ (a i) (a j)
        have hwd := D.weight_pos d (a i) z
        gcongr
      _ = (D.weight d (a i) z*J.pay (lo l m) (a i)*
          (D.weight ((hi l m).length*δ+δ) (a i) (a j)* |u|))*(H.pay (hi l m) (a j)* |w|) := by
        rw [D.weight_add]; ring
      _ ≤ (D.weight d (a i) z*J.pay (lo l m) (a i)*
          (D.weight γ (a i) (a j)* |u|))*(H.pay (hi l m) (a j)* |w|) := by
        have hw := H.pay_pos (hi l m) (a j)
        have hz := J.pay_pos (lo l m) (a i)
        have ht := D.weight_pos d (a i) z
        gcongr
        exact D.weight_mono hγ _ _
      _ ≤ M*C := mul_le_mul ha hF (mul_nonneg (H.pay_pos ..).le (abs_nonneg _)) hM
  rw [D.weight_neg]
  exact (le_div_iff₀ (D.weight_pos δ (a i) (a j))).2 h |>.trans_eq (div_eq_mul_inv ..)

/-- Take the actual spectral-column product at a retained output, summing every
intermediate physical label (with its original multiplicity). -/
theorem apply_column (hδ : 0≤δ) (hd : δ ≤ d) (hγ : (n+1:ℕ)*δ≤γ) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hV : D.Volume a δ V) (hA : ContDiffAt ℝ n A 0) (hB : ContDiffAt ℝ n B 0)
    (hf : ContDiffAt ℝ n f 0)
    (hH : ∀ l : List τ, l.length ≤ n → Here v D a p d γ z l M A B)
    (hS : ∀ (l : List τ), l.length ≤ n → ∀ j, (positions D p δ).pay l (a j)* |jet v f l 0 j ()| ≤ C)
    (l : List τ) (hl : l.length ≤ n) (i : ι) :
    D.weight δ (a i) z*(positions D p δ).pay l (a i)*
      |jet v (fun b => (B b-A b)*f b) l 0 i ()| ≤ 2^l.length*(M*C*V) := by
  let t := D.weight δ (a i) z*(positions D p δ).pay l (a i)
  have ht : 0 ≤ t := mul_nonneg (D.weight_nn ..) ((positions D p δ).pay_pos ..).le
  have hb := smooth_of_le (hB.sub hA) hl
  rw [jet_mul v l hb (smooth_of_le hf hl)]
  simp only [Matrix.sum_apply,Matrix.mul_apply]
  change t* |∑ m : Masks l, ∑ j, _|≤_
  calc
    _ ≤ t*∑ m : Masks l, ∑ j, |jet v (fun b => B b-A b) (lo l m) 0 i j*jet v f (hi l m) 0 j ()| := by
      apply mul_le_mul_of_nonneg_left _ ht
      exact (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun m _ => Finset.abs_sum_le_sum_abs ..)
    _ = ∑ m : Masks l, ∑ j, t* |jet v (fun b => B b-A b) (lo l m) 0 i j*jet v f (hi l m) 0 j ()| := by
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ _m : Masks l, M*C*V := by
      apply Finset.sum_le_sum; intro m _
      have hu := (len_high l m).trans hl
      have hv := (len_low l m).trans hl
      have hpay : (hi l m).length*δ+δ≤γ := by
        have hnat : ((hi l m).length:ℝ) ≤ n := by exact_mod_cast hu
        have hh := mul_le_mul_of_nonneg_right hnat hδ
        push_cast at hγ
        linarith
      calc
        _ ≤ ∑ j, (M*C)*D.weight (-δ) (a i) (a j) := by
          apply Finset.sum_le_sum; intro j _
          rw [jet_sub v (lo l m) (smooth_of_le hB hv) (smooth_of_le hA hv)]
          exact component l m i j hδ hd hpay hM (hH _ hv) (hS _ hu j)
        _ ≤ M*C*V := by rw [←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hV.bound _) (mul_nonneg hM hC)
    _ = _ := by simp [TestD.card,nsmul_eq_mul]

section physical
open Lattice Wilson RG Precision Tree Bloch FreeResolvent.Mid FreeResolvent.Affine PhysicalNext.Repeat.Greenbelt
open ConditionalTreeCovarianceJets ConditionalTreeCovarianceSums ConditionalCovarianceCutoff
open Pressure Pressure.Tube Pressure.Stores
variable {G : Gauge} {c fside : Side} {S : StepData c fside} {A₀ σ : ℝ} {p₀ : Clip} {W : PathData G}
variable {t : S.Choices}

/-- The active two-endpoint ordered mean line, with one physical tree change,
acting on an independently marked physical load on this same raw alphabet. -/
theorem panel (hs : 0<σ) (ha : 0 ≤ A₀) (hW : Sheet W σ A₀) (he : Bid.Larger (G:=G) S)
    (x : ℝ) (hx : 120 ≤ radiusB x) (r s : Reserve S) (z : Site c) (h : ∀ w, w≠z → r w=s w)
    (n : ℕ) (δ C : ℝ) (hδ : 0<δ) (hC : 0 ≤ C)
    (hroom : ((n+1:ℕ):ℝ)*δ ≤ width G S.patch S.kernel p₀ (n+1) A₀ σ)
    (f : Vec G c 1→Matrix (raw G fside) Unit ℝ) (hf : ContDiffAt ℝ n f 0)
    (hS : ∀ (l : List (raw G c)), l.length ≤ n → ∀ j,
      (marks G c δ).pay l (home S j)* |jet (ray G c) f l 0 j ()| ≤ C) :
    let E u := ConditionalAffinePanelWindow.columns .adjoint x hx (till x) u t p₀ W 0
    let M := windowPrice G S.patch S.kernel p₀ (n+1) A₀ σ 0 (radiusB x / 60 : ℕ) +
      diminish G S.patch S.kernel p₀ (n+1) (till x) A₀ σ 0
    ∀ (l : List (raw G c)), l.length ≤ n → ∀ i,
      (native c).weight δ (home S i) z*(marks G c δ).pay l (home S i)*
        |jet (ray G c) (fun B => (E s B-E r B)*f B) l 0 i ()| ≤
          2^l.length*(M*C*torusPay (Co S.patch.L (PAC G 1)) δ) := by
  intro E M l hl i
  have hd : δ ≤ width G S.patch S.kernel p₀ (n+1) A₀ σ :=
    (by have hu : (1:ℝ)≤(n+1:ℕ) := by exact_mod_cast (show 1 ≤ n+1 by omega)
        nlinarith only [mul_le_mul_of_nonneg_right hu hδ.le,hroom])
  have hM : 0 ≤ M := add_nonneg (window_price_nonneg (G:=G) (S:=S) hs ha (le_refl 0))
    (cut_nonneg (G:=G) (S:=S) hs ha (le_refl 0) _)
  have smooth (u : Reserve S) : ContDiffAt ℝ n (E u) 0 :=
    smooth_of_le (ConditionalAffinePanelWindow.regular (S:=S) (t:=t) (p:=p₀) (W:=W) (n:=n+1)
      hs ha hW he (le_refl 0) x hx (till x) u .adjoint).smooth (Nat.le_succ n)
  exact apply_column hδ.le hd hroom hM hC (home_volume (G:=G) S 1 _ hδ) (smooth r) (smooth s) hf
    (fun m hm => ConditionalAffinePanelWindow.tagged (S:=S) (t:=t) (p:=p₀) (W:=W) (n:=n+1) hs ha hW he (le_refl 0)
      x hx (till x) r s z h m (Nat.lt_succ_of_le hm) .adjoint) hS l hl i

end physical
end YM.Integration.ConditionalAffineRootContraction
