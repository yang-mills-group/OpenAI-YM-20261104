import YM.RG05Readout.Petals.Trail
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Petals
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "L"=> C.path.levels
local notation "χ"=> C.path.levels.clock.J
local notation "λ₀"=> C.S.toDepth
local notation "Α"=> C.S.a
local notation "R0"=> C.path.rep N p
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

local notation "L!"=> Lattice.wrap
variable {f: Extraction.Order}
/-! Cost of FD replacement on true normalized Wilson laws through regulator.
Use at arbitrarily high finite order per request to absorb also mixed errors
against any order of growing top directions. Convergence estimates in BOOK
extraction; no multiplying by outer volume without another reserve. -/
open Pulse Nuclear
variable {V:Type}[DecidableEq V][Fintype V]
local notation "Z"=> C.side N p
local notation "A"=> C.S.a
local notation "X!"=> A N
local notation "W"=> Wave V
local notation "x!"=> lattice C V N p
variable (s:V→ℕ) (M:(i:V)→Leafage C (s i))
local notation "U"=> ((i:V)→ Mark C (s i))
local notation "q!"=> k
local notation "v₀"=> fun i:V=> M i (N,p)
noncomputable def pens (s:V→ℕ)(p:∀ i,Mark C (s i))(k:ℕ): ℝ:= ∑ j:Forms k V, ‖∏ i:V, weights k (p i).1 (j i)‖ * ‖(fun i:V=>away (backward (j i)):Cloud V)‖^(k+1)
lemma remainder (hp:∑ i:V,s i ≤ k)(p':U)(t:x!) (g:W) (B':ℝ) (_hB:0≤B')(hz:∀ x, ‖iteratedFDeriv ℝ (k+1) g.val x‖ ≤ B'):
    ‖within s p' k (enters t g)-(perform s (fun i=>(p' i).1) (enters t g)).val 0‖ ≤ (A N)^(k+1)*pens s p' k * B':=by
     let Lg:=fun i=>(p' i).1; let f':=enters t g; let G':= package k 0 f'; let E':= B'*(A N)^(k+1); have he:∀ v:Cloud V, ‖iteratedFDeriv ℝ (k+1) f'.val v‖≤ E':=by
        intro v; unfold f' enters; rw [Nuclear.shoots,norm_smul,Real.norm_of_nonneg (pow_nonneg (C.S.a_pos _).le _),mul_comm]; exact mul_le_mul_of_nonneg_right (hz _) (pow_nonneg (C.S.a_pos _).le _)
     have hu(v:Cloud V): ‖f'.val v-G'.val v‖≤ E'* ‖v‖^(k+1):=by
        have h':0≤ E':=(norm_nonneg _).trans (he v); have hv:=sphere 0 f' ‖v‖ E' (norm_nonneg _) h' (fun x _=>he x) 0 (Nat.zero_le _) v (by rw [sub_zero]);
        rw [norm_sub_rev]; rw [← show iteratedFDeriv ℝ 0 (G'.val-f'.val) v= _ from iteratedFDeriv_sub_apply (lit G' _|>.contDiffAt) (lit f' _|>.contDiffAt),norm_iteratedFDeriv_zero, Pi.sub_apply] at hv; exact hv
     have hV:(perform s Lg f').val 0=(perform s Lg G').val 0:= performance s Lg (pol_cost _ _ ((pegs_cost s Lg).trans hp))
     rw [show (perform s Lg (enters t g)).val 0=(perform s Lg G').val 0 from hV, all_ports s Lg G' (pol_above (0:Cloud V) f' (show k < k+1 from k.lt_succ_self)),Petals.within,← Finset.sum_sub_distrib]; unfold pens; rw [Finset.mul_sum,Finset.sum_mul]; refine (norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=> ?_)); unfold Lg; rw [←mul_sub,norm_mul]; exact (mul_le_mul_of_nonneg_left (hu _) (norm_nonneg _)).trans_eq (by unfold E'; ring)

lemma amount (F:lattice C V N p→ℂ)(B':ℝ)(h:∀ t,‖F t‖≤B') : ‖(∏ _i:V,(X!:ℂ)^4)*∑ i,F i‖≤ (Extraction.length C.S p)^(4*Fintype.card V)*B':=by
    -- from D03
    let v:=4*Fintype.card V; have ht:Fintype.card (lattice C V N p)= (Z|>.val)^v:=by
         unfold lattice; erw [Fintype.card_fun,site_card,←pow_mul] -- orientation
    have hm:=calc ‖∑ i,F i‖ ≤ ∑ _i:lattice C V N p, B' := (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=> h i)
                  _ = ((Z|>.val:ℝ))^v*B':= by simp only [Finset.sum_const,Finset.card_univ,ht,nsmul_eq_mul,Nat.cast_pow]
    simp_rw [Finset.prod_const,Finset.card_univ, ←pow_mul, norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos _).le]; exact (mul_le_mul_of_nonneg_left hm (pow_nonneg (C.S.a_pos _).le _)).trans_eq (by rw [←mul_assoc,← mul_pow,C.S.span_side])

local notation "H"=> fun i:V=> code m k (M i)
local notation "Z₀"=> hammer (m:=m) s M
noncomputable def ribands (C:Family G)(s:V→ℕ)(k:ℕ)(c:V→ℝ):ℝ:= ∑ i:((i:V)→ Address.Mark C (s i)), pens s i k * ∏ v:V,c v
local notation "P!"=> (∑ i:V,s i)
lemma finite_bound (g:W)(v:Config G Z)(hp:∑ i:V,s i≤ k)(B' e₁:ℝ) (hB:0≤B') (hZ:∀ x, ‖iteratedFDeriv ℝ (k+1) g.val x‖ ≤ B')
    (c: V→ℝ)(hP:∀ (p':U)(j:V)(u₁:Site Z), ‖hammer (m:=m) s M p' j u₁ v‖≤ c j *((C.S.a N)^(s j))⁻¹)
    (he:∀ x∈Function.support g.val,‖x‖≤e₁)(hr:e₁<C.S.radius p)(hx:∀ j:Slots k,e₁+‖(C.S.a N) • away (backward j)‖ < C.S.radius p):
    ‖sheet g C H N p v-Pulse.multi C m N p s v₀ g v‖ ≤ (Extraction.length C.S p)^(4*Fintype.card V)*((C.S.a N)^(k+1-P!)*ribands C s k c*B'):=by
     rw [painting g _ _ v he hr hx,painted,← mul_sub,← Finset.sum_sub_distrib]; apply amount; intro t; rw [← Finset.sum_sub_distrib,ribands,Finset.mul_sum,Finset.sum_mul]; apply (norm_sum_le ..).trans; apply Finset.sum_le_sum; intro i _
     let j :=fun a:V=>(i a).1; let K:= pens s i k; have h₀:0 ≤ K:=Finset.sum_nonneg (fun i _=>mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)); have ha:= C.S.a_pos N
     rw [←sub_mul,norm_mul, norm_prod]; apply (mul_le_mul (remainder s hp i _ g B' hB hZ) (Finset.prod_le_prod (fun x _=> norm_nonneg _) (fun x _=>hP i x (t x))) (Finset.prod_nonneg fun i _=>norm_nonneg _) (show 0 ≤ (C.S.a N)^(k+1)*K * B' from by positivity)).trans_eq; rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib,Finset.prod_pow_eq_pow_sum]; rw [show (A N)^(k+1)= (A N)^(k+1-P!) * (A N)^P! from by rw [← pow_add, Nat.sub_add_cancel (hp.trans k.le_succ)]]; field_simp
-- uniform charges.Every level.H can use any larger order.Lean
lemma stays {t:ℕ} {P:Trial C} (hp: RawProtected C f P t): ∃ c:Cutoffs→ℝ,(∀ u,0 ≤ c u)∧ Slow C f c∧ ∀ᶠ u in f.fuse, ∀ i:Site (C.side u.1 u.2),∀ x:Config G _,‖P u.1 u.2 i x‖ ≤ c u*((C.S.a u.1)^t)⁻¹:=by
   obtain ⟨T,_,w,c,_,hC,hs⟩:=hp; refine ⟨fun i=>‖c i‖,fun i=> norm_nonneg _,hC.norm,(Order.fused f (fun i=> ∀ o, clothed (C.path.levels.budget i.1) (regional T o) o (unpriced C P t i.1 i.2 o) (w i) (c i))|>.mpr hs).mono fun i hi j h=> ?_⟩
   have he:= (hi j).2.2.2 h; unfold unpriced Push.RelayDifference.weight at he; simp only [Pi.smul_apply,norm_smul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos _).le] at he; rw [mul_comm] at he; rw [← div_eq_mul_inv]; exact (le_div_iff₀ (pow_pos (C.S.a_pos _) _)).mpr (he.trans (Real.le_norm_self _))
include h
variable (hG:G.Simple) (hM:∀ i:V,Slow C f (M i))
omit [Fintype V] [DecidableEq V] in
include hM hG in
lemma tools (k:V): ∃ b:Cutoffs→ℝ,(∀ u,0 ≤ b u)∧ Slow C f b∧ ∀ᶠ t in f.fuse,∀ (j:Mark C (s k))(i:Site (C.side t.1 t.2))(V'),‖pitch (M k) j m t.1 t.2 i V'‖ ≤ b t*((C.S.a t.1)^(s k))⁻¹:=by
     let A' : Slow C f (fun i:Cutoffs=> ((C.S.a i.1:ℂ)^(s k-s k))⁻¹ • M k i):=by simp [hM k];
     choose c hc hC hs using fun i:Mark C (s k)=> stays (horn (m:=m) h (M k) i hG (le_refl _) A'|>.header)
     refine ⟨_,fun u=>Finset.sum_nonneg (s:=Finset.univ) (f:=fun j=>c j u) (fun j _=> hc j u), Slow.sum _ _ (fun i _=> hC i),?_⟩
     filter_upwards [eventually_all.mpr hs] with t ht j u g
     exact (ht j u g).trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _=>hc i t) (Finset.mem_univ _)) (inv_pos.mpr (pow_pos (C.S.a_pos _) _)).le)
-- polynomial receipt multiplication
omit h
omit [Fintype V] in
lemma productC {w:V→ Cutoffs → ℝ} (hw:∀ i,Slow C f (w i))(s:Finset V): Slow C f fun u=> ∏ i∈s,w i u:=by
    induction s using Finset.induction_on with | empty=>simpa only [Finset.prod_empty] using Slow.const (C:=C) (f:=f) (1:ℝ) | insert i s hi ih=> simp_rw [Finset.prod_insert hi]; exact (hw _).mul ih
include h hG hM
lemma all_envelopes (t:ℕ)(hp:P! ≤ k)(hv:k+1-P!≥t) (B' e₁:ℝ) (hB:0≤ B'): ∃ c:Cutoffs→ℝ,(∀ i,0≤ c i)∧ Slow C f c ∧ ∀ᶠ i in f.fuse,∀ (u:Wave V), (∀ x, ‖iteratedFDeriv ℝ (k+1) u.val x‖ ≤ B') → (∀ x∈Function.support u.val, ‖x‖ ≤ e₁) → ∀ v:Config G (C.side i.1 i.2),
    ‖sheet u C H i.1 i.2 v-Pulse.multi C m i.1 i.2 s (fun j=> M j i) u v‖≤(C.S.a i.1)^t*c i :=by
     choose c hc hC hs using tools (m:=m) h s M hG hM
     let x'(i):= ribands C s k (fun j=>c j i)*B'
     have hA(i): 0 ≤ x' i:= mul_nonneg (Finset.sum_nonneg fun p _=>mul_nonneg (Finset.sum_nonneg fun x _=>mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)) (Finset.prod_nonneg fun j _=>hc j i)) hB
     have hb:Slow C f x':= by unfold x' ribands; exact (Slow.sum _ _ fun j _=> (Slow.const (pens s j k)).mul (productC hC Finset.univ)).mul (Slow.const _)
     let v(u:Cutoffs):=(Extraction.length C.S u.2)^(4*Fintype.card V)
     have hh:Slow C f v:=by intro ε h'; rw [Order.fused,Order.late]; refine Eventually.of_forall fun t=> ?_; unfold v; exact (show Tendsto (fun N=> Real.exp (ε*C.S.scale (f.mesh N))) atTop atTop from Real.tendsto_exp_atTop.comp ((C.S.divergent.comp f.mesh.cofinal).const_mul_atTop h')).eventually_ge_atTop ‖v (0,f.per t)‖
     refine ⟨_,fun i=> mul_nonneg (show 0≤ v i by unfold v Extraction.length; positivity) (hA i),hh.mul hb,?_⟩
     have h₀:∀ᶠ i in f.fuse,e₁+1<C.S.radius i.2:= (Order.fused f _).mpr ((f.per.cofinal.eventually (C.S.radius_diverges.eventually_gt_atTop (e₁+1))).mono (fun _ hi=> Eventually.of_forall fun _=> hi))
     have hx(j: Slots k): ∀ᶠ i in f.fuse, ‖(C.S.a i.1) • away (backward j)‖ ≤ 1:=by
         have hz:Tendsto (fun i: Cutoffs=> (C.S.a i.1) • away (backward j)) f.fuse (𝓝 0):=by simpa only [Function.comp_def, zero_smul] using (C.S.shrinks.comp (cutoff_grows f)).smul_const (away (backward j))
         exact hz.norm.eventually (ge_mem_nhds (by simp only [norm_zero,zero_lt_one]))
     filter_upwards [eventually_all.mpr hs,h₀,eventually_all.mpr hx] with i hl hp' hX u hq hP V'
     have hr:= finite_bound s M u V' hp B' e₁ hB hq (fun j=> c j i) (fun p j z=>hl j (p j) z V') hP (lt_trans (lt_add_one _) hp') (fun j=>lt_of_le_of_lt (add_le_add_right (hX j) _) hp');
     let a:= C.S.a i.1
     refine hr.trans (le_trans ?_ (le_of_eq (b:=_) (show v i*(a^t*x' i)=a^t*_ from mul_left_comm ..)))
     dsimp only [x']; rw [mul_assoc (a^ _)]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (C.S.a_pos _).le (Harvest.radius_paid C i.1 i.2|>.1) hv) (hA i)) (show 0 ≤ v i by unfold v Extraction.length; positivity)
end YM.RG05Readout.Petals
