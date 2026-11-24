import YM.GapsContact.Earn.Cliff

/-! # True short-price estimates at mesoscopic log clocks

Outputs cost before computing actual projected moments at this width and
all permissible layouts. Must combine with Seams' True Plot and price
relative comparisons to compare the non-running prescription against
these true yields separately. Adapted OPE Log Fees construction (uses different
width requirements and currency), here using Terminal coastal costs proved under Shipper.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Seams
open Function Set Filter Lattice RG Wilson MergeProof Accent Ribbons Source Overlay Bid
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage ManyCopies Next.Rank
open OPE OPE.Log Spec Trace Trace.Terrace Dusk
open scoped Topology BigOperators ContDiff

variable {G:Gauge}{C:Family G}{V:Type*}{l:Filter V}{T s w y:V→ℝ} {a b c:ℝ}
variable (hT:Tendsto T l atTop) (hG:G.Simple)(θ: PostT C.path.levels)
variable {W r D} (L:LogPackage C W r D)
local notation "Y!"=> C.path.levels
local notation "S'" => C.path.levels.budget
local notation "δ'"=> renal C.path.levels
local notation "η'"=> near C.path.levels
local notation "τ'"=> PhysicalNext.Repeat.Legato.Bandage.fly C.path.levels
local notation "β!"=> C.path.levels.clock.hatBeta
local notation "α!"=> C.S.a
variable {j k m: V→ℕ}

lemma Layer.gainT (hx: RateIs l T (fun i=> α! (k i)/α! (m i)) a): RateIs l T (fun i=> gainChart C.path (m i) (k i)) ((1/8)*a):=by
   refine (hx.rpow (1/8)).congr ?_; apply Eventually.of_forall; intro i; unfold gainChart; dsimp only; rw [Real.rpow_def_of_pos (div_pos (C.S.a_pos _) (C.S.a_pos _)),Real.log_div (C.S.a_pos _).ne' (C.S.a_pos _).ne']; simp only [Schedule.scale, Family.S,Real.log_inv]; congr 1; ring
include hT
variable (hk:Layer C l T k) (hm:Layer C l T m)
variable (ht:RateIs l T (fun i=> C.S.a (k i)/C.S.a (m i)) a) (ha:0<a)
include L hk hm ht ha
lemma reef_toll (D':ℕ)(hX:RateIs l T y c)(hw:RateIs l T w b)(hf: b < c+((D':ℝ)+1/8)*a): ∀ᶠ i in l,
    let u:=m i; let v:=k i; let X:=y i; let f:=(1+(C.path.levels.params u).columns); let e:= 4*f*(2*(C.S.a (u+1)^D'*(β! (u+1)*(4*(1/X)))))
    march (fun _:Unit=>w i) (η') v u () ≤ δ' u * (X / (16* β! (u+1))) ∧
      32*f*w i*‖alto C.path v D'‖*(e/gainChart C.path u v) ≤ τ' D' v/2:=by
   let d:=D'; let t(i:V):=m i+1; have hu:=(hm.next hT L).beta hT; have hv:=(tower_attach (hm.jump hT L) ht).swap (add_zero a); have hw':=((relation_inv ht).power (D'+1)); have hT':=(hm.renalT hT L).mul (hX.div ((RateIs.const (c:=16) hT (by norm_num)).mul hu)); have hz:= (hw.mul hw').mul ((hm.fly hT D').div (hk.fly hT D')); let f i:=1+((Y!).params (m i)).columns; have hF:= hm.columns hT L
   let z i:=2*((C.S.a (t i)/C.S.a (k i))^d*(β! (t i)*(4*(1/y i))))
   have h₄:= RateIs.const (c:=4) hT (by norm_num); have h₂:= RateIs.const (c:=2) hT zero_lt_two
   have hB : RateIs l T (fun i=> 32*f i*w i*((4*f i*z i)/gainChart C.path (m i) (k i))) (b-(d*a+c)-1/8*a):=by
      refine ((((RateIs.const (c:=32) hT (by norm_num)).mul hF).mul hw).mul (((h₄.mul hF).mul (h₂.mul (((relation_inv hv).power d).mul (hu.mul (h₄.mul ((RateIs.const hT one_pos).div hX)))))).div (Layer.gainT ht))).swap ?_; ring
   filter_upwards [ hT'.overtakes (hz.pays hT) hT (by push_cast; linarith only [ha,hf]),((hk.fly hT D').div h₂).overtakes (hB.pays hT) hT (by change b-(D'*a+c)-1/8*a < _;linarith only [hf]), hw.pos, tower_earlier hT ht ha,hk.grows.eventually_ge_atTop (C.ref d)] with i hi hc hW hp hJ u v X f' e
   refine ⟨(seeing C D' L.system hW u v hJ hp.le).trans hi.le, (le_of_eq ?_).trans hc.le⟩; unfold z e; rw [alto_norm]; change 32*f'*w i*(α! v^d)⁻¹*(4*f'*(2*(_*(β! (t i)*(4*(1/X)))))/gainChart _ _ _) = 32*f'*w i*(4*f'*(2*((α! (t i)/α! v)^d*(β! (t i)*(4*(1/X)))))/gainChart _ _ _); simp only [div_pow]; exact (by ring)

omit hk ht hm ha
lemma beginning (hg:Layer C l T j)(hm:Layer C l T m)(h₁:RateIs l T (fun i=> C.S.a (j i)/C.S.a (m i)) a)(hp:RateIs l T s 0) (hc: RateIs l T w b)(n:ℕ): RateIs l T (fun i=> initial C.path (δ') (η') (m i) (j i) (s i) (w i) n) ((4*n:ℕ)*a+b):= by
   have he: RateIs l T (fun i=> α! (j i)/α! (m i+1)) a:=(tower_attach (hm.jump hT L) h₁).swap (add_zero a)
   have hf:= (hg.renalT hT L).mul (hg.nearT hT L);
   have hz:= RateIs.const (c:=8) hT (by norm_num)
   exact ((hp.power n).mul (((he.power (4*n)).mul ((hp.div hz).power (n*(n-0)))).mul (((hf.div hz).power n).mul hc))).swap (by ring)

omit L
include hm ht ha hG θ
lemma park_room (D:ℕ) : ∀ᶠ i in l, Push.GridApprox.room (C.path.levels) (k i) (m i) D:=by
    let f i :ℝ:= ((C.path.levels.clock.J (m i) : ℕ):ℝ)+5; let g i:ℝ:=2*((D:ℝ)+30*f i)
    have hL: RateLE l T f 0:= ((Layer.lyra hT hm|>.add (RateLE.const (5:ℝ) hT) hT)).transfer (by filter_upwards [hm.grows.eventually (bench_register hG (Y!) θ)] with i hi; rw [Real.norm_of_nonneg (by unfold f; positivity)]; exact le_trans (add_le_add_left hi _) (Real.le_norm_self _))
    have he: RateLE l T g 0:= by exact ((RateLE.const (2:ℝ) hT).mul ((RateLE.const (D:ℝ) hT).add (((RateLE.const 30 hT).mul hL).mono (le_of_eq (add_zero 0))) hT)).mono (le_of_eq (add_zero 0))
    filter_upwards [ht.overtakes he hT ha] with i hi; refine lt_of_le_of_lt (le_of_eq ?_) ((lt_div_iff₀ (C.S.a_pos _)).1 hi); change 2*(C.path.levels.S.a (m i)* ↑D + Push.GridApprox.tail C.path.levels (m i))= _; unfold Push.GridApprox.tail; unfold g; change 2*(_+30* C.S.a (m i)* f i) = _; ring

include L hk -- hm ht etc
variable {I:Type} [Fintype I][DecidableEq I]
variable (f: Extraction.Order) {S:Table C.book}(F: Final C f S)
variable (d:I→ℕ)
local notation "n'" => Fintype.card I

include F
lemma expense_grid (H: Shipper C.path r D)(HS:Feasible C.path.levels)(T':Stock.Tabs C.path.levels) (d':ℕ)(i₀:I) (hg: Layer C l T j)(hb:0<b) (hM: RateIs l T (fun i=> α! (m i)/α! (j i)) b)(B: I → V→ℝ)
    (t: I→ℝ) (hB:∀ i,RateIs l T (B i) (t i)) (c:ℝ)(hc:(4*n':ℕ)*b+ (∑ v:I,t v)-((d':ℝ)+1/8)*a<c):
    ∃ o e: V→ℝ,RateLE l T o c ∧ ∀ᶠ i in l, ShortPrice C (e i) (o i) (fun v=> C.S.a (j i)^(d v)*B v i) d' d (k i) (m i) (j i) := by
   let w i t:= τ' (d t) (j i)/B t i; let α i:= solvency L n' (j i); let Z i:= initial C.path δ' η' (m i) (j i) (α i) (∏ s,w i s) n'
   let c₀:= -(4*n':ℕ)*b - (∑v:I,t v); let K(i:V):= basin Y! T' (k i); let u i:=m i+1
   have hf(i):= tracks Y! T' (k i); have he:0<n':= Fintype.card_pos_iff.mpr ⟨i₀⟩
   have hZ : RateIs l T Z c₀:=by
      refine (beginning hT L hg hm (relation_inv hM) (Layer.tuition hT L hg n' he) (RateIs.prod (fun v (_:v∈Finset.univ)=> (hg.fly hT _).div (hB v)) hT) n').swap ?_; unfold c₀; simp only [zero_sub, Finset.sum_neg_distrib]; ring
   have hK := hk.basinLevel hT hG θ T'
   let e i:= 4*(1+((Y!).params (m i)).columns)*(2* (C.S.a (m i+1)^d'*(β! (m i+1)*(4*(1/Z i)))))
   let f i:=Real.exp (-c*T i); have hh:RateIs l T f (-c) := RateIs.exp _ hT; let o i:= 2*(endpointT C (k i) (K i)/f i)
   have hg': RateIs l T (fun i=> α! (K i)/α! (m i)) a:= (tower_attach ht (relation_inv (hk.basinJump hT hG θ T'))).swap (by simp)
   have hL := reef_toll hT L hK hm hg' ha d' hZ hh (by unfold c₀; linarith only [hc]);
   obtain ⟨χ,hχ⟩:= L.lightCuts.mother
   obtain ⟨m',hm'⟩:= yield_ticket C hG HS θ T'
   have hf' := tower_earlier hT (tower_attach hM (relation_inv (hm.jump hT L))) (by linarith only [hb]); let X i:= (S' (m i+1)).B;
   refine ⟨o,fun i=>2*e i, ?_, ?_⟩
   · have hu:RateLE l T (fun i=>endpointT C (k i) (K i)) 0:=((((Layer.beta hT hk).pays hT).pow m' hT).mono (by simp)).of_norm_le (by filter_upwards [hk.grows.eventually hm'] with i hi; rw [Real.norm_of_nonneg (end_nn ..|>.le)]; exact hi)
     simp_rw [o, div_eq_mul_inv]; exact ((RateLE.const (2:ℝ) hT).mul (hu.mul (hh.inv.pays hT))).mono (by simp)
   have hU:RateLE l T (fun i=>(X i:ℝ)^2+1) 0:= (((Layer.cover hT (hm.next hT L)).pow 2 hT).mono (by simp)).add (RateLE.const (1:ℝ) hT) hT
   have hh: ∀ᶠ i in l,∀ x : ℕ,u i ≤ x → n' ≤ r x:= (hm.next hT L).grows.eventually ((eventually_ge_atTop ((eventually_atTop.mp (L.spare.eventually_ge_atTop n')).choose)).mono (fun x hx y hy=> (eventually_atTop.mp (L.spare.eventually_ge_atTop n')).choose_spec y (hx.trans hy)))
   filter_upwards [hZ.pos,hf', tower_earlier hT hg' ha, hL, park_room hT hG θ hm ht ha (lensScope C d'), (tower_attach (hm.jump hT L) ht).overtakes hU hT (by simp [ha]), hh,eventually_all.mpr fun s=> (hB s).pos,hk.grows.eventually_ge_atTop (C.ref d'),eventually_all.mpr (fun v=>hg.grows.eventually_ge_atTop (C.ref (d v)))] with i hi ht hK hW hr hU hA hB hN hM
   -- hx:i+1< etc
   change m i+1< j i at ht; have ht'(v):0 < τ' (d v) (j i):= inv_pos.mpr (pow_pos (zero_lt_one.trans ((Y!).fits.delayed _)) _)
   refine ⟨fun N p hn ht₁ v Ω he' hx hy hi' hv=>?_,hN.trans ((hf i).1.trans hK.le)⟩
   have hw (p:ℕ): ((S' (m i+1)).B^2+1:ℕ) ≤ (C.S.toDepth (((hf i).1.trans hK.le).trans (m i|>.le_succ)) p).count.val := by
       let v:= C.S.toDepth (((hf i).1.trans hK.le).trans (m i|>.le_succ)) p; have hl: ((X i:ℝ)^2+1) ≤ v.count.val:= le_of_mul_le_mul_right ((lt_div_iff₀ (C.S.a_pos _)).1 hU|>.le |>.trans_eq ((C.S.embeds_scale v).symm.trans (mul_comm ..))) (C.S.a_pos (u i))
       exact_mod_cast hl
   have hb'(t:I) : w i t * Spindle.paid C (d t) (j i) N p (v t) ≤ τ' (d t) (j i):= by
       unfold w; rw [mul_comm,_root_.mul_div_assoc' , div_le_iff₀ (hB t), mul_comm (Spindle.paid ..)]; apply mul_le_mul_of_nonneg_left _ (ht' t).le; apply le_of_mul_le_mul_left _ (pow_pos (C.S.a_pos (j i)) (d t)); rw [obey_quota]; exact he' t
   exact joinsD C N (m i) p d' (k i) (K i) i₀ (f i) (w i) Ω (hf i).1 hK.le hn ht.le d v F.room.cutoff L.system L.literal (hχ d') T' (hf i) H hG hN hM hb' (fun s=>div_pos (ht' s) (hB s)) hr hx (hw p) hy (solvency_pos L _ he) (solvency_le L _ he) (short L) ht (fun k _ hp=> ⟨solvency_anti L n' he hG hp.le,short_affords L k⟩) (fun k hk _=>hA k hk) _ (fun _=>rfl) hi' hv hi le_rfl (Real.exp_pos _) hW.1 le_rfl hW.2
end YM.GapsContact.Seams
