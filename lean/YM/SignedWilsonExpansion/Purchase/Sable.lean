import YM.SignedWilsonExpansion.Purchase.Rights
import YM.SignedWilsonExpansion.Purchase.TickP
import YM.TraceExtension.Quince.Nectar
/-! # Carry one **actual** finite top (interior)
Artifact-facing names are in HarvestW. These derive rights from SAME silicon
on Broad/Skill only. TillP costs from BN, so extra delays need only length,
no extra East pre-payment. Does not assert any relation to arbitrary elected
representatives of the same measure. -/
set_option autoImplicit false
set_option maxHeartbeats 640000
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince.PreCost
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source Pressure
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Legato Malachite
open Mallow Lotus Planned.PrimaryIntegral295 PPX Place
open SignedWilsonExpansion.Purchases WilsonCoeffUV.Mer.Xa.FetchP WilsonCoeffUV.Bank
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Bid Labels Extra.Iteration.Scales Work.G08
set_option quotPrecheck false
variable {G:Gauge}{M:Metals G}{D:Rolls M.p}{A:Alloy M D}{X:Factor A}{C:ℕ→ℝ}{K:Worth}(b:Bandage X C K)(Z:Bolt A){N i j m p d:ℕ}
local notation "H"=> Issue.trail Z
local notation "T"=> A.B.a
local notation "J"=> A.B.a.clock.J
local notation "L"=> A.B.a.S.block i
local notation "B" d:max=> localSection G d
local notation "F"=> ( Labels.frames G |>.level d)
local notation "ℓ" i:max=> ((T).S.block i)
-- honor d directly
lemma columns_price (N0:Side): puffs N0≤ N0.val:= by
    have ht:1≤(N0.val:ℝ):= by exact_mod_cast Nat.succ_le_of_lt N0.property
    unfold puffs; apply le_trans (Real.rpow_le_rpow_of_exponent_le ht (by norm_num: (1:ℝ)/8≤1)); exact (Real.rpow_one _).le
include b
lemma column_stock : (T|>.params (i+1)).columns ≤ (L).val:= by
    have hp:=le_trans (b.clock.bank i) (columns_price L); have hz:=one_le_pow₀ (n:=6) (K.prices ((J (i+1))+1)); let z:=(T|>.params (i+1)).columns; have hh:1≤ z:= (T|>.params (i+1)).columns_ge
    have hw: z ≤ (1+z)^2:= by nlinarith
    refine le_trans (hw.trans (le_mul_of_one_le_left (by positivity) ?_)) hp; exact one_le_mul_of_one_le_of_one_le (by norm_num) hz
include Z
lemma tick {Y:ℝ} (he:d+3≤J i)(W: Next.Free.Flight (J (i+1)) (J i)) (hm:4≤ J i) (hz:d≤J (i+1))(f:Blend 2 ((T|>.clock.threshold) (i+1)) ((T|>.clock.threshold) i)) (hL:((L).val:ℝ)≤Y)(hx:(T|>.clock.threshold) (i+1)≤(T|>.clock.threshold) i) :
   let U:= Seal.donne (localSection G d) (sound G d) M.p.kernel.penalty_pos hm (Next.Foundations.valuation G d) W hz f
   RankW F (U.leads L) (Y^(d+1)):=by
    intro U
    let ℒ:= ((L).val:ℝ); have h:1≤ℒ:=by change 1≤(((L).val:ℝ)); exact_mod_cast Nat.succ_le_of_lt (L).property
    have hl:0 < ℒ:= zero_lt_one.trans_le h
    let v:= C (J (i+1)); obtain ⟨hp,hp'⟩:= tillP b (Z) he; have hv: 1≤v:=hp -- omit Z?
    let P:= U.map; let X':=Y^(d+1); let a:= ((T).clock.threshold (i+1)); let c:=((T).clock.threshold i); have heq:= Seal.cap_lead (localSection G d) (sound G d) M.p.kernel.penalty_pos hm (Next.Foundations.valuation G d) W hz f
    have H': Push.Local.triangularPrice F _ ≤ v:= (b.shape _ _ (step_paid A.B.a i) (first_le A.B.valid i) _ he).2 W.legal hm hz
    have hw(x y:(F).Index)(hp:(F|>.grades x).1≤(F|>.grades y).1) : U.map (Size.axis F y) x= if x=y then ((↑(c/a):ℂ))^((F|>.grades y).2) else 0 := through _ (sound G d) W _ M.p.kernel.penalty_pos hm hz a c y x hp
    have hVV(p j:(F).Index) : U.leads L (Size.axis F p) j= (ℒ:ℂ)^(d-(F|>.grades p).1)*U.map (Size.axis F p) j:=by
       change U.map (vowel F L (copy F p)) j=_; rw [ PPX.vowel_col,map_smul ]; change (((L).val:ℂ)^(d-_))*_= _; push_cast [ℒ]; rfl
    have hs (j:(F).Index): (F).coeffSize (Size.axis F j)=1:= by
       classical
       unfold Frame.coeffSize Size.axis; rw [Finset.sum_eq_single j]
       · simp
       · intro i h' hp; simp [hp]
       simp
    refine ⟨fun j=>?_,fun j k=>?_,fun j k t q=>?_⟩
    · rw [hVV, hw _ _ le_rfl, if_pos rfl,norm_mul,norm_pow,norm_pow,Complex.norm_real, Complex.norm_real]; exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (h.trans (le_abs_self ℒ))) (one_le_pow₀ (((one_le_div f.fine).2 hx).trans (le_abs_self _)))
    · rw [hVV,norm_mul,norm_pow, Complex.norm_real,Real.norm_of_nonneg hl.le]; have hk: v ≤ Y:= (show v ≤ ℒ from le_trans (show v≤4*v from by linarith only [hv]) (hp'.trans (columns_price L))).trans hL
      rw [pow_succ]; refine mul_le_mul ((pow_le_pow_right₀ h (Nat.sub_le ..)).trans (pow_le_pow_left₀ hl.le hL d)) (le_trans ?_ hk) (norm_nonneg _) (pow_nonneg (zero_le_one.trans (hv.trans hk)) _); apply ((norm_le_pi_norm ..).trans (Size.norm_le F _)).trans; apply (heq.cost (Size.axis F k)).1.trans; rw[hs,mul_one]; exact H'
    rw [hVV, hw _ _ t, if_neg q, mul_zero]
-- tied top weight column all slots (for proof (25))
omit b Z in
lemma dict (W: Next.Free.Flight (J (i+1)) (J i))(hm:4≤ J i)(hz:d≤ J (i+1))(f:Blend 2 ((T|>.clock.threshold) (i+1)) ((T|>.clock.threshold) i))
    (r:ℕ)(u:(F).Coeff)(hw:∀ j, u j≠0→ (F|>.grades j)=(d,r)) :
    let U:= Seal.donne (localSection G d) (sound G d) M.p.kernel.penalty_pos hm (Next.Foundations.valuation G d) W hz f; U.leads L u=((((T).clock.threshold i/(T).clock.threshold (i+1)):ℝ):ℂ)^r • u:=by
    intro U; let c:=((((T).clock.threshold i/(T).clock.threshold (i+1)):ℝ):ℂ)^r; change _=c•u
    have H' (p) (hP: u p≠0): U.leads L (Size.axis F p)=c • Size.axis F p:=by
       apply funext; intro j; change U.map (vowel F L (Place.copy F p)) j=_; rw [vowel_col,hw p hP]; simp only [Nat.sub_self,pow_zero,one_smul]
       let h: (F|>.grades j).1 ≤ (F|>.grades p).1:=by rw [hw p hP]; exact (F|>.bound j)
       rw [show U.map (copy F p) j= _ from through _ (sound G d) W _ M.p.kernel.penalty_pos hm hz ((T).clock.threshold (i+1)) ((T).clock.threshold i) p j h]
       by_cases h:p=j; swap; · simp [Size.axis, Ne.symm h];
       subst j; simp [Size.axis,hw p hP,c]
    rw [←Size.sum_axes F u,map_sum,Finset.smul_sum]; refine Finset.sum_congr rfl fun i _=>?_ -- L locally overshadow
    by_cases hx:u i=0; · rw [hx,zero_smul,map_zero,smul_zero]
    rw [map_smul, H' i hx]; exact smul_comm ..
abbrev Unison {G:Gauge}{d:ℕ}(B':ℕ→ℝ) (Frame₂:Labels.Frame G d)(P:Frame₂.Coeff→ₗ[ℂ] Frame₂.Coeff)(i:ℕ): Prop:= ∀ (r:ℕ) (v:Frame₂.Coeff),(∀ j,v j≠0→ Frame₂.grades j=(d,r)) → P v=((↑(B' i/B' (i+1)):ℂ)^r) • v
-- omit auto false & notation conflicts
-- receipt only for storage given
structure CapsuleAt (S:ℕ→ℝ)(F':Labels.Frame G d)(H':History G)(P':Hol G)(B':SectionData F')(k N p:ℕ)(Q:ℝ)(ν:ℝ) (P:F'.Coeff →ₗ[ℂ] F'.Coeff) : Prop where
     carries : RankW F' P Q
     tunes : Unison S F' P k
     price (U:Voice F' H' p k)(V:Voice F' H' p (k+1))(u:F'.Coeff)(h: Heard B' H' N p P' k U)(hV: Heard B' H' N p P' (k+1) V)(R:
       (U.plays u).density 0 B' (H'.rep N p k)=blast H' N p k d ((V.plays u).density 0 B' (H'.rep N p (k+1)))) : F'.coeffSize (U.index u-P (V.index u))≤ ν*(F'.coeffSize (U.index u)+F'.coeffSize (V.index u))
lemma job {Y:ℝ} (hn: Nest X Z)(g:G.Simple)(ho:Skill b (bear K)) (he:d+3≤J i)(hL:((L).val:ℝ)≤Y)(hx:(T|>.clock.threshold) (i+1)≤(T|>.clock.threshold) i) :
    ∀ᶠ p:ℕ in atTop,∀ N:ℕ,i<N → ∃ P:(F).Coeff→ₗ[ℂ] (F).Coeff,CapsuleAt (T).clock.threshold (Labels.frames G|>.level d) H (hol G) (localSection G d) i N p (Y^(d+1)) ((2+Y)*(cameo T (i+1))⁻¹) P:=by
    let C₀:=C (J (i+1)); obtain ⟨hC,hC'⟩:= tillP b Z he; let R':= Doors.rate L; let s (i:ℕ):=(T|>.params i).columns; let Y':ℝ:= (L).val
    have RP:0<R':=Doors.rate_pos L; have hY':0< Y':=by unfold Y'; positivity
    have h0:0<Y:= hY'.trans_le hL
    have hp: 1≤C₀:= hC; have hh:0<C₀:= zero_lt_one.trans_le hp; let β:= cameo T (i+1); have hβ:0<β:= cameo_pos ..; have hs:0 ≤ s i:= zero_le_one.trans ((T|>.params i).columns_ge)
    let W:=1+(s i+C₀*Y'^d+R'*Y); have hS:0 < W:= by unfold W; positivity
    let ε:= β⁻¹/W; have hε:0 < ε:= div_pos (inv_pos.mpr hβ) hS
    filter_upwards [rideE (m:=i) b Z hn g ho he (bear_pos K (J (i+1)) (J i)) ε hε] with p h N e
    obtain ⟨hm,hz,hv,hp'⟩:= h N e; let U:=Seal.donne (localSection G d) (sound G d) M.p.kernel.penalty_pos hm (Next.Foundations.valuation G d) (Warehouse.flight H N i) hz hv
    refine ⟨U.leads L,tick b Z he (Warehouse.flight H N i) hm hz hv hL hx,fun r x va=> dict (Warehouse.flight H N i) hm hz hv r x va,?_⟩
    intro U' V u t t' R; let Q:= (F).coeffSize (U'.index u); let f:= (F).coeffSize (V.index u)
    have hz:0 ≤ Q:= size_nonneg ..; have hf:0 ≤ f:= size_nonneg ..
    have hk:= hp' _ _ _ _ (t.earns u).1 (t'.earns u).1 (t.earns u).2 (t'.earns u).2 R
    rw [t.currents, t'.currents] at hk
    have hu: U'.charge u ≤ s i*Q:= (t.cone _).trans (mul_le_mul_of_nonneg_left (size_core ..) hs)
    have hu': V.charge u ≤ Y*f:= (t'.cone _).trans (mul_le_mul ((column_stock b (i:=i)).trans hL) (size_core ..) (size_nonneg ..) h0.le)
    let ψ:= sprite G ((T|>.clock).hatBeta i) L (bear K (J (i+1)) (J i)); have hp:0 ≤ψ:= (sprite_pos _ (bear_pos K ..)).le; have h': ψ≤ β⁻¹:=by
       let a:= bear K (J (i+1)) (J i); have H': ψ=a/β:=by unfold ψ sprite; rw [Push.PriceCompiler.block_eq A.B.valid i, ← cameo_next (A:=A) ]
       have hv:0<a:= bear_pos K ..
       rw [H', div_eq_mul_inv]; apply mul_le_of_le_one_left (by positivity); have hh:=K.prices (J (i+1)); apply (inv_le_one₀ (by linarith only [hh])).mpr; linarith only [hh]
    refine hk.trans ?_
    let K' := Q+f; have hv : f ≤ K':= le_add_of_nonneg_left hz; have hU: Q≤K':= le_add_of_nonneg_right hf
    have hi : ψ*((F).coeffSize ((F).core (V.index u))+V.charge u) ≤ β⁻¹*((1+Y)*K'):=by apply le_trans (mul_le_mul_of_nonneg_left (add_le_add ((size_core ..).trans hv) (hu'.trans (mul_le_mul_of_nonneg_left hv h0.le))) hp); rw [add_mul,one_mul]; exact mul_le_mul_of_nonneg_right h' (add_nonneg (hf.trans hv) (mul_nonneg h0.le (hf.trans hv)))
    have hl: (U'.charge u+C₀*(F).coeffSize (vowel F L ((F).core (V.index u)))+R'*V.charge u) ≤W*K':=by
       let t'':=(F).coeffSize (vowel F L ((F).core (V.index u))); have h: t'' ≤Y'^d*K':= (size_vowel ..).2.trans (mul_le_mul_of_nonneg_left ((size_core ..).trans hv) (pow_nonneg hY'.le _))
       refine (add_le_add (add_le_add (hu.trans (mul_le_mul_of_nonneg_left hU hs)) (mul_le_mul_of_nonneg_left h hh.le)) (mul_le_mul_of_nonneg_left (hu'.trans (mul_le_mul_of_nonneg_left hv h0.le)) RP.le)).trans ?_; unfold W; simp only[add_mul,one_mul,mul_assoc]; linarith only[hf,hv]
    apply le_trans (add_le_add hi (mul_le_mul_of_nonneg_left (show (U'.charge u+(C₀*_+R'*V.charge u)) ≤ W*K' from le_trans (Eq.le (add_assoc ..).symm) hl) hε.le)); change _ + ε*(W*K') ≤ (2+Y)*β⁻¹*(Q+ f); rw [←mul_assoc ε,show ε*W=β⁻¹ from div_mul_cancel₀ _ hS.ne']; unfold K'; exact le_of_eq (by ring)
end YM.PhysicalNext.Repeat.Quince.PreCost
