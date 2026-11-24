import YM.SignedWilsonExpansion.Purchase.WakePay
/-! # Filter propagation.Names Entry charged through weight equality + circle dressing
This uses actual Ψ.Proposal columns `atCut Bel.fields`. Pose/Core budgets.Solver paycheck.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.SignedWilsonExpansion.Purchases
open Asymptotics PhysicalNext.Repeat.Quince.PreCost WilsonCoeffUV.Bank Function Filter Matrix Lattice RG Wilson Gauge Extra.Histories Analysis
open WilsonCoeffUV.Mer.Xa.FetchP Labels Trace.Physical.Germ Trace.Physical.GermGraph
open Source Work.G08 Next.Rank.Price Next.Rank Perch Commission Real
open scoped Classical ContDiff BigOperators Topology
variable {G:Gauge} {d l r:ℕ}{C:Family G}{F:Frame G d}{ι:Type}{Y W ν ρ B:ι→ℝ}{L:Filter ι}{j m n N p:ι→ℕ}
local notation "F₀" => (C.labels.level d)
open PurchVoice UVClock YM.MergeProof YM.MergeProof.Ribbons
abbrev CashY (L:Filter ι)(B:ι→ℝ){K:Type*}[Norm K](X:ι→ℝ): (ι→ K)→Prop:= Wage L (Spread B) X
abbrev CashM (L:Filter ι)(B:ι→ℝ){K:Type*}[Norm K](X:ι→ℝ): (ι→ K)→Prop:= Wage L (dollar B) X
variable {A:ι→( C.label d≃ₗ[ℂ] C.label d )}
variable (g':C.Makes)
structure ArmVote (L:Filter ι)(B:ι→ℝ)(C:Family G)(d:ℕ)(N p j n:ι→ℕ)(Y ν:ι→ℝ)(A:ι→ (C.label d≃ₗ[ℂ] C.label d)): Prop where
    simple:G.Simple
    h : Rise B L
    age : Epoch L B C.path.levels j
    epoch : Epoch L B C.path.levels ( j + n )
    credit_Y : CashY L B (1:ι→ℝ) Y
    credit_ν : CashY L B ( cent B ) ν
    fwd : ∀ᶠ i in L,ReadyReturn C d (N i) (p i) (j i) (n i) (A i) ∧ Nonempty (PurchVoice C d (N i) (p i) (j i) (n i)) ∧ ∃ T,FrontStep C d (j i) (n i) (N i) (p i) (Y i) (ν i) T
variable (q:ArmVote L B C d N p j n Y ν A)
variable {P Z:ι→ C.label d}
namespace ArmVote
include q g'
lemma f_enough : ∀ᶠ i in L,(j+n) i ≤ N i:= q.fwd.mono fun i hi=> hi.1.age
lemma start_enough : ∀ᶠ i in L, j i≤N i:= ( f_enough g' q ).mono fun i hi=> (Nat.le_add_right ..).trans hi
-- mark hats Epoch.Interface cost
lemma χ₁ : Tendsto (fun i=> phaseF C (j i) ((j+n) i) (N i) (p i)) L (𝓝 1):= phase_hats q.h C q.simple g' q.age p q.epoch (f_enough g' q) (start_enough g' q)
-- price auxiliaries following §25. Test two configurations installed in same Epoch.Anchor.Width.Sep
lemma pulse_income : CashY L B 1 (fun i=> pollS F₀ (Y i)):=by
     simpa [Function.comp] using Wage.mul (Wage.unitC (2:ℝ)) ( Wage.ornament (chargeS F₀) _ q.credit_Y )
lemma damask : CashY L B (cent B) (fun i=> pace F₀ (Y i) (ν i) (prec C d (j i) (p i)) (tollQ C d (j i) (p i)) ):=by
    let e:= cent B; let φ:= prec_w q.h C q.simple q.age d p; let uv:= pulse_income g' q; let w(i):= tollQ C d (j i) (p i); let H: CashY L B e w:= (Wage.enroll ( ( toll_w q.h C q.simple q.age 1 d p ).trans ( by simpa only[pow_one] using! mark_cent q.h ) ) ); let h:= spreadMax q.h; let x(i):=2*prec C d (j i) (p i); have hv: CashY L B e x:=by simpa using Wage.mul ( Wage.unitC (2:ℝ) ) φ
    let y(i):= money F₀ ( Y i ) ( ν i ) (w i); have hz: CashY L B e y:=by simpa using Wage.plus h ( Wage.mul ( Wage.unitC (2:ℝ)) H ) ( by simpa using Wage.mul q.credit_ν ( Wage.plus h uv uv ) ) -- simplify y
    have hs:CashY L B 1 (fun i=>1+x i):= Wage.plus h (Wage.unitC (1:ℝ)) ( hv.clip ( ceases_w q.h ) )
    simpa only [one_mul,Function.comp] using Wage.mul ( Wage.ornament (resUrgent F₀) _ q.credit_Y ) ( Wage.plus h hv ( by simpa only[mul_one] using Wage.mul hz hs ) )
lemma sizeS {Z:C.label d} (v: l≤d)(t:∀ᶠ i in L, C.S.a (j i)≤ρ i) : CashY L B (fun i=> dollar B i^r) (fun i=> ξSize C d (j i) (N i) (p i) l r (ρ i)):=by
    apply Wage.rel (( ηIP q.h C q.simple g' q.age p (start_enough g' q) ).power r); refine IsBigO.of_bound' ( t.mono (fun i hi=>?_) ); exact (ζPrice (N:=N i) (p:=p i) (r:=r) v hi).trans_eq (norm_pow _ _).symm -- implicit hi `i`
lemma fee_up {x:ι→ C.label d}(v: l≤d)(t:∀ᶠ i in L, C.S.a (j i)≤ρ i) (χ:C.label d)(hm:∀ᶠ i in L, Attention C d (j i) (N i) (p i) l r (ρ i) (x i) χ) : CashY L B (fun i=> dollar B i ^ r ) (fun i=>(F₀).coeffSize (saveS C d (j i) (n i) (N i) (p i) (ρ i) (x i))):=by
    let K'(i):= ξSize C d (j i) (N i) (p i) l r (ρ i); have hh: CashY L B (1:ι→ℝ) (fun i=>1+2*prec C d (j i) (p i)):= Wage.plus ( spreadMax q.h ) (Wage.unitC (1:ℝ)) ( ( Wage.clip ( by simpa only [one_mul] using Wage.mul (Wage.unitC (2:ℝ)) (prec_w q.h C q.simple q.age d p) ) (ceases_w q.h)))
    apply Wage.rel (q:= fun i=> ((1+2*prec C d (j i) (p i)) * (‖K' i‖*((F₀).coeffSize χ)))) (w:= ?_) (?_) -- check v₀ arg
    · simpa only [one_mul,mul_one] using Wage.mul hh (Wage.mul (( sizeS (r:=r) (Z:=χ) g' q v t).norm) (Wage.unitC ((F₀).coeffSize χ)))
    apply IsBigO.of_bound'; filter_upwards [hm,q.fwd] with i hi hK; obtain ⟨H,⟨P⟩,T,hT⟩:= hK; rw [Real.norm_of_nonneg (size_nonneg _ _)]; exact (cheap P g' hT H hi).trans (le_abs_self _)
lemma censusYn {x:ι→ C.label d}(v:l≤d)(t:∀ᶠ i in L,C.S.a (j i)≤ρ i) (χ:C.label d)(hm:∀ᶠ i in L,Attention C d (j i) (N i) (p i) l r (ρ i) (x i) χ): CashM L B (1:ι→ℝ) (fun i=>(F₀).coeffSize (saveS C d (j i) (n i) (N i) (p i) (ρ i) (x i))):= by
    have hv:= Wage.transfer ( fee_up g' q v t χ hm ) ( polyCost q.h ); refine Wage.ascend hv (?_); simpa using! ( self_w q.h (dollar B) ).power r
-- from sizeS all grade.ArmVote.bulk covariance repair.
lemma census_Υ {x:ι→ C.label d}(h:CashM L B (1:ι→ℝ) (fun i=>(F₀).coeffSize (saveS C d (j i) (n i) (N i) (p i) (ρ i) (x i)))): CashM L B (1:ι→ℝ) (fun i=> qKey C d (j i) (n i) (N i) (p i) (ρ i) (A i) (x i)):=by
    let t(i):=pollS F₀ (Y i)* (F₀).coeffSize (saveS C d (j i) (n i) (N i) (p i) (ρ i) (x i)); have hv:CashM L B 1 t:=by simpa using Wage.mul (Wage.transfer (pulse_income g' q) (polyCost q.h)) h
    apply hv.rel; apply IsBigO.of_bound'; filter_upwards [q.fwd] with i hi; obtain ⟨y,⟨P⟩,T,hT⟩:=hi; exact (Size.norm_le ..).trans (( cheapNormalized P g' hT y (ρ:=ρ i) (x i)).trans (le_abs_self _))
lemma firing (Z:ι→ (F₀).Coeff)(a:ℕ)(ε:ι→ℝ)(X:(F₀).Index)(pZ: CashM L B ε Z) : CashM L B ε (fun i=> F₀|>.scaled (shrink C (( j + n ) i) (N i) (p i)) (Z i) X):=by
    let s (i):= shrink C ((j+n) i) (N i) (p i); have hp:=ηPrice q.h C q.simple g' q.epoch p (f_enough g' q); have hv:s=O[L] (1:ι→ℝ):=by
        have hK: ((dollar B)⁻¹)=O[L] (cent B):=by refine IsBigO.of_bound' (Eventually.of_forall (fun i=>?_)); change ‖(dollar B i)⁻¹‖≤ _; rw [penny,norm_mul]; apply mul_le_of_le_one_right (norm_nonneg _); rw [Real.norm_of_nonneg (hedge _ _|>.le)]; exact exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (boil_pos _) (by norm_num))
        exact isBigO_const_of_tendsto ( Wage.next_zero ( hp.clip hK ) (daybreak q.h )) one_ne_zero
    have hX: CashM L B (fun i=>(1:ℝ)) (fun i=> ((s i ^ ((F₀).grades X).2:ℝ):ℂ)):= Wage.reals.mp ( by simpa using ( Wage.power (Wage.enroll (u:=dollar B) hv ) ((F₀).grades X).2 ) ); simpa only [Frame.scaled_apply,CashM,one_mul] using! ( Wage.mul (B:=1) hX ( Wage.rel pZ (p:=fun i=> Z i X) (IsBigO.of_bound' (Eventually.of_forall fun i=> norm_le_pi_norm _ _))))
lemma fires {x:ι→ C.label d}(h:CashM L B (1:ι→ℝ) (fun i=>(F₀).coeffSize (saveS C d (j i) (n i) (N i) (p i) (ρ i) (x i))))(i:(F₀).Index): CashM L B (1:ι→ℝ) (fun k=>furnace C d (j k) (n k) (N k) (p k) (ρ k) (A k) (x k) i):= firing g' q _ 0 _ _ ( census_Υ g' q h )
-- top: high slot receives upper bound with explicit offgrade tilt. sign funded horizon from estimation.Frame assembly.
lemma paceHour {x:ι→ C.label d} (t:∀ᶠ i in L, C.S.a (j i)≤ρ i) (χ:C.label d)(hm:∀ᶠ i in L,Attention C d (j i) (N i) (p i) d r (ρ i) (x i) χ) (i:(F₀).Index)(c:r≤ ((F₀).grades i).2): CashY L B (cent B) (fun k=> (furnace C d (j k) (n k) (N k) (p k) (ρ k) (A k) ( x k ) i) - (( ↑(phaseF C (j k) ((j+n) k) (N k) (p k)) ):ℂ)^r * χ i):=by
    let w:= ((F₀).grades i).2; let T₁ (k):=shrink C ((j+n) k) (N k) (p k); let U(k):=ξSize C d (j k) (N k) (p k) d r (ρ k); have ht: CashY L B (fun k=> (dollar B k)^r) U:=sizeS (Z:=χ) g' q le_rfl t; let V(k):= ( T₁ k:ℂ)^w; have hi: CashY L B (fun k=> (( dollar B k)^w )⁻¹) V:=by
       have hζ:= ( Wage.reals.mp (ηPrice q.h C q.simple g' q.epoch p (f_enough g' q) ) ).power w; exact hζ.fix (.refl ..) (Eventually.of_forall fun k=> inv_pow ..) -- gB?
    have H: CashY L B 1 (fun j=> V j*U j):= Wage.clip ( Wage.mul hi ht ) ( by
       apply IsBigO.of_bound'; apply Eventually.of_forall; intro j; let x:= dollar B j; have h:1≤x:= dollar_ge ..; have hx(l:ℕ):0<x^l:=zero_lt_one.trans_le (one_le_pow₀ h); change ‖(x^w)⁻¹*x^r‖≤ ‖(1:ℝ)‖; rw [Real.norm_of_nonneg (by positivity),norm_one,mul_comm, ← div_eq_mul_inv,div_le_one (hx _)]; exact pow_le_pow_right₀ h c )
    let Z':= fun k=>pace F₀ (Y k) (ν k) (prec C d (j k) (p k)) (tollQ C d (j k) (p k)); have h0: CashY L B (cent B) (fun k=> ‖V k*U k‖*Z' k * (F₀).coeffSize χ):=by simpa only[one_mul,mul_one] using Wage.mul (Wage.mul H.norm (damask g' q)) (Wage.unitC ((F₀).coeffSize χ))
    apply Wage.rel h0; apply IsBigO.of_bound'; filter_upwards [hm,t,q.fwd] with k pT hu hw; obtain ⟨y,⟨P⟩,T,t⟩:=hw; have he:= head P g' t y ((C.S.a_pos _).trans_le hu) pT i; refine he.trans (?_); refine le_trans (le_of_eq (show _=‖V k*U k‖*Z' k * (F₀).coeffSize χ from ?_ )) (le_abs_self _); unfold V U ξSize; rw [←mul_assoc ((↑(T₁ k):ℂ)^w)]; rfl
lemma furnace_unit {x:ι→C.label d} (ht: (fun i=> x i)=ᶠ[L] (fun i=> C.refUnit d)): (fun i=> furnace C d (j i) (n i) (N i) (p i) (ρ i) (A i) (x i))=ᶠ[L] fun i=> (((C.S.a ((j+n) i))/ (ρ i):ℝ):ℂ)^d • ((F₀).e0):=by
     filter_upwards [ht,q.fwd] with i hu y; obtain ⟨h,⟨P⟩,-,-⟩:=y; change x i=C.refUnit d at hu; change furnace C d _ _ _ _ _ _ (x i)= _; rw [hu, furnace, qKey,keyQ,savePage_unit g' h.late.post ((Nat.le_add_right ..).trans h.age),← P.unit_touch g' h,LinearEquiv.symm_apply_apply,unitVec,map_smul,map_smul,Frame.scaled_unit,smul_smul]; congr 1; rw [Complex.ofReal_div,div_pow,div_eq_mul_inv,mul_comm]; rfl
-- Strong spin width.Window same chamber & normalized source. Of.Mesh-receipt.Cool.Price.Shelf
lemma qPrice (s₀:Extra.Histories.Motion) (x:ι→C.label d) (hx: CashM L B 1 (fun i=> F₀|>.coeffSize (saveS C d (j i) (n i) (N i) (p i) (ρ i) ( x i)))) (hy: CashM L B 1 (fun i=> F₀|>.coeffSize (saveS C d (j i) (n i) (N i) (p i) (ρ i) ( Extra.Histories.Motion.patch F₀ s₀ (x i))))) (v:∀ᶠ i in L,Spinning C d (j i) (N i) (p i))(a:ℕ):
    let U:=Extra.Histories.Motion.patch F₀ s₀; let x':=U∘x; let qP(i):=qKey C d (j i) (n i) (N i) (p i) (ρ i) (A i); CashM L B (fun i=> mark B i^a) (fun i=> qP i (x' i)- U (qP i (x i))):=by
    intro U x' qP; let zC:= (F₀).coeffSize; let t(i):= tollQ C d ( j i ) (p i); let w:=pulse_income g' q; let T₁ (i):=pollS F₀ (Y i); let f(i):=saveS C d (j i) (n i) (N i) (p i) (ρ i); let hk: CashM L B 1 T₁:= Wage.transfer w (polyCost q.h); let B'(i):= mark B i ^a; let hu: CashM L B B' t:= Wage.enroll (toll_w q.h C q.simple q.age _ _ _) ; let p(i):=(2*t i*T₁ i)*( zC ( f i (x' i))+ Extra.Histories.Motion.orbitCost F₀*zC ( f i ( x i ))) + phasePollCost F₀ (Y i)*t i*zC ( f i (x i))
    have hK: CashM L B B' p:= by
         apply Wage.plus (dollarMax q.h)
         · simpa only [one_mul,mul_one] using! Wage.mul ( Wage.mul ( Wage.mul ( Wage.unitC (2:ℝ) ) hu ) hk ) ( Wage.plus (dollarMax q.h) hy ( by simpa only[one_mul] using! Wage.mul (Wage.unitC (Extra.Histories.Motion.orbitCost F₀)) hx ))
         simpa only [one_mul,mul_one] using! Wage.mul ( Wage.mul ( Wage.mul ( Wage.unitC (4*Extra.Histories.Motion.orbitCost F₀) ) hk ) hu ) hx
    apply Wage.rel hK; refine IsBigO.of_bound' ?_; filter_upwards [q.fwd,v] with i hi he; obtain ⟨y,⟨P⟩,T,h⟩:=hi; exact (Size.norm_le ..).trans ((qSpins (ρ:=ρ i) P g' h y he s₀ (x i)).trans (le_abs_self _))
lemma spinAccuracy (s₀:Extra.Histories.Motion) (x:ι→C.label d) (hx: CashM L B 1 (fun i=> F₀|>.coeffSize (saveS C d (j i) (n i) (N i) (p i) (ρ i) ( x i)))) (hy: CashM L B 1 (fun i=> F₀|>.coeffSize (saveS C d (j i) (n i) (N i) (p i) (ρ i) ( Extra.Histories.Motion.patch F₀ s₀ (x i))))) (v:∀ᶠ i in L,Spinning C d (j i) (N i) (p i))(a:ℕ)(i:(F₀).Index):
    let U:=Extra.Histories.Motion.patch F₀ s₀; let x':=U∘x; let qP(i):=furnace C d (j i) (n i) (N i) (p i) (ρ i) (A i); CashM L B (fun i=> mark B i^a) (fun j=> (qP j (x' j)- U (qP j (x j))) i):=by
     intro U x' qP; let K (i):=qKey C d (j i) (n i) (N i) (p i) (ρ i) (A i); have hv:= firing g' q (fun i=> K i (x' i)- U ( K i (x i))) 0 _ i (qPrice g' q _ _ hx hy v a)
     have hs(t:ℝ)(v:C.label d): ((F₀).scaled t) ( U v )= U (((F₀).scaled t) v):=by
        unfold U Extra.Histories.Motion.patch; split; · rw [Push.Local.scaled_star, Frame.scaling]
        exact (F₀).scaling ..
     refine hv.fix (Eventually.of_forall fun j=> ?_) (.refl ..); dsimp only; rw[map_sub,hs]; rfl
-- Ownership lightweight: probes cap unit and rotation. No topology q.S at stage Step.
end ArmVote
end YM.SignedWilsonExpansion.Purchases
