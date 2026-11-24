import YM.SignedWilsonExpansion.Purchase.Precharge
import YM.Next.RANK.Matrices
import YM.Next.RANK.Reign
/-! # Actual fitted page → ray basis at K
- actual `F` Arrivals same file as Forecast (full wrap)
- Kernel scale ages arbitrary; birth of this trial needs its Own Sound
- cap all data with sign & reflected motions & sectors under EXACT top quantization den.
- bound signed votes for eventual Cohort arity calls. `ρ` reporting scale; fees in homogeneous through cap even if signal lower cap.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.SignedWilsonExpansion.Purchases
open PhysicalNext.Repeat.Quince.PreCost WilsonCoeffUV.Bank Function Filter Matrix Lattice RG Wilson Gauge Extra.Histories Analysis
open WilsonCoeffUV.Mer.Xa.FetchP Labels Trace.Physical.Germ Trace.Physical.GermGraph
open Source Work.G08 Next.Rank.Price Next.Rank
open scoped Classical ContDiff BigOperators Topology
variable {G:Gauge} {d i j l b n c N p r h:ℕ}{C:Family G}{F:Frame G d}{Y ν ρ r':ℝ}
local notation "F₀" => (C.labels.level d)
local notation "H₀" => C.path
local notation "Θ"=> C.path.levels.clock.threshold
local notation "stk"=> C.factory d N p
variable (P:PurchVoice C d N p j n)
variable {T:ℕ→ (C.label d →ₗ[ℂ] C.label d)}
open PurchVoice
variable (g: C.Makes)(u:FrontStep C d j n N p Y ν T){A:C.label d≃ₗ[ℂ] C.label d}(hp:ReadyReturn C d N p j n A)
abbrev savePage (C:Family G)(d j N p:ℕ)(x:C.label d): C.label d:= page d p j ((C.factory d N p).entries j ((C.factory d N p).terminal.symm x))
abbrev prec (C:Family G)(d j p:ℕ):= tollQ C d j p+Perch.bill (-1/2) (C.path.levels.clock.hatBeta j)
abbrev keyQ (C:Family G)(d j n N p:ℕ)(A:C.label d≃ₗ[ℂ] C.label d)(v:C.label d):= A.symm (savePage C d j N p v)
abbrev qKey (C:Family G)(d j n N p:ℕ)(ρ:ℝ)(A:C.label d≃ₗ[ℂ] C.label d)(x:C.label d):= ((ρ:ℂ)^d)⁻¹ • keyQ C d j n N p A x
abbrev furnace (C:Family G)(d j n N p:ℕ)(ρ:ℝ)(A:C.label d≃ₗ[ℂ] C.label d)(x:C.label d): C.label d:= (C.labels.level d).scaled (shrink C (j+n) N p) (qKey C d j n N p ρ A x)
-- Tested is for XYZ; specify at v lifted G. Lead.L.C recalibrated exactly one scale. ξ scales Y direction.
structure Attention (C:Family G)(d j N p l r:ℕ)(ρ:ℝ)(x Z:C.label d) : Prop where
    pure_grade (i : (C.labels.level d).Index) : Z i≠0 → (C.labels.level d).grades i=(l,r)
    paid : ∃ T:C.label d→ₗ[ℂ] C.label d, Tested C d j N p T ∧ Solves C (ρ/C.S.a j) d j N p T Z x ∧ (C.labels.level d).coeffSize (awake C d j N p x-T x) ≤ Perch.bill (-1/2) (C.path.levels.clock.hatBeta j)*(C.labels.level d).coeffSize (awake C d j N p x)
lemma prec0 : 0≤ prec C d j p:= add_nonneg (mul_nonneg (invoice_nn _ _ _) (zero_le_one.trans ((stage C j).columns_ge))) (Real.exp_pos _).le
abbrev tuitionζ (C:Family G)(j N p l r:ℕ)(ρ:ℝ):ℂ:= (((ρ/C.S.a j) : ℝ):ℂ)^l* (((↑(shrink C j N p))⁻¹:ℂ)^r)
abbrev σCoin (C:Family G) (d j N p l r:ℕ)(ρ:ℝ):= (C.S.a j:ℂ)^d*tuitionζ C j N p l r ρ
lemma payAhead (ρ:ℝ)(g:C.Makes) (e:C.ref d≤j)(ht:j≤N)(x Z:C.label d)(b:Attention C d j N p l r ρ x Z) :
    (F₀).coeffSize (savePage C d j N p x- σCoin C d j N p l r ρ • Z) ≤ 2*prec C d j p*(F₀).coeffSize ( σCoin C d j N p l r ρ • Z):=by
    obtain ⟨c,u,v,hc⟩:= b.paid; let w:= shrink C j N p; have h:0<w:= shrink_pos C g ht p; have hw: (w:ℂ)≠0:=Complex.ofReal_ne_zero.mpr h.ne'; let L:= tuitionζ C j N p l r ρ
    have hu: c x= L • Z:=by
       ext1 i; let f:=((F₀).grades i); have H: (w:ℂ)^f.2*c x i=(( ↑ (ρ/C.S.a j) ):ℂ)^f.1 * Z i:=by rw [←Complex.ofReal_pow]; exact congr_fun v i
       unfold L tuitionζ; by_cases e:Z i=0; swap; · have hp: f=(l,r):= b.pure_grade i e; rw [hp] at H; rw [show c x i= ((↑(ρ/C.S.a j):ℂ)^l*Z i)/(w:ℂ)^r from (eq_div_iff (pow_ne_zero _ hw)).mpr ((mul_comm ..).trans H)]; rw [Pi.smul_apply,smul_eq_mul]; unfold w; ring
       simp only [e,mul_zero,mul_eq_zero] at H; exact (H.resolve_left (pow_ne_zero _ hw)).trans (by rw [Pi.smul_apply,e,smul_zero])
    rw [hu] at hc
    let U:=awake C d j N p x; have hz:(F₀).coeffSize U ≤ 2*(F₀).coeffSize (L• Z):= by rw [←hu]; exact Tested.cost C c u _
    let a:ℂ:=(C.S.a j:ℂ)^d; have ha:a≠0:= pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne')
    let t:= (stk).entries j ((stk).terminal.symm x); have hU:t.x=a • U:=by unfold U awake; rw [smul_smul,mul_inv_cancel₀ ha,one_smul]; rfl
    let f:= tollQ C d j p; have hf:0≤f:=mul_nonneg (invoice_nn ..) (zero_le_one.trans ((stage C j).columns_ge)); let β:= Perch.bill (-1/2) (C.path.levels.clock.hatBeta j); have hb:0≤β:=(Real.exp_pos _).le
    let z:=savePage C d j N p x; let y:=a•( L•Z )
    have he:(F₀).coeffSize (z-t.x) ≤f*(F₀).coeffSize (a•U):=by rw [←hU]; exact ( measured_diff d N p j g e ht (entryOk d N p j g e ht ((stk).terminal.symm x))).trans_eq (mul_assoc ..).symm
    rw [show σCoin C d j N p l r ρ • Z=y from (smul_smul ..).symm]; change (F₀).coeffSize (z-y) ≤ _; rw [show z-y=(z-t.x)+(a • (U-L•Z)) from by rw [hU,smul_sub]; unfold y; abel]
    apply ( Size.add .. ).trans ((add_le_add_left he _).trans ?_); unfold y; rw[Size.smul, Size.smul, Size.smul]; have hL:= norm_nonneg a
    have hh:= mul_le_mul_of_nonneg_left hc hL; change f* (‖_‖*_)+_ ≤ 2 * (f+β)*_
    let B₀:=(F₀).coeffSize U; change _ + ‖a‖ * (F₀).coeffSize (U-L • Z)≤ _; change (‖a‖* _)≤‖_‖*(β * B₀) at hh
    refine ((add_le_add_right hh _).trans ?_); apply le_trans _ ( show ( (f+β) * ( ‖a‖*(2*((F₀).coeffSize (L• Z))))) ≤ _ from le_of_eq (by ring)); change f*(‖a‖*((F₀).coeffSize U))+‖a‖*(β*((F₀).coeffSize U))≤ _; have hX:= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz hL) (add_nonneg hf hb); exact le_trans (le_of_eq (show _= (f+β)*(‖a‖*((F₀).coeffSize U)) from by ring)) hX
-- motion.X just finite accurate
lemma cutOwn (g:C.Makes)(p': Opened C d j p)(ht:j≤N)(x:C.label d) :
    (F₀).coeffSize (savePage C d j N p x-columns C d j N p x) ≤
     (2*tollQ C d j p)*(F₀).coeffSize (savePage C d j N p x):=by
   let t:= (stk).entries j ((stk).terminal.symm x); let z:=page d p j t (C:=C); have h:(F₀).coeffSize t.x≤ 2*(F₀).coeffSize z:= (size_gap d N p j g p' ht ((stk).terminal.symm x)).2; have hS:= ( measured_diff d N p j g p'.post ht (entryOk d N p j g p'.post ht ((stk).terminal.symm x)) ); apply hS.trans (le_trans _ (show _ ≤ _ from le_of_eq (show invoice (C:=C) d j p*(stock C j* ( 2 * (F₀).coeffSize z))=2*tollQ C d j p* (F₀).coeffSize z from by unfold tollQ; ring))); exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (zero_le_one.trans ((stage C j).columns_ge))) (invoice_nn ..)
-- unit of savePage exact with v=unitVec. Then all starts incl K thermostat.
lemma savePage_unit (g:C.Makes) (h:C.ref d≤j)(hz:j≤N) : savePage C d j N p (C.refUnit d)= unitVec F₀ C.path j:=by
    let r:= C.ref d; have hS:= g.calibrated d N p (h.trans hz); let y:= unitVec F₀ C.path N; let e: (stk).terminal.symm (C.refUnit d)=y:= ( (stk).terminal).injective ( (LinearEquiv.apply_symm_apply ..).trans ((hS.unit_coord r le_rfl (h.trans hz)).symm.trans ((hS.reads _))))
    unfold savePage; rw [e]; have H':=(hS.unit_coord j h hz); rw [← H']; apply sub_eq_zero.mp; apply size_separates; let t:= g.calibrated d N p (h.trans hz)
    have hY:= measured_diff d N p j g h hz ⟨hS.format j h hz y,hS.cap j h hz y⟩; apply hY.trans; rw [H']; simp [unitVec,map_smul, Size.unit_core, Frame.coeffSize]
lemma save_linear (g:C.Makes)(h:Opened C d j p)(v:j≤N): IsLinearMap ℂ (savePage C d j N p):= (((entry_isLinear d N p j g h v).mk' _).comp ((stk).terminal.symm.toLinearMap)).isLinear
abbrev phaseF (C:Family G)(j k N p:ℕ):ℝ:= ((Real.sqrt (C.path.β N p k))⁻¹) / ((Real.sqrt (C.path.β N p j))⁻¹)
lemma tuneF (u v:ℕ)(hj:C.ref d≤j)(g:C.Makes)(e:j+n≤N)(H:0<ρ):
    (shrink C (j+n) N p:ℂ)^u *(chipAt C j (j+n) u*( (ρ:ℂ)^v)⁻¹ *σCoin C v j N p v u ρ)=(phaseF C j (j+n) N p:ℂ)^u:= by
    let a:ℂ:=ρ; let g₀:=(Real.sqrt (C.path.β N p j))⁻¹; let g₁:=(Real.sqrt (C.path.β N p (j+n)))⁻¹
    let T' := Θ j; let t':= Θ (j+n); let h:ℂ:=C.S.a j
    have h0:a ≠0:= Complex.ofReal_ne_zero.mpr H.ne'; have ht:h≠0:=Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne'
    have hx:( (g₀:ℝ):ℂ)≠ 0:=by unfold g₀; exact Complex.ofReal_ne_zero.mpr (ne_of_gt (inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive g.wilson (show j≤N by omega)))) )
    have hK:( (T':ℝ):ℂ)≠ 0:= Complex.ofReal_ne_zero.mpr (C.path.levels.budget j|>.threshold_pos).ne'; have hz:( (t':ℝ):ℂ)≠0:= Complex.ofReal_ne_zero.mpr (C.path.levels.budget (j+n)|>.threshold_pos).ne'
    change (↑ (g₁ /t') :ℂ)^u * ((↑( t'/T' ):ℂ)^u * (a^v)⁻¹* ( h^v * ((↑(ρ/C.S.a j):ℂ)^v * ((↑(g₀ /T'):ℂ)⁻¹)^u)))=(↑(g₁/g₀):ℂ)^u
    simp only [Complex.ofReal_div]; change _*((↑t'/ (↑ T':ℂ))^u* (a^v)⁻¹* ( h^v * ((a/h)^v*((g₀:ℂ)/(T':ℂ))⁻¹^u)))= _; (simp only [inv_div,div_pow]; field_simp)
include g P hp u
-- normalized in home's units. For neighboring homes any magnitudes can multiply bound by relative home power ≤2^d. For η^l projection at wt=d corresponding conversion is EXACT. Head.
abbrev wpow (Y:ℝ)(F:Frame G d):ℝ:= ( resUrgent F ).buy Y
abbrev pace (F:Frame G d)(Y ν e f:ℝ):ℝ:= wpow Y F*(2*e+ money F Y ν f*(1+2*e))
lemma observedEstimate {x Z:C.label d}(b:Attention C d j N p l r ρ x Z):
    (F₀).coeffSize (savePage C d j N p x) ≤ (1+2*prec C d j p)*(F₀).coeffSize (σCoin C d j N p l r ρ • Z):= (size_triangle ..).trans ((add_le_add_right (payAhead ρ g hp.late.post ((Nat.le_add_right ..).trans hp.age) x Z b) _).trans_eq (by ring))
lemma hueF {x Z:C.label d}(b:Attention C d j N p d r ρ x Z):
   let k:= keyQ C d j n N p A x; let c:=σCoin C d j N p d r ρ; (F₀).coeffSize ( k-chipAt C j (j+n) r• (c•Z) ) ≤ pace F₀ Y ν (prec C d j p) (tollQ C d j p) * (F₀).coeffSize ( c • Z ):=by
       intro k c; let Q:=prec C d j p; let F':=tollQ C d j p; let ζ:=money F₀ Y ν F'; have hε:0≤F':=mul_nonneg (invoice_nn ..) (zero_le_one.trans ((stage C j).columns_ge)); have hp':0 ≤ (chargeS F₀).buy Y:= zero_le_one.trans (Credit.purchase _ u.y); have hH:0≤ζ:= add_nonneg (mul_nonneg zero_le_two hε) (mul_nonneg u.cost (add_nonneg (by unfold pollS; linarith only[hp']) (by unfold pollS; linarith only[hp'])))
       have h: A k= savePage C d j N p x:= LinearEquiv.apply_symm_apply ..
       have he:= P.halfPlease g u hp k (c • Z) r fun i hi=> b.pure_grade i (fun t=>hi (by rw [Pi.smul_apply,t,smul_zero])); rw [h] at he
       exact he.trans ((mul_le_mul_of_nonneg_left (add_le_add (payAhead ρ g hp.late.post ((Nat.le_add_right ..).trans hp.age) x Z b) (mul_le_mul_of_nonneg_left (observedEstimate P g u hp b) hH)) (zero_le_one.trans (Credit.purchase _ u.y))).trans_eq (by unfold pace wpow; ring))
lemma head {x Z:C.label d}(H:0<ρ)(b:Attention C d j N p d r ρ x Z)(i:(F₀).Index) :
    let R:=shrink C (j+n) N p; let r':=((F₀).grades i).2; let t:= (R:ℂ)^r'; let z:ℂ:= (ρ:ℂ)^d
    ‖ (furnace C d j n N p ρ A x) i-(phaseF C j (j+n) N p:ℂ)^r* Z i‖ ≤ ‖t*z⁻¹*σCoin C d j N p d r ρ‖ * pace F₀ Y ν (prec C d j p) (tollQ C d j p) * ((F₀).coeffSize Z) :=by
       intro R r' t z; let k:=keyQ C d j n N p A x; let w:=furnace C d j n N p ρ A x; let c:=σCoin C d j N p d r ρ; let V:=chipAt C j (j+n) r•(c•Z); let ξ:=( (phaseF C j (j+n) N p:ℂ)^r);
       have he:w i=t*(z⁻¹*k i):=by unfold w furnace qKey; rw [Frame.scaled_apply, Complex.ofReal_pow]; rfl
       have hv:t*z⁻¹ * V i= ξ * Z i:=by
         by_cases h:Z i=0; · simp [V,h]
         have h0:r'=r:= congr_arg Prod.snd (b.pure_grade i h); unfold ξ ; rw [← tuneF (d:=d) r d hp.late.post g hp.age H]; simp only [t,h0, V, Pi.smul_apply, smul_eq_mul]; unfold R z c; ring
       change ‖w i- ξ* Z i‖ ≤ _; rw [he, ← hv,←mul_assoc, ←mul_sub,norm_mul];
       refine (mul_le_mul_of_nonneg_left (le_trans ((norm_le_pi_norm (k-V) i).trans (Size.norm_le F₀ _)) (hueF P g u hp b)) (norm_nonneg _)).trans_eq ?_; rw [norm_mul (a:=t*z⁻¹),Size.smul]; ring
-- convenience bound for all bases incl lower caps. We'll use cheap ratio (ρ/a_j), no cutoff re-rooting.
abbrev saveS (C:Family G)(d j n N p:ℕ)(ρ:ℝ)(x:C.label d):= (((ρ:ℂ)^d)⁻¹)•savePage C d j N p x
abbrev ξSize (C:Family G)(d j N p l r:ℕ)(ρ:ℝ) := ((ρ:ℂ)^d)⁻¹*σCoin C d j N p l r ρ
lemma cheap {x Z:C.label d}(b:Attention C d j N p l r ρ x Z):
     (F₀).coeffSize ( saveS C d j n N p ρ x ) ≤ (1+2*prec C d j p)* ( ‖ξSize C d j N p l r ρ‖*(F₀).coeffSize Z ) := by
      unfold saveS; rw [Size.smul]; exact (mul_le_mul_of_nonneg_left (observedEstimate P g u hp b) (norm_nonneg _)).trans_eq (by unfold ξSize; rw [norm_mul,Size.smul]; ring)
omit g P hp u in
lemma ζPrice {l:ℕ} (h:l≤d) (η:C.S.a j≤ρ): ‖ξSize C d j N p l r ρ‖≤ ‖(shrink C j N p)⁻¹‖^r:= by -- mist sign sqrt e.s skip
    unfold ξSize σCoin tuitionζ; have h1:0<C.S.a j:= C.S.a_pos j; have h2:= h1.trans_le η
    let x:=ρ; let y:=C.S.a j; have hz:1≤ x/y:= (one_le_div h1).mpr η; simp only[norm_mul,norm_pow,norm_inv,Complex.norm_real, Real.norm_of_nonneg h1.le,Real.norm_of_nonneg h2.le, Real.norm_of_nonneg (zero_le_one.trans hz)]; let t:= ‖(shrink C j N p)‖⁻¹; have ht:0 ≤ t:= inv_nonneg.mpr (norm_nonneg _)
    rw [Real.norm_of_nonneg (div_nonneg h2.le h1.le)]; change (x^d)⁻¹*(y^d*((x/y)^l*t^r))≤t^r; rw[← mul_assoc, ← mul_assoc]; apply mul_le_of_le_one_left (pow_nonneg ht _); apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz h) (mul_nonneg (inv_nonneg.mpr (pow_nonneg h2.le _)) (pow_nonneg h1.le _))); exact le_of_eq (by unfold x y; rw [div_pow]; field_simp)
omit g u P hp in
lemma qUses (x:C.label d) : qKey C d j n N p ρ A x= A.symm (saveS C d j n N p ρ x):=by unfold qKey keyQ saveS; rw [map_smul]
lemma cheapNormalized (x:C.label d) : (F₀).coeffSize (qKey C d j n N p ρ A x) ≤ pollS F₀ Y * (F₀).coeffSize (saveS C d j n N p ρ x):=(qUses x) ▸ worth P g u hp _
-- other direction at cap unit & real equiv variant note.Caller can supply checkpoint. Use even for reflected partner at noncenter.V assuming page co transformed from (lift patch x) not equality of entries. Bind budgets.
abbrev Spinning (C:Family G)(d j N p:ℕ): Prop:= ∀ (s:Extra.Histories.Motion) (x:C.label d),columns C d j N p (Extra.Histories.Motion.patch (C.labels.level d) s x)=Extra.Histories.Motion.patch (C.labels.level d) s (columns C d j N p x)
open Motion
lemma spentSpins (o: Spinning C d j N p)(s:Extra.Histories.Motion)(x:C.label d) :
    let x':=Extra.Histories.Motion.patch F₀ s x; (F₀).coeffSize (savePage C d j N p x'- Extra.Histories.Motion.patch F₀ s (savePage C d j N p x)) ≤ 2*tollQ C d j p*( (F₀).coeffSize (savePage C d j N p x')+ orbitCost F₀*(F₀).coeffSize (savePage C d j N p x)):= by
    intro x'; let k:=Extra.Histories.Motion.patch F₀ s; let tt:=savePage C d j N p; let u:=columns C d j N p; let z:=2*tollQ C d j p; have hk (x y): k (x-y)=k x - k y:=by
       unfold k Extra.Histories.Motion.patch; rw [_root_.map_sub]; split; · rw [star_sub]
       rfl
    let w:= cutOwn g hp.late ((Nat.le_add_right ..).trans hp.age); have he: (F₀).coeffSize (u x'-k (tt x))≤ orbitCost F₀*(z*(F₀).coeffSize (tt x)):=by
        rw [show u x'=k (u x) from o s x,←hk]; apply (patch_cost ..).trans; refine mul_le_mul_of_nonneg_left ?_ (zero_le_one.trans (orbitCost_one_le ..)); rw [size_sub_rev]; exact w x
    change (F₀).coeffSize (tt x'-k (tt x))≤ _; rw [show tt x'-k (tt x)= (tt x'-u x')+(u x'- k (tt x)) from by abel]; exact (Size.add ..).trans ((add_le_add (w x') he).trans_eq (by unfold z tt; ring))
lemma qSpins (o:Spinning C d j N p)(s:Extra.Histories.Motion)(x:C.label d):
    let x':= Extra.Histories.Motion.patch F₀ s x; let t:= qKey C d j n N p ρ A; let y:=saveS C d j n N p ρ; (F₀).coeffSize (t x'-Extra.Histories.Motion.patch F₀ s (t x)) ≤ (2*tollQ C d j p*pollS F₀ Y)*( (F₀).coeffSize (y x')+ orbitCost F₀*(F₀).coeffSize (y x)) + phasePollCost F₀ Y*(tollQ C d j p)* (F₀).coeffSize (y x):=by
    intro x' t y; let k:= Extra.Histories.Motion.patch F₀ s; let z:=((ρ:ℂ)^d)⁻¹; let C':=(F₀).coeffSize; let f:= savePage C d j N p ; let K:= 2*tollQ C d j p
    have hh: C' ( t x'- A.symm (k (y x))) ≤ K*pollS F₀ Y*( C' (y x')+ orbitCost F₀*C' (y x)):=by
       have hn: (k (y x)) = z• k (f x):=by
          unfold k; change Extra.Histories.Motion.patch F₀ s (z • f x)=z • _; rw [Extra.Histories.Motion.patch_smul, show Extra.Histories.Motion.scalar s z=z from (?_)] ; have hz:z=((↑( (ρ^d)⁻¹)) :ℂ):=by simp [z]
                                                                                                -- comment
          rw[hz,scalar_real]
       have hφ:t x'-A.symm (k (y x))=A.symm (z•(f x'-k (f x))):=by rw [hn,smul_sub,map_sub]; exact congr_arg (·-_ ) ( qUses _ )
       rw [hφ]; apply (worth P g u hp _).trans; rw [ Size.smul ]; refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (spentSpins P g u hp o s x) (norm_nonneg _)) (by unfold pollS; positivity [Credit.purchase (chargeS F₀) u.y])).trans_eq ?_; change _=K*pollS F₀ Y*( C' (z• f x') + orbitCost F₀*C' (z• f x)); unfold C'; rw[Size.smul,Size.smul]; unfold K z x' f; ring
    change C' (t x'- k (t x))≤ _; rw[show t x'-k (t x)=(t x'-A.symm (k (y x)))+(A.symm (k (y x))- k (A.symm (y x))) from by rw [show t x= A.symm (y x) from qUses ..]; abel]; exact (Size.add ..).trans (add_le_add hh (P.motionAt g u hp _ _))
-- real exact unneeded (coherence rests on limit). Any desired accuracy.
end YM.SignedWilsonExpansion.Purchases
