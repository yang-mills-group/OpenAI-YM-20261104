import YM.OPE.Compatible.Pendulum.Profit
/-!
# Full matched budgets. Only aperture constraints on shifted readout.

Applies pointwise without identifying exteriors or placements. Each rootTest signed balance carries the purchased gain **once per block in the full signed array**, not just in the vac marginal. The lifted projection steps still needed to use ore.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Pixel
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave Relay Cells CutOrder Arcade
open scoped Topology BigOperators Classical
variable {X I : Type} [PartialOrder X][OrderBot X][Fintype X](D:Origin X){U F K:Finset X}
    {G:Gauge}{C:Family G}{L:Extraction.Order}(A:Allot C){W d e k n J J' K' b l':ℕ}{η M:ℝ}
set_option quotPrecheck false
variable (hG:G.Simple)(hC:C.Makes) {φ:Filter I}{s:I→X→ℝ}{T r:I→ℝ}{o:X}
    (h: Glowing D U φ T s η)(p:brim D U→ C.book.Token)(ho:o∈U){S:Table C.book}
local notation "t"=>fun i=>schedule C b η (s i)
local notation "K!"=>fun i=>scopeTick D C b l' η (T i) (s i)
local notation "j"=>fun i=>aperture D C b l' η (T i) (s i)
local notation "u"=>fun i=>t i o-1
local notation "s!"=>fun i=> t i ⊥-1
local notation "I'"=>brim D U
local notation "w"=>fun x:I'=>(p x).2
local notation "v!"=>fun x:I'=>(p x).1
local notation "Γ"=>cove D U o
local notation "H!"=>places X+Fintype.card (C.labels.level d).Index
local notation "P!"=>fun i=>area D v! (s i) Γ/s i o^d
local notation "U'"=>fun i=>volume D U v! (s i) * (s i (par D o)/s i o)^d
local notation "V!"=>fun i=>volume D U v! (s i) * (s i (par D o)/s i o)^d / (s i ⊥)^e
include h A hC hG ho
set_option maxHeartbeats 200000 in
lemma deposit (hI:Inward C L S)(hp:M ≥ 0)(ho':o≠⊥)(hb:1 ≤ b)(he:d ≤ b)
    (hJ : Stock.Tabs.opens C.path.levels 1 J J')(hK : Stock.Tabs.opens C.path.levels 1 J K')(hk:C.ref d ≤ J')(hk':C.ref e ≤ K') :
    ∃ x y z r:I→ℝ,Round φ T (fun i=> x i*(P! i))∧ Round φ T (fun i=> y i*(P! i))∧ Round φ T (fun i=>z i*(V! i))∧ Round φ T (fun i=> r i*(V! i))∧ ∀ᶠ i in φ,
     whenHigh U (t i)= t i o → (j i o)≤ u i → ∀ W:ℕ,∀ a:X→ Cover, Ridge (s i) η M D U (C.S.gridPoint W ∘ a)→ a ⊥=0 →(∀ x∈ allUp D U,j i x≤ W∧ ∃ z:Cover,C.S.gridPoint W (a x)= C.S.gridPoint (j i x) z)→
     ∃ g:∀ y:I', C.label ((p y).1), (∀ y:I', S.project _ (g y)=S.project _ (p y).2)∧ ∃ q t', TokenMine D C L U (fun y:I'=>⟨(p y).1,g y⟩) o a W J (u i) (s! i) d e q t' (x i) (y i) (z i) (r i):=by
    obtain ⟨M',hL⟩:= exists_nat_ge (8*M/η+2); let H:= canopy_wave D hG A h b l' J hp M' hL
    have hx(a:I') : a.val∈allUp D U:= Finset.mem_union_right _ a.2; have ht(a:I'):= climb D hG A h b l' (v:=a.val) (hx a)|>.1
    obtain ⟨t',hT'⟩:= hI.crew v! w (q:=fun (x:I') i=>j i x.val) (l:=φ) (fun x=>tendsto_atTop_mono (fun i=> Nat.le_succ _) (ht x)); let a(i:I)(x:I'):= PhysicalNext.Repeat.Legato.Bandage.fly C.path.levels ((p x).1) (j i x.val) * C.S.a (j i x.val)^((p x).1)/(2*β C (j i x.val)^t' x)
    have hA(x:I') : Round φ T (fun i=>a i x / s i (par D x.val)^(p x).1):=by
       let d':=(p x).1; obtain ⟨hK',hR⟩:=arrive D hG A h b l' (v:=x.val) (hx _); let u' i:=β C (j i x.val)
       have he:Round φ T (fun i=> PhysicalNext.Repeat.Legato.Bandage.fly C.path.levels d' (j i x.val)) := (hK'.power (MergeProof.winter G d') h.ray).inv; refine ((he.mul (hR.power d' h.ray)).div ((Round.const zero_lt_two h.ray).mul (hK'.power (t' x) h.ray))).adjust ?_
       filter_upwards with i; unfold a; rw [div_pow]; ring
    have ha(i)(y:I'):0 < a i y:=by
       let m:= j i y.val; let d':=(p y).1; let f:=β C m; have hh:0<f:=β_pos ..; unfold a; rw [fly_eq]; change (f^_)⁻¹ * C.S.a m^d' /(2*f^_)>0; exact div_pos (mul_pos (inv_pos.mpr (pow_pos hh _)) (pow_pos (C.S.a_pos _) _)) (by positivity)
    obtain ⟨hr,h',hr'⟩:= gleans D A hG b h ho; obtain ⟨a',c,hα,hc,hc'⟩:= taxes_pay D A hG b l' M' h (show 0<H! from (places_pos X).trans_le (Nat.le_add_right ..)) hr h'
    let g(i:I)(x:I'):= Run.Below C.path (a i x) (j i x.val) (finishAt D (t i) x.val); let z i:=event_fee H! (c i)*∏ y∈ Γ,g i y
    let k' i:=u i; let x i:= area D v! (s i) Γ
    have hV:Round φ T (fun i=> z i / x i):=by
        refine ((hc.power (H!+1) h.ray).mul (area_pay D A hG b l' h v! hA Γ)).adjust ?_
        filter_upwards with i; change c i ^(H!+1)* (_/x i)=z i/x i; unfold z; rw [← mul_div_assoc]; rfl
    have hs₀:∀ᶠ i in φ,0 < x i:= area_pos D h v! Γ
    have hz₀:=purse_self hV hs₀
    obtain ⟨r,hr₀,hE⟩:= exchanged_at A hG k' d hr h.ray h' hV hc hs₀
    let Q i:= purse D C o (t i) (j i) U d (k' i) H! (r i) (a' i) (c i) (g i); let F i:=t i; let Y i:=volume D U v! (s i)*(s i (par D o)/s i o)^d
    have hu : ∀ᶠ i in φ,0 < Y i:=by
        have hy:par D o∈U:= h.crowned.roots (par_le D o) ho; filter_upwards [(h.fade _ hy).eventually self_mem_nhdsWithin,(h.fade _ ho).eventually self_mem_nhdsWithin,area_pos D h v! univ] with i hi hw ha; exact mul_pos ha (pow_pos (div_pos hi hw) _)
    have hQ:Round φ T (fun i=> Q i/Y i):= purse_fund D A hG b l' h o ho v! hA hα hc hr₀; have hR:=purse_self hQ hu; obtain ⟨hσ,hT₁,hΓ,hΦ⟩:= prev_info D hG A h b
    refine ⟨_,_,_,_, weighted (Q:=x) A hG h.ray hr hr' h' hV hs₀ d,weighted_stakes (Q:=x) h.ray hr' hr₀ hs₀ J' J,weighted (Q:=Y) A hG h.ray hT₁ hΦ hΓ hQ hu e,weighted_rebate (J:=J) (Q:=Y) A hG h.ray hT₁ hΦ hΓ hQ hu hk',?_⟩
    obtain ⟨W₁,hW⟩:= eventually_atTop.1 (A.bottoms.eventually_ge_atTop (2*H!)); have hj:=lives D hG A h b h.crowned.base; have hv:=lives D hG A h b ho; have hu':o∈allUp D U:=mem_union_left _ ho; have hv':=h.crowned.base
    have hW₀ : ∀ᶠ i in φ,16*(M*s i ⊥)≤ C.S.a J:= (show Tendsto (fun i=>16*(M*s i ⊥)) φ (𝓝 0) from by simpa using ((h.fade _ hv').mono_right nhdsWithin_le_nhds|>.const_mul M|>.const_mul 16)).eventually (ge_mem_nhds (C.S.a_pos _))
    filter_upwards [hσ,hv.eventually_gt_atTop 0,H,hW₀,hT₁.eventually_ge_atTop K', hT₁.eventually (Push.GridApprox.plenty C.path.levels J (lensScope C e)),hT',hj.eventually_ge_atTop W₁,(eventually_all.mpr fun i:I'=> (ht i).eventually_ge_atTop (C.ref (v! i))),hr.eventually_gt_atTop J',hc',hE,hz₀,hR,(climb D hG A h b l' hu').1.eventually_ge_atTop (C.ref d),series_angle D hG A h b] with i hi hω hA' hW' ht₀ hΩ hL' he' hV₀ hJ' hζ hE' hz hpQ hψ hH hS hj₀ W' B hB hY' hK₀
    have hδ: k' i+1=F i o:= Nat.sub_add_cancel hω; have hK':finishAt D (F i) o < j i o:= Nat.lt_succ_of_le (le_max_left ..); have hF: F i ⊥ ≤ finishAt D (F i) o:= lower_earliest D U _ hH o hu'
    have he₀ : F i ⊥ < k' i:= hF.trans_lt (hK'.trans_le hj₀)
    let F':= clip (F i) U (k' i+1); let Q':=clip (F i) F' (k' i); have hp₀ : Wave (F i) U F' (k' i+1):= cut hH (he₀.trans (Nat.lt_succ_self _)) (le_trans hS.le hδ.symm.le)
    have hV' : Wave (F i) F' Q' (k' i):= cut hp₀.after he₀ (Nat.le_of_lt_succ hp₀.lower)
    have hu'':o∉F':=fun he=> lt_irrefl _ ((mem_filter.mp he).2|>.trans_le hδ.le); have hf:par D o∈F':= mem_filter.mpr ⟨h.crowned.roots (par_le D o) ho,(hK'.trans_le hj₀).trans_le (Nat.le_succ _)⟩; have hx₀:o∈brim D F':=(on_brim ..).mpr ⟨hu'',ho',hf⟩; have hV': Wave (F i) F' Q' (k' i):=hV'
    let v₀:brim D Q':=⟨o,(on_brim ..).mpr ⟨fun hp=> hu'' (hV'.next hp),ho',mem_filter.mpr ⟨hf,hK'.trans_le hj₀⟩⟩⟩
    obtain ⟨f,hχ,hγ,p',hp',hc⟩:= hL' L.fuse (by infer_instance) le_rfl; let v' (x:I') : C.book.Token:= ⟨v! x,p' x⟩; refine ⟨p',hp',?_⟩
    have hY(y:X)(hy:y∈allUp D U):8*‖C.S.gridPoint W' (B y-B v₀.val)‖≤ C.S.a J:=by
        let p'' i:=C.S.gridPoint W' (B i); have hz(x:X)(hx:x∈allUp D U): ‖p'' x‖ ≤ M*s i ⊥:=by
            have ht:=hB.near ⊥ x hv' hx bot_le; rw [hB.belly,zero_sub,norm_neg] at ht; exact ht
        rw [← grid_diff]; change 8*‖p'' y-p'' o‖ ≤ _; linarith only [norm_sub_le (p'' y) (p'' o),hz y hy,hz o hu',hW']
    have hf(k:ℕ)(ht : F i ⊥ ≤ k): 2*H! ≤ A.r k:= hW k (he'.trans ht)
    have h0: Q i ≤ a' i^(Q'.card*(places X+places X))* (Run.Below C.path ((lantern C.path (r i) d (k' i) (j i v₀.val))/2) (j i v₀.val) (finishAt D (F i) v₀.val)*(∏ a∈ univ.erase v₀,feedS D hV' (feedS D hp₀ (g i) H! (c i)) H! (c i) a)):=exchange_fee D hp₀ hV' v₀ hx₀ hζ.2.1.start hζ.2.2.2 hζ.1.good hζ.2.2.1 hE'.1 (fun x=>Run.below_fee _ (ha i x)|>.le)
    have hθ:z i=feedS D hp₀ (g i) H! (c i) ⟨o,hx₀⟩:=by unfold feedS; rw [elements_bunch]
    refine ore_won (F:=Q') D hp₀ hV' v₀ hx₀ ho v' (a i) (hA' B W' hB hY' hK₀) hδ.symm hj₀ hY hC hG ((show C.ref d≤ scopeTick D C b l' η (T i) (s i) o from hψ).trans_lt (Nat.lt_succ_self _)) hb he (fun k ht=>hf _ (he₀.le.trans ht)) hζ.2.1 (ha _) (s':=fun x=>K! i x) (fun x=>⟨hV₀ x,rfl⟩) hz hθ.le hJ (by assumption) hi.symm ht₀ hJ' hk hk' hE'.1 hE'.2.1 hE'.2.2.1 hE'.2.2.2 hΩ hζ.1 (fun k ht=> le_trans (by omega) (hf _ ht)) hpQ h0 f hχ hγ ?_
    filter_upwards [hc] with q hq x'
    let e':= aperture D C b l' η (T i) (s i) x'.val; let t'':=(p x').1; let r':= (C.S.a e')^t''; let s':= PhysicalNext.Repeat.Legato.Bandage.fly C.path.levels t'' e'
    have hc:0 < r':= pow_pos (C.S.a_pos _) _; have hV:0< s':= inv_pos.mpr (pow_pos (β_pos ..) _); let z':=Next.Rank.Spindle.paid C t'' e' q.1 q.2 (p' x'); let d'':=(β C e')^t' x'; have hp:0< d'':=pow_pos (β_pos ..) _; have hh':z'*r' ≤ d'':=hq x'
    change 2*(s'*r'/(2*d''))*z' ≤ s'; field_simp; linarith only [hh']
end YM.OPE.Arboreal.Pixel
