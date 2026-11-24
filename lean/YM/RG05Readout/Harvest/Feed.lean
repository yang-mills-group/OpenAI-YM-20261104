import YM.RG05Readout.Harvest.Fulfil
/-! Bouquet atom-by-atom reconstruction for the AUTHENTIC composite.
 Proof-specific Costs. Piece depends on root stencil presentation but key
 identity at cutoff independent.Polygon.Any. Norm linear.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Harvest
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Shadow Flatten Nuclear Halls Pulse
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {j b k l ℓ t:ℕ}{e Q x r a a' M:ℝ}(h:C.Makes)
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "A!"=> C.S.a
local notation "Λ"=> C.S.toDepth
local notation "F₁"=> Site (C.side (n+1) p)
variable {D:Address.Rail C}{V I:Type}[DecidableEq V][Fintype V]{P: Address.Sight C d p}{S: Address.Emblems C d} (hm: n+1 < m)(hv:b ≤ n)(hN:m ≤ N)(ht:j ≤ b)
local notation "h₁"=>hm.le.trans hN
local notation "h₂"=> n.le_succ.trans hm.le
local notation "Xo"=> V → F₁
local notation "F!"=> Fintype.card (Color V)
local notation "J"=> Bin G (C.side N p)
local notation "L"=> (Λ ht p)
local notation "Ω"=> Grip C p N n m b d j hm hv hN ht S
variable {B:ℕ→ℕ→ℝ}(hw: Awake D B b d)
lemma Grip.all_sum (Z:Finset I)(F:I→ J)(M:I→ Palette C d)(x y z:I→ ℝ) (hZ:∀ i∈Z, Ω (F i) (M i) (x i) (y i) (z i))(h:C.Makes)(hw:Awake D B b d): Ω (∑ i∈Z,F i) (∑ i∈Z,M i) (∑ i∈Z,x i) (∑ i∈Z,y i) (∑ i∈Z,z i):=by
    induction Z using Finset.induction with
    | empty=> simp_rw [Finset.sum_empty]; exact Grip.free ..
    | insert i Z hi ih=> simp_rw [Finset.sum_insert hi]; exact (hZ i (Finset.mem_insert_self ..)).plus h hm hv hN ht _ hw (ih fun i' h' => hZ i' (Finset.mem_insert_of_mem h'))
variable {ψ:ℕ→ℕ}{w:Worth}(Yc:OPE.Package C w ψ D)(hC:Storage C D)(hS:Cater C D) (s:V→ℕ) (x:(i:V)→Palette C (s i)) (A:(i:V)→Sight C (s i) p)(U:(i:V)→ Emblems C (s i)) (hp:∀ i:V,size (x i)≤ Q)(hQ:0 < Q)
variable (h'A :∀ i:V,Spine D B h (n+1) p (s i) N (A i) (U i))
    (hU:Spine D B h b p d N P S)(hg:d+3 ≤ C.path.levels.clock.J n)(hX:16*(1+t+Scope C ℓ) ≤ (C.S.toDepth ht p).count.val)(h_Open:Stock.Tabs.opens C.path.levels (bumper (2*t)) j b)(hPin: ∀ i,b≤ i→Pin C i d)
local notation "a!"=> tender C m n d ℓ k (F!) Q
local notation "e!"=> copperE C m n d ℓ k (F!) Q
local notation "q!"=> copperH C m n d ℓ k (F!) Q
local notation "τ"=> thresholdC C q! j b n d
local notation "f₁"=> fun i:V=>Many.point (U i) (x i) m N
variable (u: V→Site (C.side (n+1) p))
local notation "γ"=> buy C (n+1) p u
noncomputable def org (C:Family G)(p n N:ℕ)(h:n+1≤N)(s:V→ℕ)(x:(i:V)→Palette C (s i))(u:V→ Site (C.side (n+1) p))(f:E4→Wave V) : Bin G (C.side N p):=fun g X=> ∫ a in Native.box,g.val a * (Pulse.scalp (C:=C) s x u h (f a) X)
local notation "I"=> org C p n N h₁ s (f₁) u
local notation "K"=>Native.box
abbrev Flock (b n m p k d ℓ t:ℕ)(r a:ℝ)(C:Family G)(s:V→ℕ)(u: V→Site (C.side (n+1) p)):Prop:=∀ (f:V→Body), Pulse.buy C (n+1) p u r f → (∀ i:V, Tall (E:=E4) (f i) (s i+2) 1 1)→ Knock b n m p k d ℓ t r a C s (Lattice.lift ∘ u) f
noncomputable def cutoffFee :ℝ:= 1+ volume.real Native.box
variable (H:Flock b n m p k d ℓ t r a C s u)(he:0≤ thresholdC C (copperH C m n d ℓ k (Fintype.card (Color V)) Q) j b n d)(he':0≤ tender C m n d ℓ k (Fintype.card (Color V)) Q)
include hp hQ h hX h_Open hC Yc hS hPin H hw hg h'A hU he he'
local notation "t'"=>cutoffFee
noncomputable def in_through (a:ℝ):= t'*a
local notation "C!"=> printing C b n m d ℓ k (F!) (hv.trans (h₂)) Q (B d b)
lemma feeds (F:E4 → Wave V) (b':ℝ) (hF:Bouquet s Native.box (γ r) F b'):
    ∃ M:Palette C d, Ω (I F) M (in_through b'* a!) (in_through b'* τ) (in_through b'*C!) ∧ ∀ g:Body, ∀ X₀:Config G (C.side N p), IntegrableOn (fun a=>g.val a*(Pulse.scalp (C:=C) s (f₁) u h₁ (F a) X₀)) Native.box:=by
    let K₀:= Pulse.scalp (C:=C) s (f₁) u h₁; let I':= I; have hR:0<t':=add_pos_of_pos_of_nonneg zero_lt_one ENNReal.toReal_nonneg
    induction hF with
    | empty=>
       refine ⟨0,?_,fun g Q=>?_⟩
       · change Ω (I' 0) 0 _ _ _; rw [show I' 0=0 from ?_]; · simp only [in_through,mul_zero, zero_mul]; exact Grip.free ..
         unfold I' org; funext g i; simp
       simp_rw [Pi.zero_apply,map_zero,Pi.zero_apply,mul_zero]; exact integrableOn_zero
    | bloom f a t₁' htP hu hv' hF hx' =>
       let p':ℝ:= t'*t₁'; let z:Goods G (C.side N p):= bunchG (C:=C) (N:=N) u s f f₁ -- edit
       let pX:= voicePulse a htP
       have hP:Priced d pX p':=by
           intro x h hx; have h':volume.real (K) ≤ t':=le_add_of_nonneg_left zero_le_one; exact (voice_cost a htP hu d x h hx).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h' hv') hx.nonneg)
       let Y(a:E4 →ℂ)(i:E4):= a i • joint Finset.univ f
       have hp'(g:Body)(i:Config G (C.side N p))(j:E4): g.val j*(K₀ (Y a j) i)= g.val j*a j * z i:=by unfold Y; rw [map_smul,show K₀ (joint Finset.univ f)=z from carving ..];rw [Pi.smul_apply,smul_eq_mul,mul_assoc]
       have hπ(g:Body): I' (Y a) g=pX g • z:=by
           funext i; change (∫ j in K,g.val j*(K₀ (Y a j) i))=_; simp_rw [hp' g i,integral_mul_const]; rfl
       have hω(g:Body)(X): IntegrableOn (fun v=>g.val v*(K₀ (Y a v) X)) (K):=by
            simp_rw [hp']; exact ((body_smooth g 1|>.continuous.continuousOn).mul htP|>.mul continuousOn_const|>.integrableOn_compact Pert.Cellular.cells_compact)
       by_cases ht': t₁'=0
       · subst t₁'; refine ⟨0,?_ ,hω⟩; change Ω (I' (Y a)) 0 _ _ _; have hV:I' (Y a)=0:=by funext g; rw [hπ]; obtain ⟨x,hx,h'⟩:=Cap.cost g (d+2); have hm₀:= hP g x h';simp only [p',mul_zero,zero_mul,norm_le_zero_iff] at hm₀; rw [hm₀,zero_smul];rfl -- maybe
         rw [hV]; simp only [in_through,mul_zero,zero_mul]; exact Grip.free ..
       let f':= (p':ℂ); have hr:0<p':=mul_pos hR (lt_of_le_of_ne hv' (Ne.symm ht')); have heV: f' ≠ 0:=by unfold f'; exact_mod_cast hr.ne'
       have hc : ‖f'‖=p':=by unfold f'; simp only [Complex.norm_real, Real.norm_of_nonneg hr.le];
       let T₁:= f'⁻¹ • pX; have hT: Priced d T₁ 1:=by
           intro x h hx; have hg:= hP x h hx; unfold T₁; rw [LinearMap.smul_apply,norm_smul,norm_inv,hc]; exact le_trans (mul_le_mul_of_nonneg_left hg (by positivity)) (le_of_eq (by rw [← mul_assoc, inv_mul_cancel₀ hr.ne']))
       let z' := bunchG (C:=C) (N:=N) (fun i=> Lattice.wrap (C.side (n+1) p) ((Lattice.lift ∘ u) i)) s f f₁; have hz:z'=z:=by unfold z' z; simp only [Function.comp_apply, wrap_lift]
       obtain ⟨M,hM⟩:= spawned h hm hv hN ht hw Yc hC hS s (Lattice.lift ∘ u) f (H f hx' hF) x A U T₁ hT hp hQ h'A hU hg hX h_Open hPin -- var shadows
       have hM:=hM.scales hm hv hN ht _ hw f'
       refine ⟨f' • M,?_, hω⟩
       have hx: I' (Y a) = f' • (fun φ:Body=> T₁ φ • z'):=by
          funext g; rw [hπ,Pi.smul_apply,hz]; change pX g • z=f' • (((f')⁻¹*(pX g)) • z); rw [mul_smul,smul_inv_smul₀ heV]
       change Ω (I' (Y a)) (f' • M) _ _ _; rw [hx,show in_through t₁'=‖f'‖ from hc.symm]; exact hM
    | @add F G' p' q hu hb' IH IK =>
       obtain ⟨T',hs,hL⟩:=IH; obtain ⟨W₀,hK,hV⟩:=IK; have hp':I' (F+G')=I' F+I' G':=by
           funext g i; change (∫ j in K,g.val j* (K₀ ((F+G') j) i))= _; simp_rw [Pi.add_apply,map_add,Pi.add_apply,mul_add]; rw [integral_add (hL g i) (hV g i)];rfl
       refine ⟨T'+W₀,?_,fun g X₁=>?_⟩; · change Ω (I' (F+G')) _ _ _ _; rw [hp']; simp only [in_through, mul_add,add_mul]; exact Grip.plus h hm hv hN ht _ hs hw hK
       simp_rw [Pi.add_apply,map_add,Pi.add_apply,mul_add]; exact (hL g X₁).add (hV g X₁)
    | permit hU hx hp IK =>
       rename_i F G' p' q; obtain ⟨M,hM,hX⟩:= IK
       have hf:G' =ᶠ[ae (volume.restrict (K))] F :=by filter_upwards [ae_restrict_mem Pert.Cellular.cells_compact.measurableSet] with i hi using (hx hi).symm
       refine ⟨M,?_,fun x q=> ?_⟩
       · change Ω (I' G') M _ _ _; rw [show I' G'=I' F from funext fun x=> funext fun q=> integral_congr_ae ((hf).mono (fun i hi => (show x.val i*(K₀ (G' i) q)=_ from congr_arg (fun w=> x.val i* (K₀ w q)) hi)))]
         apply Grip.grow _ _ _ _ _ hM; · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hR.le) he'
         · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hR.le) he
         exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hR.le) (show 0≤C! from le_max_left ..)
       exact (hX x q).congr ((hf).symm.mono fun i hi=> (show x.val i*(K₀ (F i) q) = x.val i*(K₀ (G' i) q) from by rw [hi]))
end YM.RG05Readout.Harvest
