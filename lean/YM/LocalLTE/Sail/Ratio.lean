import YM.LocalLTE.Sail.Goals
import YM.MergeProof.Maid
/-!
# Analytic error after conditional (mark / vacuum) read-out

At good: price report e in the actual `Tab` and marker derivative currencies, t in units.
*/
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Sail
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext.Repeat LocalLTE
open Next.Foundations YM.MergeProof Motion Marker Accent
open Planned.GuardedAtom
open MeasureTheory Finset Push.Local Overlay
open PhysicalNext.Repeat.Legato.Bandage.Harmonics
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n:Side}{P:RG.Rep G n}
section canon
-- take Caps.P not necessarily forecast origin; permits shifted comparison on DIFFERENCE.
variable {k e Q :ℝ} {P P': Coefficient ((Labels.frames G).level 0) n}
-- stencil cost carried earlier. here applies to same.Support.
variable {F:Type*}
end canon
section
variable {d₀:ℕ}{F:Labels.Frame G d₀}(A:SectionData F)
variable {v θ t Γ k :ℝ}{D:Hol G}{i:Site n}
variable {P' Q':Coefficient F n}
-- sum of source local fields MUST retain analytic tag masks. don't drop when taking probe.
private lemma summableE {R:Coefficient F n} (U:Config G n)(h:R.remBound i P k v): Summable fun j=> R.maskedTerm P j U:=by
    obtain ⟨a,b,hz,hB,he,hr,⟨s,hs,hp⟩,hx⟩:= h
    have hf : Summable s:= hs.2.1.of_nonneg_of_le (fun i=> (hp i).1) (fun j=> P.p.loMass _ _ (hp j).1)
    refine hf.of_norm_bounded (fun j=>?_); by_cases h:Healthy P.p.threshold (R.support j) U
    · unfold Coefficient.maskedTerm; rw [masked_eq _ _ _ _ h]; exact (hp j).2 U h [] (by simp) (by simp)
    unfold Coefficient.maskedTerm; rw [masked_ne _ _ _ _ h,norm_zero]; exact (hp j).1
variable (h: FrameReport P i P' Q' D k Γ)(he:P'.remBound i P k θ) (hB:∀ j:F.Index, P.p.Regular (A.footprint i) (A.places (Pi.single j 1) i) ∧ P.p.supBounds i (A.footprint i) (A.places (Pi.single j 1) i) (v* P.p.threshold^(F.grades j).2))
variable (U:Config G n)
include h he hB
lemma readPrice (hv:v≥1)(hζ:k≤1): ‖P'.exponentialEntry i A P U - Q'.exponentialEntry i A P U‖ ≤ (3+v)*Γ:=by
    let K:= Vinca.decrement P' Q'; have hf:= summableE U he; have hk:= summableE U (R:=K) (h.earns.bound le_rfl)
    have hh j : K.maskedTerm P j U=P'.maskedTerm P j U-Q'.maskedTerm P j U:=by
       change masked _ (P'.support j) (P'.regular j-Q'.regular j) U = _ ; unfold Coefficient.maskedTerm; rw [h.alignment]; by_cases he:Healthy P.p.threshold (Q'.support j) U
       · rw [masked_eq _ _ _ _ he, masked_eq _ _ _ _ he,masked_eq _ _ _ _ he]; rfl
       rw [masked_ne _ _ _ _ he, masked_ne _ _ _ _ he,masked_ne _ _ _ _ he,sub_zero]
    have ht: Summable (fun j=> Q'.maskedTerm P j U):= (hf.sub hk).congr (fun i=>by rw [hh,sub_sub_cancel])
    have hz: K.exponentialEntry i A P U=P'.exponentialEntry i A P U-Q'.exponentialEntry i A P U:=by
       change Extra.Histories.part A i P U (P'.x-Q'.x)+ ∑' j,K.maskedTerm P j U=(Extra.Histories.part A i _ U _+_)-(Extra.Histories.part A i _ U _+_)
       rw [map_sub]; simp_rw [hh]; rw [hf.tsum_sub ht]; abel
    rw [← hz]; refine (Accent.hull A P i K U hB (h.earns.bound le_rfl) hζ (zero_le_one.trans hv)).trans (?_)
    apply (add_le_add_left (mul_le_mul_of_nonneg_left h.monte (add_nonneg zero_le_one (zero_le_one.trans hv))) _).trans
    exact le_of_eq (by ring)
end
section panel
variable {V:Type}[DecidableEq V][Fintype V] (Z:Census V)(O:Appendix Z P)(F F':V→ Config G n→ℂ)(w:V→ℝ) (o:V→Site n)
noncomputable def receipt (U:Config G n):Poly Z:= Mach Z (fun v=>F v U)+ O.truth.extra U
noncomputable def forecast (U:Config G n):Poly Z:= Mach Z (fun v=>F' v U)+ O.model.extra U
variable (R: V→ℕ→ Config G n→ℂ)(X:Config G n→ Poly Z)
    (hp:Appendix.Prepared Z P O o F R X)(U:Config G n)
local notation "P'"=> receipt Z O F U
local notation "M"=> forecast Z O F' U
local notation "PR"=> Marker.Poly
include hp
-- For passing, all K apart from empty occupancy read as zero. Covers act.Support. No claim off.
lemma allclear (h:flags P.p.threshold U=∅): let y:= P.eval U; 0 <y ∧ y⁻¹ • X U=Marker.Poly.pass (receipt Z O F U):=by
    intro y; let a:= Real.exp (P.exponent U); have he':y=a:=by unfold y Rep.eval; rw [Activities.gas_one _ _ h,mul_one]
    rw [he',hp.density]; let z':= P.p.threshold; let p:=P.activities
    let κ(i:Box n):= bar P.activities Z U i+Mach Z (fun j=>profile P.activities (R j) i U)+O.K i U
    have hh i : i.2=∅→κ i=0:=by
       intro he; letI : IsEmpty {k // barcode P.activities k=i}:= ⟨fun j=> (P.activities.forced j.val).inventory_ne.ne_empty ((congr_arg Prod.snd j.property).trans he)⟩
       have hp'(f:ℕ→ Config G n→ℂ): profile P.activities f i U=0:=tsum_empty -- need syntax
       unfold κ bar; rw [hp', map_zero]; simp_rw [hp',Mach, Marker.Poly.send_zero,sum_const_zero,add_zero,zero_add]; exact Classical.byContradiction (fun hv=> ((hp.plate.flag i|>.1).permits U hv).2.1.ne_empty he)
    have hV: Accent.field κ (RG.flags P.p.threshold U)=1:=by
       rw [h]; unfold Accent.field; rw [Finset.sum_eq_single ∅]; unfold grid; rw [if_pos ?_,Finset.prod_empty]
       · refine ⟨fun _ h=> ?_, Finset.biUnion_empty⟩; exact (Finset.notMem_empty _ h|>.elim)
       · intro j _ hj; unfold grid; split
         next ht=>
           obtain ⟨a,ha⟩:= Finset.nonempty_iff_ne_empty.mpr hj; exact prod_eq_zero ha (hh a (le_antisymm (ht.2 ▸ Finset.subset_biUnion_of_mem Prod.snd ha) (Finset.empty_subset _)))
         rfl
       simp
    unfold receipt Bands.extra; simp only [hp.bank, Pi.zero_apply,Marker.Poly.send_zero, Finset.sum_const_zero, zero_add, hp.headings]; refine ⟨Real.exp_pos _,?_⟩
    unfold restore; rw [hV,mul_one]; change a⁻¹ • (a • Poly.pass (Mach Z (fun i=>F i U)+ ∑ i,O.H i U)) = _; rw [inv_smul_smul₀ (Real.exp_pos _).ne']
omit hp
omit [Fintype V] in
private lemma price_below {r:V→ℝ}(h:∀ i,0<w i)(ht:∀ i,w i ≤ r i)(x:Poly Z): Poly.price w x ≤ Poly.price r x:=by
    apply Finset.sum_le_sum; intro i hi; exact mul_le_mul_of_nonneg_right (prod_le_prod (fun p _=> (h _).le) (fun p _=>ht _)) (norm_nonneg _)
noncomputable def margin (k :ℕ):ℝ:= Real.exp (3*k)*(∑ i∈Finset.range (k+1),‖((i.factorial:ℂ)⁻¹)‖*(k:ℝ)^i)
-- Emit θ intermediate. q.model stamp derivatives separate.Exception.B
include hp
variable {a b c k e t Γ A b' :ℝ}{N:ℕ}
lemma comparisonPrice (he:0 ≤ Γ)(ht:Γ ≤ 1/2)(hx:a≤1)(hh: Appendix.Budget Z P O w a b c t k)(hc:Appendix.Budget Z P O (fun _=>1) A Γ Γ b' k) (hr:∀ i,w i ≤1) (hN':Fintype.card V ≤ N)
     (hu:∀ i,w i* ‖F i U‖≤1)(hV:∀ i,w i* ‖F i U-F' i U‖≤ Γ):
        (P').part Z.quiet=0 ∧ (M).part Z.quiet=0 ∧ Marker.Poly.price w (P'-M) ≤ N*(2*Γ) ∧ Marker.Poly.price w (Poly.pass P'-Poly.pass M) ≤ margin N*(2*Γ):=by
    let H:= P'; let E:=M; let v:=H-E; let pv:Poly Z→ℝ:= Poly.price w
    have hw:= hh.trueB.pure; have hP:H.part Z.quiet=0:=by unfold H Sail.receipt; rw [Poly.part_plus,mute,Port.tones w U hp.entire hh.trueB,add_zero]
    have hE:E.part Z.quiet=0:=by unfold E Sail.forecast; rw [Poly.part_plus,mute,Port.tones w U hp.shelf hh.cope,add_zero]
    have hv:v.part Z.quiet=0:=by unfold v; rw [Extra.Trajectories.part_sub,hP,hE,sub_zero]
    have hrw:0 ≤ 2*Γ:=mul_nonneg zero_le_two he; let z:ℝ:=N; have hz:0≤z:=Nat.cast_nonneg _; have hN:(Fintype.card V:ℝ) ≤ z:= Nat.cast_le.mpr hN'
    have hxT(f:V→ℂ){t:ℝ} (hp:0≤t)(h:∀ i,w i*‖f i‖ ≤ t): pv (Mach Z f) ≤ N*t:= by refine (Poly.batch hw _ _).trans (?_); simp_rw [Poly.solo,Poly.solo_toll]; exact (sum_le_sum (fun i _=>h i)).trans ((Eq.trans_le (by rw [sum_const, Finset.card_univ,nsmul_eq_mul]) (mul_le_mul_of_nonneg_right hN hp)))
    let q:= O.remainder.extra U
    have hd : pv v≤ N*(2*Γ):=by
        unfold v H E receipt forecast
        rw [Port.extraEqual O.truth O.model O.remainder (fun _=>1) U hp.shelf hp.printed hc.cope hc.rented hp.trial]
        let f:= Mach Z fun i=> F i U; let f':=Mach Z fun i=> F' i U; rw [show f+(O.model.extra U+q)-(f'+O.model.extra U)= (f-f')+q from by abel] -- placeholders _
        have hK: Marker.Poly.price (fun _=>1) q ≤ N*Γ:=by simpa only [zero_add] using ((O.remainder.bulkBound hp.printed hc.rented U|>.2).trans (by rw [zero_add]; exact mul_le_mul_of_nonneg_right hN he)) -- edit lin
        have hV' : pv (f-f')≤ N*Γ:=by
           have hv:f-f'=Mach Z (fun i=> F i U-F' i U):=by unfold f f' Mach; rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun i hi=> ?_); ext k; simp only [Extra.Trajectories.part_sub, Poly.part_send]; split <;>ring
           rw [hv]; exact hxT _ he hV
        refine (Poly.addition hw _ q).trans ((add_le_add hV' ((price_below Z w hw hr _).trans hK)).trans_eq (?_)); ring
    refine ⟨hP,hE,hd,?_⟩
    change pv (Poly.pass H-Poly.pass E) ≤ _
    have hxH : pv H ≤ 2*z:=by
        have hX:= (O.truth.bulkBound hp.entire hh.trueB U).2; unfold H receipt
        refine (Poly.addition hw _ _).trans ((add_le_add (hxT _ zero_le_one hu) (le_trans (c:=z) hX ?_)).trans_eq (?_)); rotate_left
        · unfold z; ring
        rw [zero_add]; exact (mul_le_mul_of_nonneg_left hx (by positivity)).trans (by rw [mul_one]; exact hN)
    have hv0: pv E ≤ 3*z:=by
        have heE:E=H+(-1:ℂ) • v:=by unfold v; simp
        have h0 : 2*Γ ≤ 1:=by linarith only [ht]
        nth_rw 1 [heE]; refine (Poly.addition hw H _).trans ?_; unfold pv at hxH hd; rw [Poly.adapted,norm_neg,norm_one,one_mul]; have hh:Poly.price w v≤ z:= hd.trans ((mul_le_of_le_one_right hz h0)); linarith only [hxH,hh]
    have hD: Poly.pass H = Poly.pass E * Poly.pass v:=by 
         conv_lhs => rw [show H= E+v from (show E+v=H from add_sub_cancel ..).symm]
         rw [Extra.Trajectories.pass_add hE hv]
    rw [hD,show Poly.pass E*Poly.pass v-Poly.pass E= Poly.pass E*(Poly.pass v-1) from by ring]
    unfold margin; rw [mul_assoc (Real.exp _)]; refine (Poly.multiplication hw _ _).trans (mul_le_mul ((Poly.pass_budget hw _).trans (Real.exp_monotone hv0)) (?_) (Poly.nonnegative hw _) (Real.exp_nonneg _)); refine Port.outbound _ hw v hN' hd hrw (by linarith only [ht]) -- hN' shadow
end panel
end YM.LocalLTE.Sail
