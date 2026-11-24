import YM.OPE.Compatible.Eyrie.Forest
/-! # Local grant for opacity; instantaneous, work at actual temperature. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Owl
open Function Filter Set MeasureTheory Lattice Laurent RG Pressure Tree Precision Wilson Org RG.Supply Input RG.Shoot
open PhysicalNext PhysicalNext.Repeat Legato Graces Roost PhysicalNext.Repeat.Aroma Pressure ConnectedActivityE6 Shell Channel Push.PriceCompiler Lass Zest Stroke.MatchZ
open Next.Free Woody Votive CardinalQ Stroke Stroke.MatchZ ThroughLaunch Source Next.Foundations Zeph Eyrie
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I :Type} {G : Gauge} {l k n i r:ℕ}{P':Patch}{n:Side}{H:Sponsor G}{T:Seasons H}{θ t u:ℝ}
local notation "Z"=> Labels.frames G
noncomputable abbrev δerror (x:ℝ):ℝ:= Real.exp (-x)
noncomputable def Brisk (r:ℕ)(x:ℝ)(V:Rep G n)(Q:lots G n):Prop:=∀ U:Config G n, ∀ p:lots G n,LocalOn (Push.Mark.Outer r 0) p → Envelope p → ‖πfee Q p‖ ≤ Real.exp (V.exponent U)*δerror x*γfee p
structure Cyan (S:Stage)(θ x:ℝ)(V:Rep G n):Prop where
       lawful:V.Lawful S.width S.paths (capL θ x) (ℰb x) (Ωb x)
       clip : V.clip=S.clip
       TagQ : CardinalQ.Tag S x V.p V.beta
-- Apex appointment. Need Tag V.p enough to uniformly bound all expenses by x,n.Post
lemma equal_tag (S:Stage){V Q:Rep G n}(a:Cyan S θ t V)(h:Cyan S θ t Q):V.p=Q.p:=by
        obtain ⟨hn,hN,hr,hB,hx,hA⟩:= a.TagQ; obtain ⟨hk,hk',hz,hb,hh,hA⟩:=h.TagQ; suffices H : ∀ (p q:BudgetPoint),p.order=q.order→p.B=q.B →p.threshold=q.threshold→p.supportExponent=q.supportExponent→p.power=q.power→p=q from H _ _ (hn.trans hk.symm) (hN.trans hk'.symm) (hr.trans hz.symm) (hB.trans hb.symm) (hx.trans hh.symm)
        rintro ⟨_,_,_,_,_,_⟩ ⟨_,_,_,_,_,_⟩ h1 h2 h3 h4 h5; congr
lemma gusto (S:Stage){x:ℝ}(h:0<x)(θ:ℝ)(n:Side): ∃ b:ℝ,0≤b∧ ∀ P:Rep G n,Cyan S θ x P → ∀ U:Config G n, ‖P.exponent U - rhoE P‖ ≤ b:=by
       by_cases hC:∃ P:Rep G n,Cyan S θ x P; swap; · exact ⟨0,le_rfl,fun P h=>False.elim (hC ⟨P,h⟩)⟩
       obtain ⟨p,hC⟩:=hC; obtain ⟨c,hc⟩:= labor (G:=G) (n:=n) (C:=S.clip) (c:=S.paths) (v:=capL θ x) (σ:=S.width) p.p (2*x)
       let z:= c + ↑(Fintype.card (Site n))*ℰb x; refine ⟨max 0 z, le_max_left ..,fun V he U=>?_⟩
       have hz:V.beta>0:= (half_pos h).trans_le he.TagQ.beta.1; have hp:V.p=p.p:=equal_tag S he hC; have ht:= hc V.path (he.clip ▸ he.lawful.paths) V.beta (by rw [Real.norm_of_nonneg hz.le]; exact he.TagQ.beta.2) U
       rw [←hp,←he.clip] at ht; apply le_trans _ (le_max_right ..); have hY : V.exponent U-rhoE V= -(V.path.inChannels V.clip V.p V.beta U)- V.activities.additive V.p U:=by unfold Rep.exponent rhoE; ring
       rw [hY]; exact (norm_sub_le ..).trans (add_le_add ((norm_neg _).trans_le ht) (Blinds he.lawful.labels.boundE _))
lemma freeze_it (S:Stage){x:ℝ} (h:0<x)(θ:ℝ)(n:Side): ∃ b:ℝ,0<b ∧∀ V:Rep G n, Cyan S θ x V→ ∀ (Q:lots G n)(r:ℕ), Pennant V r b Q→ Brisk r x V Q :=by
       obtain ⟨b,hb,hV⟩:= gusto (G:=G) S h θ n; refine ⟨Real.exp (-b)*δerror x, mul_pos (Real.exp_pos _) (Real.exp_pos _),fun V hv Q r hQ U p ht hk=>?_⟩; have hp:=hV V hv U; apply (hQ _ ht hk).trans; apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun i=> norm_nonneg _); rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _|>.le); rw[← Real.exp_add]; apply Real.exp_monotone; have hh:= (abs_le.mp hp).1; linarith
section Req
variable (A:Stage)(i r l:ℕ)(P:Spells.Pad G)
set_option quotPrecheck false
local notation "S"=>localSection G l
local notation "F"=> (Labels.frames G).level l
-- Point budgets carry the physical density's relation to R, non-lit not positive
structure HillZ (θ x:ℝ)(n:Side) where
       art : (Z).level l|>.Coeff
       norm : ‖art‖ ≤ 2
       path : Rep G n
       gen : Cyan A θ x path
       cost : (F).Coeff→ Coefficient F n
       living : Torch S (hol G) 0 path cost (l+6) (salary x)
       lens : Cab T i A.clip
       valid : Zeph.fitsW lens.ℳ path
       cents : SealK x A S (hol G) _ path cost living
       salaryF:lens.fees=capL θ x
       realm: Continuous ((cost art).density 0 S path)
       outlook: Brisk r x path ((cost art).density 0 S path)
-- Bactual trigger all stores rising
end Req
end YM.OPE.Owl
