import YM.OPE.Compatible.Sear.Loam
/-!
# Conditional formal weights. Grain preservation via Jensen. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cinders
open Function Filter Set MeasureTheory
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {X Y I:Type}{s t c:ℝ}{i j k:ℕ}
open PertExtension Series Libra GaussianScore Jargon
section
variable [MeasurableSpace X][MeasurableSpace Y]{μ:Measure X}{ν:Measure Y}
lemma Fault.alongP (g:Y→ X)(h:MeasurePreserving g ν μ)(f:X→ℝ)(p:Fault μ i f t): Fault ν i (f ∘ g) t:=⟨p.pos,p.strong.comp_measurePreserving h,(eLpNorm_comp_measurePreserving p.strong h).trans_le p.passes⟩
variable [IsProbabilityMeasure μ][IsProbabilityMeasure ν]
noncomputable abbrev nearOp (ν:Measure Y)(f:X×Y→ℝ)(x:X):= ∫ y,f (x,y) ∂ν
private lemma Jicks {p:X→ℝ}(hi:0 < i) (hp:Integrable p μ)(h:Integrable (fun x=>‖p x‖^i) μ): ‖∫ x,p x ∂μ‖^i ≤ ∫ x,‖p x‖^i ∂μ:=by
        let t:= ∫ x,‖p x‖^i ∂μ; let v:=t^(i:ℝ)⁻¹; have he:0 ≤ t:= integral_nonneg fun _=> pow_nonneg (norm_nonneg _) _; have hv : v^i=t:= Real.rpow_inv_natCast_pow he hi.ne'; let H:= Fault.ofInt (f:=p) (t:=v) (Real.rpow_nonneg he _) hi hp.aestronglyMeasurable h hv.symm.le; exact (pow_le_pow_left₀ (norm_nonneg _) (H.pays hi) i).trans_eq hv
lemma Fault.nova (f:X×Y→ℝ)(hi:0 < i)(h:Fault (μ.prod ν) i f t): Fault μ i (nearOp ν f) t:=by
       have hp:= h.rich.integrable (show (1:ℝ≥0∞) ≤ (i:ℝ≥0∞) from mod_cast hi); obtain ⟨hb,hL⟩:= h.rose hi; let u(x:X×Y):= ‖f x‖^i; let v:= nearOp ν f; let p:= nearOp ν u; have he: Integrable p μ:=hb.integral_prod_left; have hv: AEStronglyMeasurable v μ:= hp.integral_prod_left.aestronglyMeasurable; have ht:∀ᵐ x ∂μ, ‖v x‖^i ≤ p x:=by
             filter_upwards [hp.prod_right_ae,hb.prod_right_ae] with x hx hy; exact Jicks hi hx hy
       let b(x:X):= ‖v x‖^i; have hg : Integrable b μ:= he.mono' (hv.norm.pow i) (ht.mono fun x hx=>(Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) i)).trans_le hx); refine Fault.ofInt h.pos hi hv hg ((integral_mono_ae hg he ht).trans ?_); exact (integral_prod u hb).symm.trans_le hL -- orientation
end
section
variable {X Y:I→Type}[∀ i,MeasurableSpace (X i)][∀ i,MeasurableSpace (Y i)] {φ:Filter I}{Z:I→ℝ} {μ:(i:I)→Measure (X i)} {ν:(i:I)→Measure (Y i)}
noncomputable abbrev ProductS (μ:(i:I)→Measure (X i))(ν:(i:I)→Measure (Y i)):=(fun i=> (μ i).prod (ν i))
variable [∀ i, IsProbabilityMeasure (μ i)][∀ i,IsProbabilityMeasure (ν i)]
local notation "Ξ"=> ProductS μ ν
omit [∀ i,IsProbabilityMeasure (μ i)] in lemma Grain.loco {p:PayR X}(h: Grain μ φ Z p t): Grain (ProductS μ ν) φ Z (fun i x=> p i x.1) t:=by intro k hk; obtain ⟨s,hs,H⟩:=h k hk; exact ⟨s,hs,H.mono fun i hi=> hi.alongP Prod.fst measurePreserving_fst _⟩ -- ν instance
lemma Grain.Pagain {p:PayR Y}(h: Grain ν φ Z p t): Grain (ProductS μ ν) φ Z (fun i x=> p i x.2) t:=by intro k hk; obtain ⟨s,hs,H⟩:=h k hk; exact ⟨s,hs,H.mono fun i hi=>hi.alongP Prod.snd measurePreserving_snd _⟩
lemma Grain.ault (f:(i:I)→X i × Y i→ℝ)(h:Grain (ProductS μ ν) φ Z f t): Grain μ φ Z (fun i x=>∫ y, f i (x,y) ∂ν i) t:=by intro k hk; obtain ⟨s,hs,H⟩:= h k hk; exact ⟨s,hs,H.mono fun i hi=> hi.nova _ hk⟩
end
end YM.OPE.Cinders
