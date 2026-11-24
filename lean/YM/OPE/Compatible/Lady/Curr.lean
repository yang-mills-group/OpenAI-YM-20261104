import YM.OPE.Compatible.Lady.Attic
/-! # production under old inventory roofs. Lip sensors. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma.Chase
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard AnalyticBridge.VerifiedReset Geo
open Next.Rank.Thirst YM.OPE
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P:Teller G} {D:Patch} {E:ConnectedActivityE6.Target G P} {L:Side} {W a σ C κ v γ t s w:ℝ} {m:ℕ}
variable {o:ConnectedActivityE6.Target.Order G W}
variable {ι:Type*} {l g:Filter ι} {A:ι→ Model D P L E o κ C m}
variable (h:Chase A l)
include h
variable {j:ι→ℕ}{t u F:ι→ℝ}
open Gauge Flume Next.Rank.Beamer Spells Lass
lemma Kcost (n:ι→Side)(x:∀ i, Site (n i)) (hk:Lite A l (fun i=>(j i:ℝ)))(hz:∀ᶠ i in l,2*(j i+1)<(n i).val): Lite A l (fun i=> Spells.sizeQ (j i)):=by
       have hh(c:ℝ):= Lite.flatC c h; apply ((hh 1).add ((((hk.add hk h|>.add (hh 1) h).product_pw h 4)).rmul (hh 4)) h).ofLe; filter_upwards [hz] with i hi; rw [Real.norm_of_nonneg (show 0 ≤ sizeQ (j i) from (by unfold sizeQ; positivity))]; exact (scoopμ (j i) (n i) (x i) hi).trans (Real.le_norm_self _)
lemma laurels (N:Spells.Pad G) (hk:Lite A l (fun i=>(j i:ℝ)))(hK:Lite A l (fun i=>sizeQ (j i)))(hf:Lite A l F)(hr:∀ᶠ i in l, 0 ≤F i∧ (A i).R.p.threshold≤ u i*t i ∧ 0≤ u i∧ 0 ≤t i)(hu:Lite A l u) :∀ᶠ i in l, let x:=σW A i*F i; let z:=Belts (j i)*x; z ≤ N.B∧ sizeQ (j i)*((t i)⁻¹*z)^2 ≤ N.r^2/2 ∧ 4*x≤ t i:=by
       have hh(c:ℝ):= Lite.flatC c h; let B(i):= Belts (j i); let f(i):=B i*F i; let q(i):=sizeQ (j i); have hp:Lite A l f:= ((hh 8|>.rmul hk).add (hh 1) h).rmul hf; let v(i):= u i*((2*N.r⁻¹)*q i*f i); let g(i):= u i*(4*F i); have he: Lite A l v:= hu.rmul (((hh _).rmul hK).rmul hp); have hg:Lite A l g:= hu.rmul ((hh 4).rmul hf)
       filter_upwards [h.brush he,h.brush hg,hr,h.Dscale,(((h.ζOpR.pays h.tense).mul (hp.sound h)).tends (by norm_num) h.tense).eventually (ge_mem_nhds N.hB)] with i hi he hr hv hz; obtain ⟨hy,hr,hc,hz'⟩:=hr; dsimp only; let x:=σW A i; let a:= F i; let T:= t i; let C:= u i; have hx:0 ≤ B i:=(by unfold B Belts; positivity); have hp:0 < u i*t i:=(A i).R.p.threshold_pos.trans_le hr; have ht:0< t i:= pos_of_mul_pos_right hp hc; have hC:0<C:=pos_of_mul_pos_left hp hz'; have hN:=N.pos; have hq:1 ≤ q i := le_add_of_nonneg_right (by positivity)
       have hV:0 ≤ f i:= mul_nonneg hx hy; have hP:0≤ v i:=by unfold v; positivity; -- uses hq
       rw [Real.norm_of_nonneg hP] at hi; rw [Real.norm_of_nonneg (show 0≤g i from (by unfold g; positivity))] at he; have hR : T⁻¹ * (x*f i) ≤ N.r/(2*q i):=by
              apply (le_div_iff₀ (mul_pos zero_lt_two (zero_lt_one.trans_le hq))).2; have hZ : x*(2*N.r⁻¹ * q i*f i) ≤T :=le_of_mul_le_mul_left ((show C*(x*((2*N.r⁻¹)*q i*f i))=x*v i from by unfold C v;ring).trans_le (hi.trans hr)) hC; unfold T at *; field_simp at hZ ⊢; linarith only [hZ]
       have hh' : 0 ≤ x:=hv.1.le; have hz₀:q i*(T⁻¹*(x*f i))^2 ≤ N.r^2/2 := by
              calc _ ≤ q i*(N.r/(2*q i))^2:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hR _) (by positivity)
                   _ = N.r^2/(4*q i):= by field_simp; ring
                   _ ≤ _:= by gcongr; linarith only [hq]
       have hh: B i*(x*a)=x*f i:=by unfold a f;ring
       refine ⟨hh.trans_le hz,?_,?_⟩; · change q i*(T⁻¹*(B i*_))^2≤_; rw [show B i*_=_ from hh]; exact hz₀
       have hy' : C*(4*(x*a))=x*g i:=by unfold a C g; ring
       exact le_of_mul_le_mul_left (hy'.trans_le (he.trans hr)) hC
end YM.PhysicalNext.Repeat.Aroma.Chase
