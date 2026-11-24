import YM.WilsonCoeffUV.Stable.Analytic.Pay
/-!
# Cost of D in true exponential controlled kernel class

After exact projection; coordinates have to be kept separately for the soft-stop budget.
Cost works for any On (finite degree caps per coupling power and all Ward); not an arbitrary
single compact profile with just finite derivative norm. Funds the exponential paths for the
single-step reader at ANY step of that propagation. Normalization issue: strict terms all price
linearly in support budget even with enormous input (eg. from capture).
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.StableStrip
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Shard Mer.Scopes
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{ι U V: Type*}{r h D l j i e k a m b u N M c:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A C' t B x δ:ℝ}

lemma emitted (X:Island F D)(p:Shimmer X)(P:TowerS G D)(W:Clean u e r F C' P.2) (v:x≥0)(H:∀i j,j≤ e→ Twig 0 s x (X.2 i j r)) : Twig 0 s (∑ _ : Alma F,∑ _∈ Finset.antidiagonal e,C'*x) ((Shrine X (opal F P)).2 e r):=by
   have hx:=W.fare; unfold Shrine; simp_rw [Prod.snd_sum,Stem,Shard.vein, Finset.sum_apply, affix]; apply Cork.sum; intro i _; rw [Finset.sum_apply]; apply Cork.sum; intro b hb
   have he:=Finset.mem_antidiagonal.mp hb; by_cases hv:r≤valence F i+b.2; · rw [Pi.smul_apply]; refine (Cork.μ (H i b.2 (by omega)) _).cost ((mul_le_mul_of_nonneg_right ?_ v)); rw [opal,coeff_mk]; exact W.row _ _ (by omega)
   rw [Pi.smul_apply, show X.2 i b.2 r=0 from solo_shape (p.scan.solo i) b.2 r (lt_of_not_ge hv), smul_zero]; exact Cork.zero.cost (by positivity)

lemma unStem (F:Frame G h)(H:Hol G)(T:SectionData F)(p:h<D)(k e r:ℕ): ∃ d:ℕ,∀ I:Cloister G h,∃ C:ℝ,0≤ C∧∀ (A:Levels G)(Ñ:ChartRatio G)(N m:ℕ)(W:Rally (e+1) 0 (inkPin I))(hv:m<N)(g:G.Simple)(q:LocalRatio Ñ)(V:Usage A Ñ m), ClaimP A N m hv g q V _ W.P → I.lamp.dues r →∀Y:TowerS G D, On k Y → opal F Y=0 → Shimmer (Peaks A Ñ T p N m)→ Courant I W.P →(∀ i j,j≤e → Twig 0 I.lamp.exitS W.x ((Peaks A Ñ T p N m).2 i j r)) →∀ X:ℝ, Twig 0 I.lamp.input X (Y.2 e r) → (∀ i j,lowerGrade i j e r → Twig 0 I.lamp.input 1 (Y.2 i j)) →
    Twig 0 I.lamp.exitS (velo H F p I.lamp r/(inkPin I).patch.L.val * X + C*W.x^d) ((Sink A Ñ T p N m k Y).2 e r):=by
   obtain ⟨d,H'⟩:= unShelved F H p e k r
   refine ⟨d+1,fun I=>?_⟩; obtain ⟨A,hA,f⟩:= H' I; let E:=A+ (∑ _ : Alma F, ∑ _∈ Finset.antidiagonal e,A)
   have hE:A≤E:=le_add_of_nonneg_right (Finset.sum_nonneg fun _ _=> Finset.sum_nonneg fun _ _=>hA)
   refine ⟨E,hA.trans hE,?_⟩; intro A' Ñ n m W hp G' q V he a Y w z hs q' rt X hc v
   let U:= Peaks A' Ñ T p n m; let Z:= Spout A' Ñ n m h k Y; have hv: Z.2= _:=spout_orch Y he h k
   let P: Tand I.lamp e r D:=⟨W,Y.2,Y.2,fun i j p=>Shelf.encore ((v i j p).cost W.rich) W.θ⟩
   have hg (i:Alma F): glean F Y.2 e i=0:=by rw [show glean F Y.2 e i= coeff e (opal F Y i) from Eq.symm (show coeff e (opal F Y i)=_ by rw [opal,coeff_mk]),z]; simp
   obtain ⟨ht,hx⟩:=f P q' X a w.flanks (fun i _=> hg i) hc
   have hr:0≤W.x:=zero_le_one.trans W.rich
   have hd := emitted U hs Z (hv.symm ▸ hx) hr rt
   change Twig 0 I.lamp.exitS _ (Z.2 e r- (Shrine U (opal F Z)).2 e r); apply (Cork.sub (hv.symm ▸ ht) hd).cost; rw [add_assoc]; apply add_le_add_right; change A*W.x^d+(∑ _ : Alma F,∑ _∈ Finset.antidiagonal e,A*W.x^d*W.x) ≤ _; unfold E; rw [add_mul]; simp_rw [Finset.sum_mul]; refine add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ W.rich (by omega)) hA) (Finset.sum_le_sum fun i _=> Finset.sum_le_sum fun _ _=>?_); exact le_of_eq (by ring)
-- homogeneity bridge
lemma stem_μ (A:Cost)(Y:TowerS G D)(c:ℝ): Stem (c • A) Y= c • Stem A Y:=by
    have hh {V: Type}(T:Pal (Vote D) V): affix (c • A) T=c • affix A T:=by funext i; unfold affix; simp only [Pi.smul_apply,Finset.smul_sum, coeff_smul,smul_eq_mul,smul_smul]
    exact Prod.ext (funext fun _=> hh _) (hh _)
lemma shrine_μ (c:ℝ)(Y:Island F D)(v:Verse F): Shrine Y (c • v)=c • Shrine Y v:=by unfold Shrine; simp_rw [Pi.smul_apply, stem_μ,Finset.smul_sum];
lemma sink_μ {A:Levels G}{Ñ:ChartRatio G}(hp:m<N)(g:G.Simple)(q:LocalRatio Ñ)(T:SectionData F)(p:h<D){Y:TowerS G D}(u:On k Y)(c:ℝ): Sink A Ñ T p N m k (c • Y)= c • Sink A Ñ T p N m k Y:=by unfold Sink Spray; rw [supp hp g q Y u,opal_mu,shrine_μ,smul_sub]

lemma cork_right {Y:ChamberTen G (Vote D) r}(C M:ℝ)(h:∀ᶠ x:ℝ in nhdsWithin A (Set.Ioi A),Twig 0 s (C+M*x) Y): Twig 0 s (C+M*A) Y:=by
    have he: Tendsto (fun x:ℝ=>C+M*x) (nhdsWithin A (Set.Ioi A)) (𝓝 (C+M*A)) := (tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds)))
    refine ⟨ge_of_tendsto he (h.mono fun i v=> v.1),fun i=> ge_of_tendsto (he.mul_const _) (h.mono fun j v=>v.2 i)⟩

lemma analyticStep (F:Frame G h)(H:Hol G)(T:SectionData F)(p:h<D)(k e r:ℕ): ∃ d:ℕ,∀ I:Cloister G h,∃ C:ℝ,0≤ C∧∀ (A:Levels G)(Ñ:ChartRatio G)(N m:ℕ)(W:Rally (e+1) 0 (inkPin I))(hv:m<N)(g:G.Simple)(q:LocalRatio Ñ)(V:Usage A Ñ m), ClaimP A N m hv g q V _ W.P → I.lamp.dues r →∀Y:TowerS G D, On k Y → opal F Y=0 → Shimmer (Peaks A Ñ T p N m)→ Courant I W.P →(∀ i j,j≤e → Twig 0 I.lamp.exitS W.x ((Peaks A Ñ T p N m).2 i j r)) →∀ X A':ℝ,0≤ A' → Twig 0 I.lamp.input X (Y.2 e r) → (∀ i j,lowerGrade i j e r → Twig 0 I.lamp.input A' (Y.2 i j)) →
    Twig 0 I.lamp.exitS (velo H F p I.lamp r/(inkPin I).patch.L.val * X + C*W.x^d*A') ((Sink A Ñ T p N m k Y).2 e r):=by
   obtain ⟨d,H'⟩:=unStem F H T p k e r; refine ⟨d,fun i=>?_⟩; obtain ⟨C,h,H⟩:= H' i
   refine ⟨C,h,?_⟩; intro A Ñ n m W hv g q V hp hM Y t ht z u H' X K hK hX v
   apply cork_right; filter_upwards [self_mem_nhdsWithin] with j hj; have he: K<j:= hj; have h:0<j:=hK.trans_lt he; have hh:j⁻¹•opal F Y=0:=by rw [ht,smul_zero]
   let Z:=j⁻¹ • Y; have he: Twig 0 i.lamp.input (j⁻¹ * X) (Z.2 e r):=by have hx:= Cork.μ hX j⁻¹; rw [abs_of_nonneg (inv_nonneg.mpr h.le)] at hx; exact hx
   have hz i' j' (hg:lowerGrade i' j' e r): Twig 0 i.lamp.input 1 (Z.2 i' j'):=by
       have he:= Cork.μ (Cork.cost (v i' j' hg) (show K≤ j from (show K<j from hj).le)) j⁻¹
       rw [abs_of_nonneg (inv_nonneg.mpr h.le),inv_mul_cancel₀ h.ne'] at he
       exact he
   have hg:= H A Ñ n m W hv g q V hp hM Z (t.μ j⁻¹) (by rw [show Z=j⁻¹ • _ from rfl,opal_mu F]; exact hh) z u H' _ he hz
   have hx:= Cork.μ hg j; unfold Z at hx; rw [sink_μ hv g q _ _ t, abs_of_nonneg h.le] at hx; simp only [Prod.smul_snd,Pi.smul_apply,smul_smul,mul_inv_cancel₀ h.ne',one_smul] at hx; apply hx.cost; apply le_of_eq; field_simp
end YM.WilsonCoeffUV.StableStrip
