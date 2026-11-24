import YM.WilsonCoeffUV.Root.UV.LimitMatrix
/-!
# Aggregate marks admit exact boot over limiting step/ward. Bare out-of-horizon unconstrained. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V α β:Type*}{r h D l e j k a N M m b i q:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{s t t' A B C x y δ σ γ S O v:ℝ}
variable {E W U' V':Credit}{T:SectionData F}{p:h<D}{θ:ℕ→ℝ}

variable (L:Theatre H T p e E W)
lemma meadow (a:L.V.anchor≤m)(v:i≤ e)(j: Alma F): Symbol F j (L.matron m j) i := by
    intro b; exact tendsto_nhds_unique (gleet F (fun n=>(L.lore n m).2 j) (L.matron m j) (fun i h=>fleetOff L a (h.trans v) j) (PathCost.fade L.V.draws.S m) (L.angle m a).lamp.positive b) (tendsto_const_nhds.congr' ((eventually_ge_atTop m).mono fun _ hn=> (epoch (production L hn a).1 j i b).symm))
lemma steedΓ (a:L.V.anchor≤m)(v:i≤e)(j: Alma F): pillar (L.matron m j) i:=by
    let F n:= (L.lore n m).2 j; let W:= L.matron m j
    intro b x
    let V n:= ∑ v:Axis,∑ j:G.ColorIndex,∑ z∈Finset.antidiagonal i, (wickLamp b 0 (x,v) j z.1 (F n z.2)+wickLamp 0 b (x-step v,v) j z.1 (F n z.2))
    have he : ∀ᶠ n in atTop, V n=0:= (eventually_ge_atTop m).mono fun n hn=> solo_upright ((production L hn a).1.scan.solo j) b x i
    funext l w; refine tendsto_nhds_unique (l:=(atTop:Filter ℕ)) (f:=fun n=> V n l w) ?_ (tendsto_const_nhds.congr' (he.mono fun n h=>by dsimp only; rw [h]))
    simp_rw [V,Finset.sum_apply,Pi.add_apply]; apply tendsto_finsetSum; intro t _; apply tendsto_finsetSum; intro j' _; apply tendsto_finsetSum; intro v' hv; have hg:= Finset.mem_antidiagonal.mp hv; exact (Bank.lamp_sure (P:=fun n=> F n v'.2) (F:=W v'.2) (gleaming L a (by omega) j) _ _ _ _ _ _ w).add (Bank.lamp_sure (P:=fun n=> F n v'.2) (gleaming L a (by omega) j) _ _ _ _ _ _ w)
lemma ballet (a:L.V.anchor≤m)(v:i≤e)(j:Alma F)(r)(s:Signed): alliance s (L.matron m j i r) (impose (L.matron m) (paintC F s) j i r):=by
    let W n:= L.lore n m; let σ:= paintC F s
    have hx n (h:m≤n): alliance s ((W n).2 j i r) (impose (W n).2 σ j i r):=by
       have p:= (production L h a).1.scan; exact solo_mercy (p.solo j) (Solo.affixing (W n).1 (W n).2 p.solo (paintCap F s) j) s (fun n=> p.spirit s n j) i r
    have he x: Tendsto (fun n=> impose (W n).2 σ j i r x) atTop (𝓝 (impose (L.matron m) σ j i r x)):=by
       unfold σ; simp_rw [canvasF,Finset.sum_apply,Pi.smul_apply]; exact tendsto_finsetSum _ (fun j _=> (gleaming L a v j r x).const_smul _)
    intro x c; let D:= spinV s D c
    have ht:= (ContinuousLinearMap.apply ℝ ℝ c).continuous.continuousAt.tendsto.comp (he (tickW s 0 ∘ x)); have hu:= (ContinuousLinearMap.apply ℝ ℝ D).continuous.continuousAt.tendsto.comp (gleaming L a v j r x)
    exact tendsto_nhds_unique ht ((hu.const_mul _).congr' ((eventually_ge_atTop m).mono fun n h=> (hx n h x c).symm))
structure GloryBound (F: Frame G h)(P:Thesis F D)(e:ℕ): Prop where
    pose (j: Alma F) i: i ≤ e → Symbol F j (P j) i
    work j i: i≤e → pillar (P j) i
    shoot s j i r : i≤e → alliance s (P j i r) (impose P (paintC F s) j i r)
    cure j i : i≤ e → Pure (P j i)
    trim j i r : i≤ e → valence F j+i< r → P j i r=0
    mote j i : i≤e → P j i 1=0
    slick j i r : i≤e → mural (P j i r)
    earn j i r : i≤e → Standby (P j i r)
lemma primetime (a:L.V.anchor≤ m): GloryBound F (L.matron m) e:=by
   let X:= L.matron m; let T:= fun (n:ℕ)=> L.lore n m
   have hh k (p:k≤e) j r (v:∀ n:ℕ,m≤ n → (T n).2 j k r=0): X j k r=0 := funext fun i=> tendsto_nhds_unique (gleaming L a p j r i) (tendsto_const_nhds.congr' ((eventually_ge_atTop m).mono (fun n hn=>congr_fun (v n hn).symm i)))
   refine ⟨fun j i h=>meadow L a h j,fun j i h=>steedΓ L a h j,fun s j i r h=> ballet L a h j r s,?_,fun j i r p h=> hh i p j r (fun i h' => solo_shape ((production L h' a).1.scan.solo j) _ r (by omega)),fun j i p=>hh i p j 1 (fun n h'=>solo_beam ((production L h' a).1.scan.solo j) L.V.hG i),?_,?_⟩
   · intro j i p r s x; exact tendsto_nhds_unique (gleaming L a p j r _) ((gleaming L a p j r x).congr' ((eventually_ge_atTop m).mono fun n hn=> ((solo_pure ((production L hn a).1.scan.solo j) _ r) s x).symm))
   · intro j i r u f v x; let Q (w:Fin r→ G.ColorIndex):= fun i=>stone (v i) (w i); let K (y:Fin r→G.ColorIndex):=∏ i,gammaC f (y i) (x i)
     refine tendsto_nhds_unique (gleaming L a u j r (Q x)) ((tendsto_finsetSum _ (fun s _=> (gleaming L a u j r (Q s)).const_smul (K s))).congr' ((eventually_ge_atTop m).mono (fun n hn=>?_))); exact (solo_mural ((production L hn a).1.scan.solo j) _ _ f v x).symm
   intro j i r h; obtain ⟨V,hV⟩:=fleetOff L a h j r; obtain ⟨n,hn⟩:= hV.exists; exact ⟨_,_,(L.angle m a).lamp.positive,hn.wane⟩
-- closure equation with inverse useful.
lemma impose_thru [AddCommGroup U][Module ℝ U]{P Q:BookC F U V}(h:∀ i:Alma F,∀ j≤k,P i j= Q i j)(A:Coil F)(i): impose P A i k=impose Q A i k:=by
    simp only [impose,Finset.sum_apply,affix]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro j hj; rw [h a j.2 (by have he:= Finset.mem_antidiagonal.mp hj; omega)]
theorem glossed (a:L.V.anchor≤ m)(v:i≤ e)(j:Alma F):
    let P:=glory L.V.draws L.V.paid T p m; let Y:= Grey L.V.draws L.V.paid m (glory L.V.draws L.V.paid T p (m+1)); P j i= impose Y ((prismata F Y)⁻¹) j i:=by
    intro P Y; let C:=prismata F Y; have hh: impose (impose P C) C⁻¹=P:=by rw [imposition, Matrix.mul_nonsing_inv C (stellarized (leaseOld L a)),impose_plain]
    change P j i=impose Y C⁻¹ j i; nth_rw 1 [←hh]; exact impose_thru (fun j k h=> funext (gliding L a (h.trans v) j)) _ _
theorem matronP (a:L.V.anchor≤m)(v:i≤e): lineS (prismata F (glory L.V.draws L.V.paid T p m)) i=lineS 1 i:=by
    ext1 s w
    have hh:= (primetime L a).pose w i v s
    rw [coined]; rw [show glory L.V.draws L.V.paid T p m=L.matron m from rfl,hh]; rw [lineS,Matrix.of_apply]
    by_cases h:s=w; · subst s; by_cases b:i=0 <;> simp [b]
    simp [h,Ne.symm h]
end YM.WilsonCoeffUV.Cosmos
