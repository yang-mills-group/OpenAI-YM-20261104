import YM.FormalBulk08.Hay.Epoch

/-! Canonical BAC ages through to various Kin sides. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Hay
open Filter Set Function MeasureTheory Lattice RG Exterior Wilson Precision Tree Work.F05
open Stationary hiding shine Rays
open Reef Series Wick Jets Orb Plait PowerSeries Lava Mesa Broc City Cork Lotus Shore Gorge Laurent Bloch Flat Next.Free Bank
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{K:KernelChoices}{m:ℕ→Side}{p q:Clip}{R U:PathData G}{σ Γ Λ B C γ η E D α:ℝ}{j t r e:ℕ}
lemma lit_period {V:Type*}(F:(n:Side)→ Tile (Tor n V) r)(a:Tile (Biglot V) r){h:ℝ}(hv:Kith h a F)(hp:Tendsto m atTop atTop)(x:chain (Biglot V) r): Tendsto (fun i=>F (m i) (Lotus.drip _ ∘ x)) atTop (𝓝 (a x)):= (hv.1 x).comp hp
lemma lit_cum (V:Pot G)(h:FloatK V)(hp:Tendsto m atTop atTop)(i: Fin r)(x : chain (edgeL G) r)(e): Tendsto (fun k=> cum i (m k) (V e r) (Lotus.drip _ ∘ x)) atTop (𝓝 (V e r x)):= by
    obtain ⟨s,C,hs,H⟩:=h.fare e r; exact lit_period _ _ (stable hs.le (h.civil e r) H i) hp x
variable (P:Flight j t)(T:Lodge P.patch)(W:Pot G)(ρ:ChartRatio G)(h:P.patch.Branches K G)
section planning
variable (F : ∀ i:ℕ, Bid.Dir G (m i) → AxisChart G (Reef.floor K P T (m i)))
variable (hm:Tendsto m atTop atTop)(ht:4≤ t)(hr:LocalRatio ρ)
    (hb: R.Bounds p σ B C)(hy:Story W (pink K.penalty P.wing))(hx:∀ i,Through 2 (stone W (m i*P.patch.L)) (novel p R _))
    (H:∀ i,Critical (S:=primary P.patch K (m i)) (Reef.floor K P T (m i)) p R (F i))(hs:G.Simple)
include F hm ht hr hb hy hx H hs
-- choose K independently from any `Kin` label
lemma equal_spot (he:e≤2)(Y:Pot G)(hY:Troupe Y q U)(hF:∀ i,ClassicalMatch (S:=primary P.patch K (m i)) (Reef.floor K P T (m i)) p q R U (F i)):
       waken P T W ρ h e (e+2)= Y e (e+2):= by
    let k n:= Classical.choice (chooseable _ _ (primary P.patch K n)); let v:=Bank.burn P T W ρ h k
    obtain ⟨s,b,hV⟩:=componentwise P T W ρ h hy ht hr k e (e+2) 0
    have hE(e:ℕ)(he:e≤2)(n:ℕ): marble (e+2) (coeff e (v (m n)))=cum 0 (m n) (Y e (e+2)):= by
        obtain ⟨h0,h1,h2,h3⟩:=ready P T (m n) ρ h ht (k (m n)) W hy hb (F n) (H n) (hx n) hs hr
        refine head_lane _ (F n) (k (m n)) (hF n) he ?_ hY
        interval_cases e
        · rw [show coeff 0 (v (m n))=_ from h0,map_neg,MvPolynomial.homogeneousComponent_eq_self (paste_grade ..)]
        exact h1
        exact h2
    funext x;refine tendsto_nhds_unique (lit_period _ _ hV hm x) ?_; refine (lit_cum Y hY.toFloatK hm 0 x e).congr' (.of_forall fun i=>?_)
    exact congr_fun (hE e he i).symm _
lemma flat_fee (Y: Pot G)(hY:Troupe Y q U)(hU:U.Bounds q η E D)(hγ:0<γ)(hF:∀ i, FiniteBound (S:=primary P.patch K (m i)) (Reef.floor K P T (m i)) R U p q α ρ (F i) Γ γ Λ):
       waken P T W ρ h 2 2= Y 2 2+α • Y 0 2:= by
    let k n:= Classical.choice (chooseable _ _ (primary P.patch K n));let v:=Bank.burn P T W ρ h k
    obtain ⟨s,b,hV⟩:=componentwise P T W ρ h hy ht hr k 2 2 0
    funext x; let f(n:ℕ):=Lotus.drip (I:=Loc G 1) (m n) ∘ x
    let g(n:ℕ):= rancho (v (m n)) 2 2 (f n)
    let Z :=Y 2 2+α•Y 0 2; let u(n:ℕ):=cum 0 (m n) Z (f n)
    let L(n:ℕ):= (1/2:ℝ)*(skyL G (m n) * ((Fintype.card (Site (m n)):ℝ) *(Γ * Λ)*Real.exp (-γ *(m n).val)))
    have hL:Tendsto L atTop (𝓝 0):= by simpa only [mul_zero,L] using (tolling hm hγ G (Γ*Λ)).const_mul (1/2:ℝ)
    have hd n:|g n-u n|≤ L n:= by
       unfold g u Z; let c:=m n; have he:= ready P T c ρ h ht (k c) W hy hb (F n) (H n) (hx n) hs hr; change |marble 2 _ _-cum 0 (m n) _ _|≤ _; obtain hw:= body_lane (Reef.floor K P T c) (F n) (k c) ρ (hF n) hU he.2.2.2 hY (f n); exact hw.trans_eq (by unfold L; rw [←mul_assoc (Fintype.card (Site c):ℝ) Γ Λ])
    have hZ: Tendsto u atTop (𝓝 (Z x)):= by
        obtain ⟨s,A,hX,hA⟩:=hY.fare 0 2; obtain ⟨p,B,hP,hB⟩:=hY.fare 2 2
        have he : 0 < min s p:= lt_min hX hP; exact lit_period _ Z (stable he.le (Up.add (hY.civil 2 2) (Up.smul (hY.civil 0 2) α)) ((hB.shrink (min_le_right ..)).add ((hA.shrink (min_le_left ..)).smul _)) 0) hm x
    have he:Tendsto g atTop (𝓝 (Z x)):= by
       have hz: Tendsto (g-u) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun i=>norm_nonneg _) hd hL)
       have hu:= hz.add hZ; rw [zero_add] at hu; simpa using! hu
    exact tendsto_nhds_unique (lit_period _ _ hV hm x) he
end planning
end YM.FormalBulk08.Hay
