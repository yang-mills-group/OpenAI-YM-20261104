import YM.MSbar.Alto.Nestas
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Alto
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge} (B:MapPrices)(j i s p:ℕ)
-- diagnostic caps independent positivity of underlying Sheet Ω.Or
noncomputable def drift (B:MapPrices)(i:ℕ):=|B.Ω i|+1
noncomputable def ceilα (B:MapPrices)(j i:ℕ):= min (1:ℝ) (min (B.α j/4) (B.α i/2))
noncomputable def leads (a:ℝ)(s:ℕ)(t:ℝ):Prop:=1≤t ∧ ∀ i:ℝ, 0 ≤ i→(1+i)^s ≤ t * Real.exp (a*i)
lemma lobby (a:ℝ)(s:ℕ)(h:0<a) : ∃t:ℝ, leads a s t:=by obtain ⟨t,ht,hC⟩:=sufficient s a h; exact ⟨t,ht,hC⟩
noncomputable def low (a:ℝ)(s:ℕ) :ℝ:= if h:0<a then (lobby a s h).choose else 1
lemma low_earns (a:ℝ)(s:ℕ)(h:0 < a): leads a s (low a s) :=by rw [low,dif_pos h]; exact (lobby a s h).choose_spec
lemma zonepos:0 < ceilα B j i:=by unfold ceilα; have he:=B.alpha_pos j; have hx:= B.alpha_pos i; positivity
lemma cone_pos:0 < drift B i:=by unfold drift; positivity
noncomputable def widthP (B:MapPrices)(i s:ℕ):= low (B.α i/4) s
noncomputable def quota (B:MapPrices)(i s:ℕ):= low (B.α i/2) s*apron (B.α i) (drift B i)
lemma moneyN :0 ≤ quota B i s:=by
    let a:=B.α i; have he:= B.alpha_pos i; have hx:= low_earns (B.α i/2) s (by positivity); unfold quota; apply mul_nonneg (zero_le_one.trans hx.1); unfold apron; have h₁:0≤ (oer a):= (Next.Free.delta_budget 1 a).choose_spec.1.le; have h₂:= UVNext.PricedKernels.dC_nonneg 1 (B.α i); have h:=cone_pos B i; unfold a at *; positivity
noncomputable def seats (B:MapPrices)(j i s:ℕ):Fees:=  { pre:= B.α j
                                                         tilt := drift B j
                                                         shape := widthP B j s
                                                         axis:=3
                                                         bc:=quota B i s
                                                         bf:=quota B j s
                                                         c1:=0
                                                         c2:=0
                                                         c3:=0
                                                         c4:=0
                                                         farms:=0 }
-- choose L threshold paying `Host` all p.Pr max for pairs.
local notation "α"=> ceilα B j i
local notation "V"=> seats B j i s
include j in
lemma pieces : 0 ≤ (seats B j i s).pre ∧0≤(seats B j i s).tilt∧0≤(seats B j i s).shape:=by
    exact ⟨(B.alpha_pos j).le,(cone_pos B j).le, zero_le_one.trans (low_earns _ s (show 0 < B.α j/4 from by have he:=B.alpha_pos j; positivity)).1⟩
lemma hoster (G:Gauge)(hs:6≤ s): ∀ᶠ m:ℕ in atTop, ∀ n: Side,n.val=m→Host G (seats B j i s) n p s (ceilα B j i):=by
    let F(k:ℕ):=fixP G k α (seats B j i s).tilt (seats B j i s).pre (seats B j i s).shape s (seats B j i s).axis
    have hp₀:= pieces B j i s; have ht(x:ℕ):0≤ F x:=(fixer _ _ _ _ hp₀.2.1 hp₀.2.2 le_rfl).1
    let X(k:ℕ)(n:ℕ):=F k/n; have hx (p): Tendsto (X p) atTop (𝓝 0):=tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop; have hv (n):∀ᶠ m in atTop,X n m < 2⁻¹^ Dean n ∧ X n m*(1+(seats B j i s).bc) < 2⁻¹^Dean n:=by
        have hp :0 < ((2:ℝ)⁻¹^Dean n):=by positivity
        have he:= (hx n).mul_const (1+(seats B j i s).bc); rw [zero_mul] at he; exact ((hx n).eventually (eventually_lt_nhds hp)).and (he.eventually (eventually_lt_nhds hp))
    filter_upwards [(Finset.Icc 1 p).eventually_all.mpr (fun k _=>hv k)] with m he n hn; subst m
    exact ⟨he,le_rfl,hs,(zonepos ..|>.le),hp₀,⟨moneyN B j s,moneyN B i s⟩,fun r _=>div_nonneg (ht _) (by positivity),⟨le_rfl,le_rfl,le_rfl,le_rfl,le_rfl⟩⟩
variable {μ C':ℝ}{K:KernelChoices}
noncomputable def pinK (j:ℕ) (G:Gauge)(c:ℝ)(p m:ℕ)(P:Patch)(H:ChartRatio G)(Y:Uniform.Before G μ C' j K (p+3)) := 1+∑ i∈Finset.range p, |cream c m i P Y H|
-- choose actual slot sizes with chart capsule from S fixed. define seats.Fees from δ.Of
noncomputable def tango (A:Patch) (J:ChartRatio G) (Z:Uniform.Before G μ C' j K (p+3)) (b:ℝ)(v:ChartPrices) :Fees:= let a:= B.α j; let C:=low b s; {seats B j i s with
                                        c1:=goalM G A C a (drift B j) b
                                        c2:=goalL G A C a (drift B j) b
                                        c3:=goalK G C b
                                        c4:=goalN G v.gap C b
                                        farms:=pinK j G (ceilα B j i) p s A J Z }
open UVNext.PricedKernels
lemma largeJ {G:Gauge} (A:Patch)(J:ChartRatio G) (Z:Uniform.Before G μ C' j K (p+3))(b:ℝ)(v:ChartPrices) (h:Host G (seats B j i s) A.L p s (ceilα B j i)): Host G (tango B j i s p A J Z b v) A.L p s (ceilα B j i):=by
   refine ⟨h.expedient,h.spark,h.arity,h.orbit,h.ok,h.fine,h.stars,?_⟩
   let S:= (tango B j i s p A J Z b v); refine ⟨(show 0≤pinK j G (ceilα B j i) p s A J Z from ?_),zero_le_one.trans (le_max_left ..),zero_le_one.trans (le_max_left ..),zero_le_one.trans (le_max_left ..),zero_le_one.trans (le_max_left ..)⟩; unfold pinK; positivity
end YM.MSbar.Alto
