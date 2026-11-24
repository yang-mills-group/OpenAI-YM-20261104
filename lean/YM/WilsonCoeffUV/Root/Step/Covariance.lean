import YM.WilsonCoeffUV.Root.Step.OnLattice
/-! # Orientation δ_i,j. Full columns w/t. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V:Type*}{r h D l j e:ℕ} {G:Gauge}{F:Labels.Frame G h} (T:SectionData F) (w:h<D)

lemma shadePlies (i:F.Index)(n:Side)(u:Config G n)(s:Signed): (T.places (F.act s.ortho (Pi.single i 1)) 0 u).re= ∑ j,bleached F s.ortho j i • (T.places (Pi.single j 1) 0 u).re := by
    let p (j:F.Index):= bleached F s.ortho j i
    have he : F.act s.ortho (Pi.single i 1)=∑ j,(p j:ℂ) • Pi.single j 1:= by funext j; rw [bleach_even]; simp [Pi.single_apply]; rfl
    rw [he]; simp_rw [Source.SectionData.places, Source.SectionData.evaluate,map_sum, map_smul,Complex.re_sum]; exact Finset.sum_congr rfl fun j _=>by simp [p]

-- contravariant lookup sum over sending labels. Applied inputs/ℂ.ToReal.
lemma rootIn (v i:Alma F)(s:Signed)(b:Volume D)(t:spindle s (notar F v)=notar F i): jewelBloom w v (spinV s D b)= hue s (notar F v).val * jewelBloom w i b:=by
    obtain ⟨b,rfl⟩:=submitted b; rw [chronic]; change crease (spinWord s D b) (knurl (notar F v)) 0 = _ * crease b (knurl (notar F i)) 0; rw [Embroider.circle _ _ _ w.le,t]

lemma herald_wind (i:Alma F)(s:Signed)(n:Side)(p:Bid.pop T)(H:Hol G)(hq:T.Sound H):
    Wreathe (herald T w i n) (∑ j:Alma F,blueIn F s j i • herald T w j n) s := by
    classical
    let f:=sheet F i; let u:=notar F i; let M:= fun j:Alma F=> blueIn F s j i • herald T w j n
    let K:=F.grades f; let W:= Finset.univ.filter fun j:Alma F=> spindle s u=notar F j ∧ F.grades (sheet F j)=K; let V:=Finset.univ.filter fun j:F.Index=>F.grades j=K
    let a:= hue s u.val; let J:=valence F i
    intro c X I x A B E; have ht (j:Alma F)(h:j∈W):valence F j=J:= congr_arg Prod.snd (Finset.mem_filter.mp h).2.2
    let D:=jewelBloom w i; let R:=D (spinV s _ c); let b:= bleached F s.ortho
    let U j:= Plies T j n ∘ A; let S:= Plies T f n ∘ B
    have hu j: Green (U j):= ContDiffAt.comp (g:=Plies T j n) _ (E.f₀.symm ▸ (innu T H hq j n)) E.g₀
    have hb : S=ᶠ[𝓝 0] ∑ j∈V,b j f • U j:=by
       filter_upwards [E.shift] with z hz
       change (T.places _ 0 (mantle (B z))).re=_; rw [hz,T.placed_invariant hq _ _, T.placed_signed hq s]; rw [show affine s (0:Site n) 0=0 from by simp [affine], shadePlies]
       rw [Finset.sum_apply]; apply Eq.symm; exact Finset.sum_subset (Finset.subset_univ V) (fun j hj hh=>by unfold b; rw [Pi.smul_apply]; rw [bleach_sparse F _ _ _ (fun k=>hh (Finset.mem_filter.mpr ⟨hj,k.symm⟩)),zero_smul])
    have he:=jet_congr hb
    have hm j: Green (b j f • U j):=ContDiffAt.const_smul (b j f) (hu j)
    rw [jet_sum _ _ (fun j _=> hm j)] at he
    have ht' j: jet (b j f • U j)= b j f • jet (U j):=by
       let c:= b j f; rw [show b j f • _=(fun _:Lawn X=> c)* U j from rfl,jet_mul _ (hu j),jet_const,← real_alg,Algebra.smul_def]; exact contDiffAt_const
    simp_rw [ht'] at he
    have hx : ∑ j∈ W,M j=∑ j:Alma F, blueIn F s j i • herald T w j n := Finset.sum_subset (Finset.subset_univ W) (fun j hj hh=>by
        have hg : blueIn F s j i=0:=by
           unfold blueIn; split
           next e=> rw [bleach_sparse F _ _ _ (fun ht=>hh (Finset.mem_filter.mpr ⟨hj,e,ht.symm⟩)),mul_zero]
           next e=>rfl
        exact (congr_arg (· • herald T w j n) hg).trans (zero_smul ..))
    rw [← hx,map_sum]; have hlen j (h:j∈W): shellK J (M j):= by rw [← ht j h]; exact mu_shellG (herald_norm T w j n) _
    rw [flash_term _ (fun j h=> jot_length _ (hlen j h)),map_sum]
    have hf (A:Lawn X → Lawn (Woods G n))(u:Green A)(t:A 0=0) (i: Alma F)(c:Volume _) :
       (PowerSeries.X^(valence F i))*train (spool A) (flash (jot c (herald T w i n))) = jewelBloom w i c • jet (Plies T (sheet F i) n ∘ A):=by
       conv_lhs=>arg 1; rw [←train_X (spool A),← map_pow];
       rw [←map_mul,herald_lit T w i n c p H hq,train_smul,traveling A u t _ (innu T H hq _ _)]
    apply mul_left_cancel₀ (a:=PowerSeries.X^J) (pow_ne_zero _ X_ne_zero)
    rw [Finset.mul_sum,hf B E.g₁ E.f₁]; rw [he]
    have hg j (hh:j∈W):
       PowerSeries.X^J*train (spool A) (flash (jot c (M j)))=R • b (sheet F j) f • jet (U (sheet F j)):=by
       unfold M; rw [map_smul,flash_mu (l:=J)];
       · rw [train_smul,mul_smul_comm,← ht j hh,hf A E.g₀ E.f₀ j]
         let u:=jewelBloom w j c
         have hu : R=a*u:=rootIn w i j s c (Finset.mem_filter.mp hh).2.1
         rw [hu,smul_smul,smul_smul]; unfold blueIn; rw [if_pos (Finset.mem_filter.mp hh).2.1]; congr 1; unfold a b; ring
       rw [← ht j hh]; exact jot_length c (herald_norm T w j n)
    rw [Finset.smul_sum]
    refine Finset.sum_bij (fun i _=> sheet F i) (fun i h=> Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp h).2.2⟩) ?_ ?_ hg
    · intro i hi j hj v; exact Subtype.ext (Prod.ext v (((Finset.mem_filter.mp hi).2.1).symm.trans (Finset.mem_filter.mp hj).2.1))
    intro j hj; have hx :=(Finset.mem_filter.mp hj).2
    have he' : (F.grades j).1+rankS (spindle s u)≤ h:=by rw [hx,spun_card]; exact weigh_cap F i
    exact ⟨⟨(j,spindle s u),he'⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl,hx⟩,rfl⟩
end YM.WilsonCoeffUV.Cosmos
