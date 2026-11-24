import YM.MSbar.Mosaic.Hammer
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Mosaic
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz
open Next.SectorChange Bulk Posture JetTab
variable {G:Gauge}
namespace Issue
variable {ι:Type}{X f' g:ι→ℝ}{A:ι→Issue G}{φ:Filter ι}[φ.NeBot] (hX:Tendsto X φ atTop) (χ:ChartRatio G)(J:Voice G)(H H':Stage)(K:Patch)(D:KernelChoices)
variable (hG:G.Simple) (hD:K.Branches D G)(hQ: Clear G J)(hχ:LocalRatio χ)
local notation "α'" i=> tip G K.L (X i)
local notation "Y"=> fun i:ι=> tip G K.L (X i)
local notation "w'" i=> vol (tip G K.L (X i))
local notation "t'" i=> (A i).fClock
variable (hp:∀ᶠ i in φ,Paid (A i) K H H' J (X i)) (hq:∀ᶠ i in φ,(A i).S.kernel=D)
variable (W:(i:ι)→Positions (Primary (A i).c G))(hW:∀ᶠ i in φ,‖W i‖ ≤ hull (X i))
variable {p m k q:ℕ}
variable (M:StageCost)(i':G.ColorIndex){s e ν b:ℝ}(hc:∀ᶠ i in φ,Festival (A i) χ p i' ∧ ClockD (A i) p m M.s (X i)∧ Cs (A i) χ M.s p m (X i) i' (f' i) b ∧ Issue.Receipt (A i) M (X i))
variable (h₁:p+2 ≤ m)(ha:Run φ X f' 0)(hk:k=m+1) (hT:p+3≤ k) (hμ:4 ≤ m)
include h₁ ha hk hT
-- outer choice after orientation budgets. caller. Vows export with constants cost.Ra.
local notation "N"=> k*(p+2)
variable (U Ω:ι→ℝ)(hU:Run φ (fun i=>tip G K.L (X i)) U 0)(hΩ: Run φ (fun i=>tip G K.L (X i)) Ω 0) (hu:∀ᶠ i in φ,1 ≤ U i∧1 ≤ Ω i)
-- expose anchors. stamp.Y
noncomputable def Ages' (C D c d:ℝ)(r1 r2 tx bb k1 k2 u w:ℝ) := (⟨C,D,c,d,r1,r2,4*r1,tx,bb,k1,k2,u,w⟩:Ages)
include hX hp hc hQ hχ hq hU hΩ hu hG hμ
lemma award : ∃ (a b c d k1 k2 tx:ℝ) (ψ:ι→ℝ), Run φ (fun i=> tip G K.L (X i)) ψ 0∧ ∀ᶠ i in φ,
          let w:=vol (Y i); let y:=5*goalP (Y i) p
          Ages.Vying (Ages' a b c d (U i) (Ω i) tx (ψ i) k1 k2 y w) p k (A i).fClock (A i).T (A i).F (A i).pre χ (A i).v:=by
     let P:=Ages'; let t(x):=(A x).fClock; let v:=Y; have hv:Tendsto v φ atTop:= (Work.E09.betaF_growth G K.L).comp hX; have ht:=roundS hX J H H' K hG hp|>.1
     obtain ⟨V⟩:= pre_order G H'.width H'.paths K.J D (by omega:3 ≤ k)
     obtain ⟨C,D',he⟩:= Tilt.gate G; obtain ⟨c,d,h₀,hd,hI⟩:=Ruby.storie G 2 p
     obtain ⟨B0,C1,hB,h1,hQ'⟩:= Ruby.almostX χ hχ k
     let K1:= Parma.priceArc K G D k V.Z V.lc V.W; let z:=min (Ruby.volumeP V K) B0; obtain ⟨S,hS,hS'⟩:=server hX χ J H H' K hG hp M i' hc h₁ ha
     let z'(x):= S x*(1+4*U x)^(p+2+1); have hh:S = S:=rfl; have hz:(Run φ v z' 0):= ((Run.wander hX G hG K.L _ _).1 hS).Ymul hv ((Run.addR hv (Run.token hv _) (Run.mulK hv hU _)).Ypow hv _)
     let f:= fun x=>t x*U x; let δ:ℝ:=-(1/2:ℝ); have hx:Tendsto f φ (𝓝 0):= ((ht.Yrat hv hU).bouquet hv (by norm_num)); have hf:Tendsto (fun x=>D'*t x*U x^2) φ (𝓝 0):= ((ht.mulK hv D'|>.Yrat hv (Run.Ypow hv hU 2)).bouquet hv (by norm_num)); have ht': Tendsto t φ (𝓝 0):=ht.bouquet hv (by norm_num)
     obtain ⟨i,he',hy'⟩:= (hp.and hq).exists; have hz0:0<z:=lt_min (he'.space ▸ (Ruby.convertR (A i).F (A i).v V hy').1) hB
     refine ⟨C,D',c,d,K1,C1,z,z',hz,?_⟩
     have hu': Tendsto (fun x=> t x*(4*U x)) φ (𝓝 0):= by
          have h:= hx.const_mul 4; rw [mul_zero] at h; exact h.congr (fun i=>mul_left_comm ..)
     have hg:Tendsto (fun i=>t i*Ω i) φ (𝓝 0):= (ht.Yrat hv hΩ).bouquet hv (by norm_num); have hw:Tendsto (fun i=> vol (v i)) φ atTop:=by
           unfold vol; simp_rw [div_eq_mul_inv]; exact (Alto.broad.comp hv).atTop_mul_const (by positivity)
     filter_upwards [ hp,hq,hc,hu,hS', ht'.eventually (eventually_lt_nhds zero_lt_one), hx.eventually (eventually_lt_nhds he.r), hx.eventually (eventually_lt_nhds h₀), hu'.eventually (eventually_lt_nhds h₀), hg.eventually (eventually_lt_nhds hz0),hf.eventually (ge_mem_nhds zero_lt_one),hw.eventually_ge_atTop 1, gate hX hG hX K.L 0] with i he' hq ⟨hV,hQ,hL,hG⟩ hU hh ht hx hx' he1 h2 h3 h4 hQ0 w y
     let Q:= P C D' c d (U i) (Ω i) z (z' i) K1 C1 y w; have hu:1 ≤ U i:=hU.1; have hμ':(A i).passage (X i)= v i:=by unfold passage; rw [he'.space] -- Xf missing
     have hS':0 ≤ S i:=hh _ le_rfl|>.1.2.1
     have hh':∀ i'≤p, Tokew (Measuring.chart (A i).f G) (αm (Y i)) M.s (p+2) 0 (PowerSeries.coeff i' (tariff (A i).f p (A i).pre.clip (A i).pre.path (A i).T)) (S i):=by
         intro i' hi; have hx := hh i' hi|>.1.2; rw [hμ'] at hx; refine Tokew.delta (Tokew.soft hx hQ0.2.2.1 (le_trans (show 0 ≤ ray 0 (thorn (Y i) 0) from mul_nonneg (Nat.cast_nonneg _) hQ0.1.le) hQ0.2.1)) (by omega) le_rfl
         -- αm downgrade derive
     have hη' :0 ≤ αm (v i):=le_trans (mul_nonneg (Nat.cast_nonneg _) hQ0.1.le) hQ0.2.1
     have hVq:=hQ.turns; rw [hμ'] at hVq; let X':=Metric.closedBall (0:Positions (Primary (A i).f G)) w; have hb':0< w:= zero_lt_one.trans_le h4; have hS'' : ∀ i'∈X',ContDiffAt ℝ (↑(m+1:ℕ)) ((A i).preY p) i':=by unfold X'; unfold w; rw [← show (A i).passage (X i)=tip G K.L (X i) from hμ'];exact hQ.beam
     change Ages.Vying Q p k _ _ _ _ _ _; refine Ruby.rent (A i).F (A i).pre (A i).v χ (A i).fClock (A i).T p Q V hq hχ ?_ ?_ ?_ hT ht.le ?_ h1 ?_ he hI ?_ he1 hx hx' h2 ?_ hη' h4 ?_ le_rfl hh' hV.preT.choose_spec.plane ?_ ?_ -- signature
     · rw [he'.space]; exact min_le_left ..
     · exact hz0
     · change 0 ≤ z' i; unfold z'; have h₀:= hU.1; positivity
     · intro a b hv; apply hQ' (A i).F b a (hv.trans_le (min_le_right ..))
     · rw [he'.space,hq]; exact le_rfl
     · change 1 ≤ 4*(U i); linarith only [hu]
     · change 3*U i+D'*t i*U i^2 ≤ 4*U i; linarith only [hu,h3]
     · apply mul_nonneg (by norm_num : (0:ℝ)≤5) (hVq.peak _ le_rfl|>.1)
     · intro x hx; exact (hS'' x hx).of_le (by exact_mod_cast (show 2 ≤ m+1 from by omega))
     · intro j hj; exact JetTab.levelAll hb' hη' hS'' hVq hμ (le_rfl : m+1≤ m+1) j (by omega)
end Issue
end YM.MSbar.Mosaic
