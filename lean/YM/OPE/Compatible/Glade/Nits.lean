import YM.OPE.Compatible.Glade.Dusk
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.PriceZ
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {W:Type}{v b:W→ℝ}
-- regular voyages, auxiliary mobility.Link.
variable {x:ℝ}{X: Seasons K}
lemma trice (φ: W→TileC X P p R x)(z:ℝ)(h: ∀ i,upperX (φ i)≤ z)(hs:G.Simple)(hq:LocalRatio R)(hp:Crest G P K.K m): Linking (v:=fun i:W=>(φ i).1.1.cost) (v':=fun i=>(φ i).1.2.cost) (fun i=>UA (φ i)) (fun i=>VA (φ i)) (downK∘φ):=by
       refine ⟨⟨⟨p,fun i=>(φ i).1.1.R _⟩,⟨max 0 z,le_max_left ..,fun i=>le_trans (le_trans (le_max_left ..) (h i)) (le_max_right ..)⟩,fun i=>zero_le_one.trans (φ i).1.1.fits⟩,⟨⟨p,fun i=>(φ i).1.2.R _⟩,⟨max 0 z,le_max_left ..,fun i=>le_trans (le_trans (le_max_right ..) (h i)) (le_max_right ..)⟩,fun i=>zero_le_one.trans (φ i).1.2.fits⟩,(fun i=>show 0 ≤ (1/2:ℝ)^(φ i).2 from by positivity),?_,?_,?_,?_⟩
       all_goals
         have he(i:W):0 ≤ upperX (φ i):= zero_le_one.trans (max_cap (H:=X) (p:=p) (P:=P) (V:=R) (C:=x) (φ i))
         have ht(i:W):0 ≤ downK (φ i):=pow_nonneg (by norm_num : 0 ≤ (1/2:ℝ)) _
         have hv (k:ℕ)(p':TileC X P p R x→Script (Shade G) k)(hp:Loan m p' downK upperX): ToughZ (p'∘φ) (downK ∘φ):=by
              obtain ⟨c,hc,r,H⟩:= hp.crush (Nat.zero_le _); refine ⟨c*(max 0 z)^r,(by positivity),fun i=>(H (φ i)).tips ?_⟩; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (he i) ((h i).trans (le_max_right ..)) _) hc) (ht _)
       · exact hv 2 (Alps.marksD 2) ((energyProd hq hp hs).1 2 (by decide) (by decide))
       · exact hv 3 (marksD 3) ((energyProd hq hp hs).1 3 (by decide) (by decide))
       · exact hv 4 (marksD 4) ((energyProd hq hp hs).1 4 (by decide) (by decide))
       exact hv 2 (Newton 2) (energyProd hq hp hs).2.2
lemma liftLoanP {A:Type}(φ: W→TileC X P p R x)(z:ℝ)(h:∀ i,upperX (φ i)≤ z)(p':TileC X P p R x→ Script A k)(hp:Loan r p' 1 upperX):∃ c:ℝ,∀ i, soot r (p' (φ i)) c :=by
     obtain ⟨c,hc,r,H⟩:=hp; refine ⟨c*(max 0 z)^r,fun i=>(H _).tips ?_⟩; rw [Pi.one_apply,mul_one]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (max_cap (P:=P) (p:=p) (H:=X) (V:=R) (C:=x) _)) ((h i).trans (le_max_right ..)) r) hc
lemma Runic (φ: W→ TileC X P p R x)(z:ℝ)(h:∀ i,upperX (φ i)≤ z) (B:Medal P G K.K P.J)(hp:Crest G P K.K m): ∃ a b:ℝ, 0 < a ∧ 0 ≤ b∧∀ i, Telet P (charmSeal B (UA (φ i)).gear) a b:=by
    obtain ⟨s,V,hX,hF,hp⟩:= running X P B p R x hp
    have he(I J:Type) (A:TileC X P p R x→ Row I J)(ht:Tip V A 1 upperX):∃ c:ℝ,∀ i:W,(A (φ i)).strip V c:=by
         obtain ⟨c,hc,r,H⟩:=ht; refine ⟨c*(max 0 z)^r,fun i=>strip_mono (H (φ i)) le_rfl ?_⟩; simp only [Pi.one_apply,mul_one]; apply mul_le_mul_of_nonneg_left _ hc; exact pow_le_pow_left₀ (zero_le_one.trans (hF.fuel _)) (le_trans (h i) (le_max_right ..)) r
    obtain ⟨c,hC⟩:=he _ _ _ hF.post₁; obtain ⟨a,ha⟩:=he _ _ _ hF.ext₁; obtain ⟨u,hu⟩:=he _ _ _ (tipRoot (J:=Shade G) hF.post₁ zero_le_one hF.fuel); obtain ⟨v,hv⟩:=he _ _ _ (shuttle hF.ext₁); let D:=max 0 (max (max c a) (max u v)); refine ⟨V,D,hF.price,le_max_left ..,fun i=> ?_ ⟩; exact ⟨strip_mono (hC i) le_rfl (by unfold D; grind),strip_mono (hu i) le_rfl (by unfold D;grind),strip_mono (ha i) le_rfl (by unfold D;grind),strip_mono (hv i) le_rfl (by unfold D;grind)⟩ -- grind
lemma Verve (φ: W→ TileC X P p R x)(z:ℝ)(h:∀ i,upperX (φ i)≤ z) (B:Medal P G K.K P.J)(hp:Crest G P K.K m)(he:k+44≤ m)(hs:G.Simple)(hr:LocalRatio R):∃ b:ℝ,1 ≤ b∧ ∀ i,
    let A:=UA (φ i); let V:= charmSeal B A.gear
    weightsB (Yarn G P K.K R A.live A.clip 0) (k+44) (fun _=>b)∧ soot (k+24) (voteV P K.K A.live A.clip 3) b∧ soot (k+24) (voteV P K.K A.live A.clip 4) b∧ soot (k+24) (V.Fly A.live A.clip) b:=by
        obtain ⟨a,Y,hY,H,f⟩:= running X P B p R x hp; obtain ⟨c,hc⟩:= liftLoanP φ z h _ (H.earnX (k+24)).1; obtain ⟨s,hs'⟩:= liftLoanP φ z h _ (boardLoan UA (H.uni₁ 3 (k+24)) H.fuel); obtain ⟨t,ht⟩:= liftLoanP φ z h _ (boardLoan UA (H.uni₁ 4 (k+24)) H.fuel)
        choose d hd using fun i: Ask=> liftLoanP φ z h _ ((worried B hr hp hs 0 (k+44) he i).A); let V:= ∑ i, max (0:ℝ) (d i); let D:= max (max 1 V) (max c (max s t)); have he(i):d i≤D:=(le_max_right 0 _|>.trans (( Finset.single_le_sum (fun i _=>le_max_left 0 (d i)) (Finset.mem_univ i)).trans (show V ≤ D from (le_max_right ..).trans (le_max_left ..))))
        exact ⟨D, (le_max_left ..).trans (le_max_left ..),fun i=>⟨fun j=>(hd j i).tips (he j),(hs' i).tips (by unfold D;grind),(ht i).tips (by unfold D;grind),(hc i).tips (by unfold D;grind)⟩⟩
end YM.OPE.Quit.PriceZ
