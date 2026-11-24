import YM.Juniper.Bright.Dusk
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Alto
/-!
 # Unforced part high-order re-expression: connect to SMALL environments certified

 This computation is algebra with explicit hypotheses on same Ph.D. integration output.
 Uses Slide to avoid solving a Laurent system explicitly: charges can be rebased onto
 local (high-height but fixed size budget) mirrored toroidal capsules. Their shape
 includes original V paths. Cannot re-express at post-seam Shutter without further
 theorem. mask attachment payments in `Succor`.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Bright
open ConnectedActivityE6 Blaze Silica March Captain PhysicalNext PhysicalNext.Repeat Height
open Filter Function Set Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Shoot SliceRows Control Pulse Mask Raw Matter Pond Gas Ursell Trees Reserves Greenbelt Deck Mint Shield Stained
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Extra.Iteration Animals Corona Match Song Meadow Refrain Slide
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G: Gauge} {c f L : Side} {P:Teller G}
      {W μ x C s t δ K u:ℝ} {χ:Chi}{Q: ConnectedActivityE6.Target G P} {o:Target.Order G W}
      {j n k l m b w z:ℕ} {S : StepData c f} {T:Tube G S} {R: Rep G f}
   {I:Cash W x μ L Q o C T R}{B:BudgetPoint}{V : Config G c}
local notation "v"=> plusone I (blank I) χ s
variable (B I s χ V)
def earnAll (Z : Finset (Magazine I)) (i:Site c)(V:Config G c): ℝ := ∑ j∈lantern I Z, garnerAt I B i j *((posting B I).read v|>.regularOccurrence B j V)
local notation "W₁"=> leftOver
lemma additives {δ K:ℝ} (H:Finset (Magazine I)) (hp : Collection.Local (Song.posting B I) B v δ K) :
    ((posting B I).read v).additive B V=((posting B I).read (W₁ H s χ)).additive B V+∑ i:Site c,earnAll s χ I B H i V:= by
  let t i:= ((posting B I).read v).regularOccurrence B i V; let V' i:=((posting B I).read (W₁ H s χ)).regularOccurrence B i V
  let k i:= if i∈ lantern I H then t i else 0; have h : V'=t-k:= by
    funext i; change masked _ _ ((W₁ H s χ).logRead i) V=t i-k i; rw [leftover_value]
    unfold k; split; next he => rw [sub_self]; simp [masked]
    next he=> rw [sub_zero]; rfl
  have ht: ∑ i:Site c,earnAll s χ I B H i V=∑ z∈lantern I H,t z:= by unfold earnAll; rw [Finset.sum_comm]; exact sum_congr rfl fun i _=> by rw [← sum_mul,paysOne, one_mul]
  have hk: HasSum k (∑ z∈lantern I H,t z):= by
     convert hasSum_sum_of_ne_finset_zero (s:=lantern I H) (f:=k) (fun _ hi=> if_neg hi) using 1; exact (sum_congr rfl (fun i hi=> if_pos hi : ∀ i∈ lantern I H,k i=t i)).symm -- syntax
     infer_instance
  change (∑' i,t i)=(∑' i,V' i)+_; have hx: ∑' i,V' i=_:= h.symm ▸ (show ∑' i,(t - k) i=_ from ((show Summable t from Roof.Embrasure.series _ _ hp V).hasSum.sub hk).tsum_eq); rw [hx,ht]; exact (sub_add_cancel ..).symm
variable (Y: Shelf I n)
local notation "t'" => selection Y k B.B m
local notation "θ"=> living χ I k Y B.B m s
lemma mirrors (k m:ℕ): Trio.Mirrors (living χ I k Y B.B m s) := fun _ y z _=> Meadow.astrolabe _ _ _ (y,z)
variable {I χ B s V} {Y}
lemma normal (b:Finset (Magazine I)) (I':Site c) (h:flags B.threshold V=∅) : earnAll s χ I B b I' V=∑ j∈lantern I b, Meadow.garnerAt I B I' j * (v).logRead j V:= by unfold earnAll; refine Finset.sum_congr rfl fun i _=> congr_arg (_*·) ?_; exact masked_eq _ _ _ _ (by unfold Healthy; rw [h]; simp)
-- projector identity in all-large env
lemma normal_here {κ L₁:ℝ} (σ :ℝ) (h: Collection.Local (posting B I) B v κ L₁) (hT: S.push R.beta R.eval V=earlyValue (posting B I) T.down T.low B v R.beta σ s V)
     {σ' C' Λ:ℝ}(hp:T.down.Bounds T.low σ' C' Λ)(hh:flags B.threshold V=∅) :
    Real.log (S.push R.beta R.eval V)+R.beta*Precision.mainTerm T.low T.down V+Precision.loop T.down V+s* Precision.secondTerm T.low T.down V=
    σ*(Fintype.card (Site c):ℝ) - ∑ i:Site c, living χ I k Y B.B m s i V - Boulevard.throng (leftOver (selection Y k B.B m) s χ).logRead V:=by
   have hq: Collection.receipt T.down T.low B V= Precision.secondTerm T.low T.down V:= VerifiedReset.allGoodPrice hp V hh
   let L:=posting B I; let h₀:= L.read (W₁ t' s χ); have ht(a): earnAll s χ I B t' a V= θ a V:= by rw [normal t' a hh,candles B, Finset.sum_apply]; rfl
   have hz:h₀.additive B V=∑' i,(leftOver t' s χ).logRead i V:=tsum_congr fun i=> masked_eq _ _ _ _ (by unfold Healthy; rw [hh]; simp)
   rw [hT]; unfold earlyValue Rep.eval Rep.exponent Collection.frozen; dsimp only
   rw [Activities.gas_one _ _ hh,mul_one, ← Real.exp_add, Real.log_exp,hq, additives s χ I B V t' h]
   simp_rw [ht]; unfold Boulevard.throng; rw [Pane.crystalline _ _ _ _ _ hh, hz]; ring

variable {Y₀:Stars→ Side}(a :Site c) (DY:ℕ) (hb:∀ i:Stars,(Y₀ i).val=2*(w+i.val))(f₀:∀ i:Stars,Trio.Offer G (Y₀ i))
def difference (a:Site c)(V:Config G c):=earnAll s χ I B t' a V - θ a 1 - Trio.unearned B hb DY (Trio.rip f₀) a V -- notation shadow?
-- k m shadow issue. check
lemma arranged (H:Collection.Local (posting B I) B v K δ) :
     ((posting B I).read v).additive B V=((posting B I).read (leftOver t' s χ)).additive B V + (Fintype.card (Site c):ℝ)* θ 0 1 + (∑ i:Site c, masked B.threshold (neighbors DY i) (Trio.ornament hb f₀ i) V)+ ∑ i:Site c,Bright.difference (χ:=χ) (s:=s) (B:=B) (m:=m) (k:=k) (Y:=Y) DY hb f₀ i V:=by
  have h i: θ i 1= θ 0 1:= by
    simpa [Lattice.affine, VerifiedReset.pull_one_field] using ((mirrors s χ I B Y k m) 0 1 i (1: Config G c)).symm
  rw [additives s χ I B V _ H]; unfold Trio.ornament; rw [Trio.parade]
  unfold Bright.difference; simp_rw [h]; rw [sum_sub_distrib,sum_sub_distrib,sum_const,nsmul_eq_mul,card_univ]; ring
variable {a hb f₀}
lemma scrub (hk:0<l)(hp:4*l+16 ≤ c.val)(hB:B.B=radiusB x)
    (hA:Shelf.terrace n k≤l) (hC:2*radiusB x≤ l) (ha:2*l≤w)(hs: w+4 ≤ DY)(hr:2*DY ≤ b)
    (h:Trio.CompatibleP B l θ f₀) (hv:Healthy B.threshold (neighbors b a) V) : Bright.difference (χ:=χ) (s:=s) (B:=B) (m:=m) (k:=k) (Y:=Y) DY hb f₀ a V=0:=by
   refine sub_eq_zero.mpr ?_
   have hq:Trio.unearned B hb DY (Trio.rip f₀) a V = θ a V- θ a 1:= Trio.cruising B hb DY (Trio.rip f₀) V a hs ha hr hp hv _ (Trio.tinted θ f₀ h) hk
   refine (congr_arg (·- θ a 1) ?_).trans hq.symm
   rw [candles B, Finset.sum_apply]; unfold earnAll; refine Finset.sum_congr rfl fun i hi=> ?_; rw [Pi.smul_apply, smul_eq_mul] -- might applies differently
   by_cases hy:Meadow.garnerAt I B a i=0; · rw [hy,zero_mul,zero_mul]
   refine congr_arg _ (masked_eq _ _ _ _ (Finset.disjoint_of_subset_left ?_ hv)); exact fun x hx=> (neighbors_mem ..).2 (((neighbors_mem ..).1 ((candles_size B hB Y hA hC a i hi hy).2 hx)).trans (by omega)) -- edit
end YM.Juniper.Bright
