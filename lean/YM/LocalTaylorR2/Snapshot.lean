import YM.LocalTaylorR2.Tolls
/-!
# Charge the local inserted logs in the same physical recoil norm.

All bounds at actual probes, on whole shapes. Supports may be bigger
than one head, and the same argument works before attaching other
(non-unit test) decorations. These purchases are then needed in the
second cluster sum.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves
variable {j k n l : ℕ} {v r d A D x C' θ ζ c':ℝ} {U : Molecule S} {χ : Chi}

def Sees (_H : Cash W s μ L Q o C T R) (j : ℕ) (v d:ℝ) (χ:Chi) (K : Port.Test T) (M q:ℝ) :=
    ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (F:Forest S.ratio) (X:Coat T F)
      (V:E→ Config G c) (u:E→ Directions G f) (z:E→ Air f G) (x:E) (w:Air f G), X.x=s → X.width=o.K → X.manifest → X.χ=χ → Mode V x j v →
      Clutch X w o.a R.beta d x j V u z → Brush j M q (fun y=>K F (vary X (V y)) (z y)) x
namespace Sees
variable (H : Cash W s μ L Q o C T R)
variable {θ' C'' : ℝ} {g g' : Port.Test T}
lemma times (h:Sees H j v d χ g C' θ) (h':Sees H j v d χ g' C'' θ'): Sees H j v d χ (fun F X w=>g F X w*g' F X w) (C'*C'') (θ+θ'):= by
  intro E _ _ _ F X V u z x w he hk hm hX hv hw
  exact (h E F X V u z x w he hk hm hX hv hw).paints (h' E F X V u z x w he hk hm hX hv hw)
lemma collect {ι:Type*} {g:ι→ Port.Test T} {K y:ι→ℝ} (U:Finset ι) (h:∀ i∈U,Sees H j v d χ (g i) (K i) (y i)): Sees H j v d χ
    (fun F X w=> ∏ i∈U, g i F X w) (∏ i∈U,K i) (∑ i∈U,y i):= fun E _ _ _ F X V u z x w he hk hm hX hv hw=> Brush.all_prod U _ K y fun i hi=> h i hi E F X V u z x w he hk hm hX hv hw
lemma climb (h:Sees H j v d χ g C' θ) (hp:C'≤C'') (hz:θ≤θ'):Sees H j v d χ g C'' θ':=fun E _ _ _ F X V u z x w he hk hm hX hv hw=> (h E F X V u z x w he hk hm hX hv hw).climb hp hz
end Sees
-- tied to Local prescriptive argument. No sharpness assumed; produced by LocalBookingsR2.
namespace Charge
variable (M: StoresR2 H j v d A D k x n χ) {Ξ:Utopia H j v d r C' χ}
variable (B:LocalBookingsR2 ζ c' Ξ)
include B
lemma logSees (i:LogIndex c f):Sees H j v d χ (weightLog H i) (Ξ.goalsL i) (r*spanW T R (radiusB s) Q.halo (identityLog (S:=S) i)):= by
  intro E _ _ _ F X V u z x Z hx he hm hk hπ hf
  have hU:= B.logsT E F X V u z x Z hx he hk hm hπ hf i
  unfold Coat.B at hU; rw [hx] at hU
  apply hU.shimmy; filter_upwards [hf.patch] with y hy
  let Y:= vary X (V y); change weightLog H i F Y (z y)=_
  unfold Port.weightLog; rw [show worldZ Y _ _= u y from hf.moving y]
  have ht : Room P S T Y.x := hx.symm ▸ H.laws.data.room
  have hv : Intake P T Y.x R:= hx.symm ▸ H.laws.intake
  have hq:= (plastic hy hf.pulse).reeled ht W Q.table ∅ Q.halo hv (identityLog i) (z y)
  exact Real.exp_injective (sub_left_inj.mp (show Real.exp _-1=Real.exp _-1 from hq))

-- no validity requirements on financing witness hFac at p=0, actual obtained via allowance for all

def Allows (k j : ℕ) (u:ℝ) := ∀ (i:Series.Letter k) (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f:E→ℝ) (x:E) (v d:ℝ), Brush j v d f x → v≤1 → Brush j (u*v^Series.rank i) (d*((k:ℝ)+3)) (Series.split i ∘ f) x
lemma lowFare (p:Paint U l) (hFac:Allows l j θ) (hv:∀ i,Ξ.goalsL i≤1): Sees H j v d χ (letters H p)
    (∏ i:↥(logs U), (θ* (Ξ.goalsL i.val)^Series.rank (p i)))
    (r*(l+3:ℝ)*(∑ i∈logs U, spanW T R (radiusB s) Q.halo (identityLog (S:=S) i))) := by
  have hf (i:↥(logs U)): Sees H j v d χ (fun F X w=> Series.split (p i) (weightLog H i.val F X w)) (θ* (Ξ.goalsL i.val)^Series.rank (p i))
      ((r*spanW T R (radiusB s) Q.halo (identityLog (S:=S) i.val))*((l:ℝ)+3)):= by
    intro E _ _ _ F X V u z x w he hk hm hX hz hD
    exact hFac (p i) E _ _ _ _ (logSees B i.val E F X V u z x w he hk hm hX hz hD) (hv _)
  apply (Sees.collect H univ (fun i (_:i∈univ)=> hf i)).climb H le_rfl
  refine le_of_eq ?_; rw [← Finset.sum_attach (logs U), Finset.mul_sum]; exact sum_congr rfl fun i _=> by ring

lemma sumSpeed (p:Paint U l) {U':Molecule S} (hu: U⊆U') (hq:troupe T R Q.halo (radiusB s) U') (hFac:Allows l j θ) (hv:∀ i,Ξ.goalsL i≤1): Sees H j v d χ (letters H p)
    (∏ i:↥(logs U), (θ* (Ξ.goalsL i.val)^Series.rank (p i))) (2*r*(l+3:ℝ)*(1+H.shapeW U')):= by
  have hle: (logs U).image identityLog ⊆ U':= image_subset_iff.mpr (fun i hi=> hu ((log_occ i).1 hi))
  apply (lowFare B p hFac hv).climb H le_rfl
  let f:= spanW T R (radiusB s) Q.halo
  have hf (i:Head S) : 0≤ f i:= by
    rcases i with i|i; exact zero_le_one
    exact add_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hx : ∑ i∈logs U, f (identityLog i) ≤ 2*H.shapeW U':= by
    rw [← sum_image (f:=f) (fun _ _ _ _ he=> scenic_inj he)]
    exact (sum_le_sum_of_subset_of_nonneg hle (fun i _ _=> hf i)).trans (Utopia.worthy _ hq)
  have hr:1≤r:= Ξ.active
  apply le_trans (mul_le_mul_of_nonneg_left (hx.trans (show _≤2*(1+H.shapeW U') by linarith)) (show 0≤r*(l+3:ℝ) by positivity))
  apply le_of_eq; ring
omit B
include M
lemma holds (K:Port.Test T) {M':ℝ} (hM:0≤ M') (hq:0≤θ) (p : Molecule S) (ht:Sees H j v d χ K M' (θ*(1+H.shapeW p))) : IntegrandCost H (H.unionP p) K j A v
    (M'*(x*(1+D+θ)^j)*(1+H.shapeW p)^(n+j)) χ := by
  refine ⟨?_⟩; intro F X hx hk hm hX hU E _ _ _ V y hV hy m I
  let S':= 1+H.shapeW p; let a:=M'*(1+D+θ)^j*S'^j
  have hS:1≤S':=le_add_of_nonneg_right (H.positive_volume _); have hD : 0≤D:=M.fuel
  have ha:a≥0:=by unfold a; positivity
  let f(z:Air f G):=facescale I z^(k*j)
  obtain ⟨hh',hv'⟩:= M.curtain p F X hx hX hk hm a ha 1 zero_le_one Set.univ MeasurableSet.univ (by simp)
  simp only [Set.indicator_univ,mul_one] at hh' hv'
  refine ⟨fun z=> a*f z.2, hh', hv'.trans_eq ?_,?_⟩
  · unfold a S'; ring
  intro ⟨w,z⟩; let Y:= X.wrapY w; obtain ⟨hw,hq'⟩:= M.flight F Y hx hX hk hm z E V y hy hV
  have hs := ht E F Y V _ _ y z hx hk hm hX hV hw
  apply ((hq' p|>.paints hs).trim).climb _ le_rfl; rw [one_mul]; let K':=facescale I z
  have he:1≤K':= (Flux.expenses I z).1
  have H0 : 0 ≤ D*K'^k:=by positivity
  have hy':(1+(D*K'^k+θ*S'))≤(1+D+θ)*S'*K'^k:=by
    have hv:= one_le_mul_of_one_le_of_one_le hS (one_le_pow₀ (n:=k) he)
    have hB:K'^k≤ S'*K'^k:= le_mul_of_one_le_left (by positivity) hS
    have hL:S' ≤ S'*K'^k:= le_mul_of_one_le_right (zero_le_one.trans hS) (one_le_pow₀ he)
    nlinarith only [hv,mul_le_mul_of_nonneg_left hB hD,mul_le_mul_of_nonneg_left hL hq]
  exact le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0≤1+(D*K'^k+θ*S') by positivity) hy' j) hM) (le_of_eq (by unfold a f; unfold K'; simp only; rw [pow_mul,mul_pow, mul_pow]; ring))
end Charge
end YM.LocalTaylorR2
