import YM.LocalTaylorR2.Orbit.Trunk
import YM.LocalTaylorR2.Reel.Prod
/-! # Source template stability literature. Issue a permit for reading real history, BUT substituting logs from shadow E.
 Marker weights and gas exponents and all poses untouched. Analytic norms survive due to budget accounting below in the mixed history.Pure unit in Press. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Grafting
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Art Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes Census Itinerary
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive Candle
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m n : ℕ} {W a r σ E Λ μ s κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W} {H:Cash W s μ L Q o C T R}
section permits
variable {ι: Type*}{w x y:ι→ℝ} {S:ι→ Support c}{z:ι→ℕ}
lemma salesPlus (hx: Sales n a σ S w z κ) (hy:Sales n a σ S x z r) : Sales n a σ S (w+x) z (κ+r):=by
   refine ⟨fun i=> add_nonneg (hx.nonneg i) (hy.nonneg i),fun i=> ?_⟩
   convert! budget_plus (hx.hit i) (hy.hit i) using 1; ext j; simp only [Reserves.tariff,Pi.add_apply]; split <;> ring
lemma salesMerge (hx: Sales n a σ S w z κ) (hy:Sales n a σ S x z r) (he:∀ i, 0 ≤ y i) (hh: ∀ i,y i ≤ w i+x i): Sales n a σ S y z (κ+r):= by simpa only [one_mul] using (salesPlus hx hy).shift zero_le_one he (fun i=> by rw [one_mul]; exact hh i)
end permits
variable {q₀:Reel.Scroll G f}{H':Cash W s μ L Q o C T (Reel.bend R q₀)}
variable {ζ c' θ v d C':ℝ} {j k n':ℕ} {χ:Chi}
variable (Ξ : Utopia H j v d r C' χ) (U : Utopia H' j v d r C' χ)
variable {χHp:ℝ}
local notation "Ω" => betaF G s L
local notation "B" => radiusB s
open Reserves Tender
variable (h:1≤betaF G s L)(hz:0≤ζ)
local notation "u" => Ξ.goalsK
local notation "v'"=> (Ξ.goalsL + U.goalsL)
local notation "m₁"=> Ξ.M
local notation "vM"=> Ξ.rad
local notation "D"=> (Sum.elim (forcedExtra R) (Sum.elim (exCharge T R) fun _=>0))
variable (hL:LocalBookingsR2 ζ a Ξ) (hQ:LocalBookingsR2 ζ c' U)
include h hL hQ
lemma leasedP : Sales B Q.relative Q.ε (footprints T R Q.halo (radiusB s)) (fun i=> Ω^lease ζ c f i * rates u v' (m₁*vM) i) D (a+c'):=by
   let k(i:Alphabet c f):= Ω^lease ζ c f i
   have hk i:0≤ k i:=Real.rpow_nonneg (zero_le_one.trans h) _
   have hp:∀ i,0≤ Ξ.flair i:=Ξ.uses.nonneg
   have hv':∀ i,0≤ U.flair i:=U.uses.nonneg
   apply salesMerge hL.leases (x:=fun i=> k i*U.flair i) hQ.leases -- defeq support maps
   · intro i; apply mul_nonneg (hk i); rcases i with i|i|i
     · exact hp (.inl i)
     · exact add_nonneg (hp (.inr (.inl i))) (hv' (.inr (.inl i)))
     exact hp (.inr (.inr i))
   intro i; change k i*_≤ k i*_+k i*_; rw [← mul_add]; apply mul_le_mul_of_nonneg_left _ (hk i)
   rcases i with i|i|i; exact le_add_of_nonneg_right (hv' (.inl i))
   · rfl
   exact le_add_of_nonneg_right (hv' (.inr (.inr i)))
omit h hL hQ in
lemma stool (t:ℝ) (j:ℕ)(K:Head S): stout S Q.halo j (Q.costs L μ R.beta s C') u Ξ.goalsL t K ≤ stout S Q.halo j (Q.costs L μ R.beta s C') u v' t K:= by
   rcases K with i|i|i|i; any_goals rfl
   exact le_add_of_nonneg_right (U.uses.nonneg (.inr (.inl i)))
variable (he: a+c' ≤ Q.goal L s) include he hz
def upSize : Utopia H j v d r C' χ where
   goalsK:=u
   goalsL:=v'
   M:=m₁
   positive:=Ξ.positive
   rad:= vM
   awake:= Ξ.awake
   clock:= Ξ.clock
   active:= Ξ.active
   lives:= Ξ.lives
   uses:= (loosen (leaseNN hz) h (leasedP Ξ U h hL hQ)).raise he
   stream:= by
        intro E _ _ _ F X A' b z y Z hx hk ht hm hv hC f k i hB
        exact (Ξ.stream E F X A' b z y Z hx hk ht hm hv hC k i hB).climb (stool Ξ U _ _ i) le_rfl
   ship:=Ξ.ship
local notation "Ξ₂" => upSize Ξ U h hz hL hQ he
lemma charters : LocalBookingsR2 ζ (a+c') Ξ₂:= by
  refine ⟨leasedP Ξ U h hL hQ,?_⟩
  intro E _ _ _ F X A' b z y Z hx hk ht hm hv hC i
  exact (hL.logsT E F X A' b z y Z hx hk ht hm hv hC i).climb (le_add_of_nonneg_right (U.uses.nonneg (.inr (.inl i)))) le_rfl
lemma atLeast (i:Molecule S)(k:ℕ): Ξ.meant i k ≤ (Ξ₂).meant i k:= by
   unfold Utopia.meant; split; · exact mul_le_mul_of_nonneg_right (prod_le_prod (fun i _=> Ξ.fares i) (fun i _=> stool Ξ U _ _ _)) (pow_nonneg (add_nonneg zero_le_one (H.positive_volume _)) _)
   rfl
variable {A B' b X y:ℝ}
lemma flares (hF:FlareW H Ξ A B' k)(hB:0≤ B'): FlareW H (Ξ₂) A B' k:= by
   refine ⟨?_⟩; intro E _ _ _ F X Y y p hζ hM hX hK hr hu hE hf hy m
   obtain ⟨W,h,H0,hv⟩:= hF.tents E F X Y y p hζ hM hX hK hr hu hE hf hy
   exact ⟨W,h,H0.trans (mul_le_mul_of_nonneg_left (atLeast Ξ U (by assumption) hz hL hQ he _ _) hB),hv⟩
-- mk New N+ :: combine
omit hL in
abbrev teen (N:Captain H j C' d v X A b r B' y k χ) (hL:LocalBookingsR2 ζ a N.conduit) : Captain H j C' d v X A b r B' y k χ := {N with
   conduit:= upSize N.conduit U h hz hL hQ he
   oboe:= ⟨N.oboe.conduit,N.oboe.mode,flares N.conduit U h hz hL hQ he N.oboe.delta N.balance,N.oboe.flow⟩ }
end YM.LocalTaylorR2.Grafting
