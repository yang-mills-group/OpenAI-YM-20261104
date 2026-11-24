import YM.LocalTaylorR2.Exponent.Shill
import YM.LocalTaylorR2.Reel.Pend

/-!
 # For powers of the kept Burke interpolation. Budget at one real Captain. Version used in vacc readout and marked aperture later. Same Tide.Q costs. No post masks live. Use Even-Extension half typical chamber.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Exponent
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
variable {j k n l p m:ℕ} {g v d A D x y β:ℝ} {χ:Chi}
open PhysicalNext PhysicalNext.Repeat Greenbelt Reel Charge Tender Candle
abbrev Bevy (T:Tube G S) := LogIndex c f → Port.Test T
def replay (Φ Ξ:Bevy T) (x:ℝ): Bevy T:= Φ+x • (Ξ-Φ)
variable {Ψ Ξ: Bevy T} {V: Molecule S} {i : LogIndex c f}
def Pop' (H:Cash W s μ L Q o C T R)(A : Support c): Submodule ℝ (Port.Test T) where
  carrier := {f':Port.Test T | Port.Burst H A f'}
  zero_mem' := Port.Burst.fixed _
  add_mem' := fun hg hk=> Port.Burst.plus hg hk
  smul_mem' := fun x _ h=> (Port.Burst.fixed x).times h
lemma population (h : Port.Burst H (H.supportP (identityLog i)) (Ψ i))(hp:Port.Burst H (H.supportP (identityLog i)) (Ξ i)) {ι :Type*}(U:ι→ℝ) (x:ℝ):
    Filled (Pop' H (H.supportP (identityLog i))) 1 U (fun p=> replay Ψ Ξ (U p*x) i):=by
    let Y:= Pop' H (H.supportP (identityLog i)); let u:= x • (Ξ i-Ψ i)
    have hp': u∈ Y:= Y.smul_mem _ (Y.sub_mem hp h); have ht:= (Filled.steady (P:=Y) (Ψ i) h).adds (Filled.shoots (w:=U) 1 le_rfl u hp')
    refine Eq.mp (congr_arg (Filled Y 1 U) (?_ : _ = _)) ht
    funext t; dsimp only [Pi.add_apply,replay,u]; rw [pow_one,smul_smul]; rfl
variable (Ξ:Bevy T)(H)
def rafters (q:Paint V k):Port.Test T:= fun F X w=>∏ i:↥(logs V), Series.mono (Series.rank (q i)) (Ξ i.val F X w)
lemma cups (q:Paint V k)(h: chooseSlot q≠ Candle.perch k): Mesh.warm H Ξ q=rafters Ξ q:= funext fun _=> funext fun _=> funext fun _=> Finset.prod_congr rfl (fun _ _=> Mesh.lights h ..)
lemma glow (q:Paint V k)(s:Support c)(he:H.unionP V ⊆ s)(h:∀ i∈logs V,Port.Burst H (H.supportP (identityLog i)) (Ξ i)): Port.Burst H s (rafters Ξ q):=by
  have hp {g:Port.Test T} (hg:Port.Burst H s g)(k:ℕ): Port.Burst H s (fun F X w=> (g F X w)^k):=by
    induction k with
    | zero => simp_rw [pow_zero]; exact Port.Burst.fixed 1
    | succ k ih=> simp_rw [pow_succ]; exact ih.times hg
  refine Port.Burst.product _ _ ?_; intro i hi; simp_rw [Series.mono,div_eq_mul_inv]
  exact (hp ((h _ i.property).mono ((subset_biUnion_of_mem H.supportP ((log_occ _).1 i.property)).trans he)) _).times (Port.Burst.fixed _)
variable {r B b t y R' C':ℝ}
structure Lodestar (H:Cash W s μ L Q o C T R) (p:ℕ) (B:ℝ)(U:Utopia H j v d r C' χ) (Φ:Bevy T):Prop where
  love : ∀ i, Port.Burst H (H.supportP (identityLog i)) (Φ i)
  income : ∀ i Y, H.supportP (identityLog i) ⊆ Y → Rates H Y j p 1 B v d χ (Φ i) (U.goalsL i) (r*spanW T R (radiusB s) Q.halo (identityLog (S:=S) i))
variable {U:Utopia H j v d r C' χ}
variable (ht: Lodestar H p B U Ξ)
include ht
lemma tall (hp:1≤B)(q:Paint V k)(Z:Molecule S)(hV: V⊆Z)(hG:troupe T R Q.halo (radiusB s) Z)(hT:inserts q ≤ k)(h:1≤b): Rates H (H.unionP Z) j p k B v d χ (rafters Ξ q) (forge U b q) (2*r*(k+3:ℝ)*(1+H.shapeW Z)):=by
 apply Rates.earns H _ hp hT
 let u i:= spanW T R (radiusB s) Q.halo i; let t(i:↥(logs V)):= u (identityLog i.val); let e:= λ (i:↥(logs V))=> U.goalsL i.val
 have hr :1≤r:= U.active; have hx (i:Head S) :0 ≤ u i:= by rcases i with i|i; exact zero_le_one; exact add_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
 have hv (i:↥(logs V)):0≤ e i:= Tender.logN ..
 intro E _ _ _ F X V' z w x t' hX hK hM hχ hF hz; let D:= glacial X (H.unionP Z) t' R.beta (o.ξ/2) B p
 let c i:= Series.rank (q i); have hh :1≤ D:= frozenWide _ _ _ hp
 have hT(i:↥(logs V)): Brush j (b*(e i*D)^c i) ((r*(k+3:ℝ))*t i) (fun x=> Series.mono (c i) (Ξ i.val F (vary X (V' x)) (w x))) x:=by
    have hz := ht.income i (H.unionP Z) (subset_biUnion_of_mem H.supportP (hV ((log_occ _).1 i.property))) E F X V' z w x t' hX hK hM hχ hF hz; rw [pow_one] at hz
    let v:=((c i).factorial:ℝ)⁻¹; have hci:0≤r*t i:=mul_nonneg (zero_le_one.trans hr) (hx _); have hs:=hv i
    have h:= (Series.power hz (c i)).smul v; refine (h.climb ?_ ?_).shimmy (Eventually.of_forall fun y=> (show _ from (by change Series.mono (c i) _= v*_; unfold v Series.mono; ring)))
    · apply mul_le_mul_of_nonneg_right _ (pow_nonneg (mul_nonneg hs (zero_le_one.trans hh)) _); apply le_trans _ ‹1≤ b›; rw [Real.norm_of_nonneg (by unfold v; positivity : 0≤ v)]; exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos _)
    change r*t i*(c i:ℝ)≤r*(k+3:ℝ)*t i; rw [mul_right_comm r (↑k+3:ℝ)]; refine mul_le_mul_of_nonneg_left (?_ : (c i:ℝ) ≤ k+3) hci
    have hV : ((q i).val:ℝ) ≤ k:=by exact_mod_cast Nat.le_of_lt_succ (q i).isLt
    change (((q i).val+1:ℕ):ℝ) ≤ _; push_cast; linarith
 have hl: (logs V).image identityLog ⊆ Z:= image_subset_iff.mpr (fun i hi=> hV ((log_occ i).1 hi))
 have hN: ∑ i:↥(logs V),t i ≤2*H.shapeW Z:= by
    unfold t; rw [show (∑ i:↥(logs V),u (identityLog i.val))=(∑ i∈logs V,u (identityLog i)) from Finset.sum_attach (f:=fun i=> u (identityLog (S:=S) i)) _]; rw [← sum_image (f:=u) (fun _ _ _ _ he=> scenic_inj he)]; exact (sum_le_sum_of_subset_of_nonneg hl (fun i _ _=>hx _)).trans (Utopia.worthy Z hG)
 refine (Brush.all_prod univ _ _ _ (fun i _=> hT i)).climb ?_ ?_
 · apply le_of_eq; unfold forge inserts; rw [← Finset.prod_pow_eq_pow_sum,← Finset.prod_mul_distrib]; refine prod_congr rfl fun i hi=>?_ ; unfold c D e; ring
 rw [← Finset.mul_sum]; apply (mul_le_mul_of_nonneg_left hN (by positivity : 0≤r*(k+3:ℝ))).trans; nlinarith only [mul_nonneg (b:=(k:ℝ)+3) (zero_le_one.trans hr) (by positivity)]
end YM.LocalTaylorR2.Exponent
