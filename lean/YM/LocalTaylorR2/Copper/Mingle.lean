import YM.LocalTaylorR2.King.Bayes
/-! # Mingle: paint apertures with a scalable additive discrepancy.
 Uses The argument Taylor estimate (via TRUE Engine transport) at UNSINGULAR
 masks before extracting Ili. Extrapolate without assuming analyticity of
 the masked global density in its inputs. -/
 set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Copper
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
open Charge Candle RG01.Survive Mesh
abbrev Stems {G:Gauge}{c f:Side}{S:StepData c f} (T:Tube G S) := LogIndex c f→Port.Test T
variable (Φ:Stems T)
structure Solfege (H : Cash W s μ L Q o C T R)(Ψ:Utopia H j v d r C' χ) (Φ:Stems T): Prop where
   flights (i):Kept H (H.supportP (identityLog i)) (Φ i)
   part (i):Sees H j v d χ (Φ i) (Ψ.goalsL i) (r*spanW T R (radiusB s) Q.halo (identityLog (S:=S) i))
open Reel (Scroll Strand)
variable {ψ: Reel.Scroll G f} {J:Cash W s μ L Q o C T (Reel.bend R ψ)}
variable {Ξ:Utopia H j v d r C' χ} {X:Utopia J j v d r C' χ} {ρ b:ℝ}
variable (Z:King.Engine G)(ε:ℝ) (hx:x=0)
-- amplitude g (dial *ρ^l): Y−dial * F⁻¹*(Y-Z) where F=ρ⁻ˡ. domain Cash not tied to H? choose signs to convert.
def contour (H : Cash W s μ L Q o C T R) (ψ:Reel.Scroll G f) (k:ℕ) (t:ℝ) (Z:King.Engine G): Stems T:=fun i=> Reel.sprout H ψ i-t • (Reel.sprout H ψ i-Z.plug H ψ k i)
lemma knotTop (H : Cash W s μ L Q o C T R)(ψ:Reel.Scroll G f): contour H ψ l 1 Z= Z.plug H ψ l:=by funext i; unfold contour; rw [one_smul,sub_sub_self]
lemma knotCold (H : Cash W s μ L Q o C T R)(ψ:Reel.Scroll G f): contour H ψ l 0 Z= Reel.sprout H ψ:=by funext i; unfold contour; rw [zero_smul,sub_zero]
local notation "u" => Reel.Strand.dial
local notation "Y" => fun i:Strand=> contour H ψ l (u i*ρ^l) Z
variable (hM : Crib (Z.symbol J l) X l ρ)
include hM
lemma romps (i: LogIndex c f): Reel.Filled (Reel.Pop H (H.supportP (identityLog i))) 1 u (fun z:Strand=> Y z i):=by
    let A:= Reel.Pop H (H.supportP (identityLog i)); let y:= Reel.sprout H ψ i; let g:= Z.plug H ψ l i
    have hz:y∈A:=by
       have hp:= Port.logTest J i; exact ⟨hp.links,hp.borel,hp.rotate,hp.clutch⟩
    have hg:g∈A:=by
       unfold g; rw [Z.fits H ψ J l]; have hu:= hM.kept i; exact ⟨hu.links,hu.borel,hu.rotate,hu.clutch⟩
    let f:= ρ^l • (g-y); have he z: contour H ψ l (u z*ρ^l) Z i=y+u z ^1 • f:=by unfold f g y contour; rw [pow_one,smul_smul]; rw [smul_sub,smul_sub]; abel
    exact (funext he).symm ▸ (Reel.Filled.steady y hz).adds (Reel.Filled.shoots 1 le_rfl f (A.smul_mem _ (A.sub_mem hg hz))) -- fun not Pi+
lemma guides (hp:1 ≤ρ)(hx:∀ i, X.goalsL i + X.goalsL i ≤ Ξ.goalsL i)(hg:LocalBookingsR2 ζ b X)(p:Strand): Solfege H Ξ (Y p):=by
   let a:= u p; have hf:0<ρ:=zero_lt_one.trans_le hp; let z:=a*ρ^l; have hv : |a|≤1:= abs_le.mpr p.property
   refine ⟨fun i=>(romps (H:=H) Z hM i).land p,?_⟩
   intro i E _ _ _ F Z' V w W x I h hW ht hu hP hT
   unfold contour; rw [Z.fits H ψ J l]; have he:= logSees hg i E F Z' V w W x I h hW ht hu hP hT; have hh:= hM.mark i E F Z' V w W x I h hW ht hu hP hT
   apply (he.separating (hh.smul z)).climb _ le_rfl
   have hy : ‖z‖*((ρ⁻¹)^l) ≤ 1:=by rw [Real.norm_eq_abs,show z=a*ρ^l from rfl,abs_mul,abs_of_pos (pow_pos hf _),inv_pow,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hf.ne'),mul_one]; exact hv
   apply le_trans _ (hx i); rw [mul_left_comm]; exact add_le_add_right (mul_le_of_le_one_right (Tender.logN ..) hy) _
omit hM
variable (H : Cash W s μ L Q o C T R){Ξ₀:Utopia H j v d r C' χ} (hS:Solfege H Ξ₀ Φ)
def namesP (p:Paint U l): Port.Test T:= fun F X w=> ∏ i:↥(logs U), Series.split (p i) (Φ i.val F X w)
lemma namesZero (p:Paint U l)(h: chooseSlot p=0): namesP Φ p=(1:Port.Test T):=by
   have hv : min (l+1) (inserts p)=0:= congr_arg Fin.val h
   funext F X w; unfold namesP; apply prod_eq_one; intro i hi
   have hz : (p i).val+1 ≤ inserts p:=single_le_sum (f:=fun i=> Series.rank (p i)) (fun _ _=>Nat.zero_le _) hi; omega
include hS
lemma namesKept (p:Paint U l) (M:Support c) (h:H.unionP U ⊆ M): Kept H M (namesP Φ p):= by
   refine Kept.product univ (fun i:↥(logs U)=>fun F X w=>Series.split (p i) (Φ i.val F X w)) (fun i _=> ((hS.flights i).smooth _ (Series.smooth ..)).mono ((subset_biUnion_of_mem H.supportP ((log_occ _).1 i.property)).trans h))

lemma lowFlock (p:Paint U l) (hFac:Allows l j θ) (hv:∀ i,Ξ₀.goalsL i≤1): Sees H j v d χ (namesP Φ p)
    (∏ i:↥(logs U), (θ* (Ξ₀.goalsL i.val)^Series.rank (p i)))
    (r*(l+3:ℝ)*(∑ i∈logs U, spanW T R (radiusB s) Q.halo (identityLog (S:=S) i))) := by
  have hf (i:↥(logs U)): Sees H j v d χ (fun F X w=> Series.split (p i) (Φ i.val F X w)) (θ* (Ξ₀.goalsL i.val)^Series.rank (p i))
      ((r*spanW T R (radiusB s) Q.halo (identityLog (S:=S) i.val))*((l:ℝ)+3)):= by
    intro E _ _ _ F X V u₀ z x w he hk hm hX hz hD
    exact hFac (p i) E _ _ _ _ (hS.part i.val E F X V u₀ z x w he hk hm hX hz hD) (hv _)
  apply (Sees.collect H univ (fun i (_:i∈univ)=> hf i)).climb H le_rfl
  refine le_of_eq ?_; rw [← Finset.sum_attach (logs U), Finset.mul_sum]; exact sum_congr rfl fun i _=> by ring

lemma tallFlock (p:Paint U l) {U':Molecule S} (hu: U⊆U') (hq:troupe T R Q.halo (radiusB s) U') (hFac:Allows l j θ) (hv:∀ i,Ξ₀.goalsL i≤1): Sees H j v d χ (namesP Φ p)
    (∏ i:↥(logs U), (θ* (Ξ₀.goalsL i.val)^Series.rank (p i))) (2*r*(l+3:ℝ)*(1+H.shapeW U')):= by
  have hle: (logs U).image identityLog ⊆ U':= image_subset_iff.mpr (fun i hi=> hu ((log_occ i).1 hi))
  apply (lowFlock Φ H hS p hFac hv).climb H le_rfl
  let f:= spanW T R (radiusB s) Q.halo
  have hf (i:Head S) : 0≤ f i:= by
    rcases i with i|i; exact zero_le_one
    exact add_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hx : ∑ i∈logs U, f (identityLog i) ≤ 2*H.shapeW U':= by
    rw [← sum_image (f:=f) (fun _ _ _ _ he=> scenic_inj he)]
    exact (sum_le_sum_of_subset_of_nonneg hle (fun i _ _=> hf i)).trans (Utopia.worthy _ hq)
  have hr:1≤r:= Ξ₀.active
  apply le_trans (mul_le_mul_of_nonneg_left (hx.trans (show _≤2*(1+H.shapeW U') by linarith)) (show 0≤r*(l+3:ℝ) by positivity))
  apply le_of_eq; ring
end YM.LocalTaylorR2.Copper
