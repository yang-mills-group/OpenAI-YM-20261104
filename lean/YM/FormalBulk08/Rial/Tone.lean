import YM.FormalBulk08.Rial.Hear

/-! Exact linear orientation proof for section. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Rial
open Filter Set Function Lattice Laurent Wilson Exterior Stationary
open Orb Reef Jets Lava Lotus Mesa Gorge Shore City Kemp Rift Wine Pose PowerSeries Wick
open Planned.PrimaryIntegral295 Place Carrier Film Labels Source Source.Drops Next.Foundations Dawn
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical Matrix
variable {G : Gauge} {d D k:ℕ} {I: Type} {F:Frame G d} (T:SectionData F)(H:Hol G)(hp:T.Sound H)(hb:Bid.pop T)(s:Signed)

lemma flags_sum (S:Finset I)(Q:I→Anthem D G)(a:Loc G 1)(h:∀ i∈S,Wade a (Q i) k)(p:Dawn.Studio D)(n:Side): Wade a (∑ i∈S,Q i) k ∧ Kemp.banner k ((∑ i∈S,Q i) p) n=∑ i∈S,Kemp.banner k (Q i p) n:=by
    induction S using Finset.induction with
    | empty=>simp only [Finset.sum_empty,Pi.zero_apply]; exact ⟨wade_zero,banner_zero ..⟩
    | @insert i S he ih=> obtain ⟨hz,H⟩:=ih (fun i hi=>h i (Finset.mem_insert_of_mem hi)); have hp:=h _ (Finset.mem_insert_self ..); rw [Finset.sum_insert he,Finset.sum_insert he]; constructor; exact hp.add hz; change Kemp.banner _ ((Q i) p+((∑ i∈S,Q i) p)) n=_; rw [banner_add k _ _ n (hp.summable _) (hz.summable _), H]

lemma scalar_paste (c : ℝ){I : Type}[Fintype I](f : Jets.Rays I→ℝ)(h:ContDiffAt ℝ ∞ f 0) : PowerSeries.C (MvPolynomial.C c) * paste f=paste (c • f) := by
   rw [←paste_flat (I:=I) c, ←paste_mul _ f contDiffAt_const h]; congr
lemma coatG (n:Side)(j:F.Index) : ContDiffAt ℝ ∞ (fun x:Jets.Rays (wire G n)=> (T.places (copy F j) 0 (input _ _ x)).re) 0:= by
   simp_rw [trueLamp]; exact (lights_diff T j).contDiffAt.comp _ (contDiffAt_pi.mpr fun j=>contDiffAt_apply ..) |>.of_le le_top

include hp
lemma assemblage (n:Side)(u v : Config G n)(α:Site n→G.El)(i:F.Index)(he:v=Lattice.gauge α (pull s 0 u)):
   (T.places (copy F i) 0 v).re=∑ j∈family F i,(F.act s.ortho (copy F i) j).re*(T.places (copy F j) 0 u).re:= by
   rw [he,T.placed_invariant hp 0 _ _ _, T.placed_signed hp]; simp only [affine,Signed.act_zero,zero_add]
   let Q:=F.act s.ortho (copy F i)
   have ht : ∑ j∈family F i,Q j • copy F j=Q:= by
      ext1 j; have h : ∑ v: F.Index, Q v • copy F v = Q := by ext1 k; simp [copy, Pi.single_apply]
      apply congr_fun _ j; refine Eq.trans (Finset.sum_subset (Finset.subset_univ _) ?he) h
      case he=> intro k _ hk; rw [show Q k=0 from exactGuard F s i k (Ne.symm (by simpa [family] using hk)),zero_smul]
   change (T.evaluate Q _).re=_; conv_lhs=> rw [←ht];
   simp only [SectionData.evaluate,map_sum,map_smul,Complex.re_sum]; apply Finset.sum_congr rfl; intro j hj; rw [show Q j= ↑(F.act s.ortho (copy F i) j).re from (realTurn F s _ _).symm]; simp [smul_eq_mul]; left; simp [SectionData.places, SectionData.evaluate]

variable (i: Letter F)(hd:d+1≤D)(o:Loc G 1)
-- matrix times column contribution y? F W=sum origins coefficient line `i` on input x.
def shades := ∑ y:Letter F, launch (lariat F s y i) (sectionY T hd y)
omit hp
lemma bounds (x:Letter F) (h:lariat F s x i≠0): Pose.slots F i=Pose.slots F x:= by
    unfold lariat at h; split at h
    next he=> exact (crew_rank F s he).1.symm
    contradiction
lemma shifted_conn (y:Letter F)(p:Dawn.Studio D)(h:Crew F s y i) :
    let ξ:= Pose.pet F y; let η:=Pose.pet F i
    ∀ (u:Chapel.upper η.val≤ D)(v:Chapel.upper ξ.val≤ D), Dawn.notch η u (Dawn.froth s D p) = Dawn.tone ξ s* Dawn.notch ξ v p := by
   intro ξ η u v; have he:breeze η.val s⁻¹=ξ.val:=congr_arg Subtype.val ((crew_flip F s).mp h).1.symm; rw [spun]; simp [he]
include hb o
lemma torsion (p:Dawn.Studio D)(n:Side):
    let l:=Pose.slots F i; let q:=Dawn.froth s D p; let θ:= notch (pet F i) (show Chapel.upper _ ≤ D from ((paper_fits _).trans (Nat.le_trans d.le_succ hd))) q
    PowerSeries.X^l*Kemp.banner l ((shades T s i hd) p) n=paste (fun z:Jets.Rays (wire G n)=> ∑ j∈family F (mint F i), θ*(F.act s.ortho (copy F (mint F i)) j).re*(T.places (copy F j) 0 (input _ _ z)).re):= by
    intro l q θ; let S:=mates F s⁻¹ i; let W (y:Letter F):= launch (lariat F s y i) (sectionY T hd y)
    have he : shades T s i hd = ∑ y∈S,W y:= by
       symm; refine Finset.sum_subset (Finset.subset_univ _) ?_
       intro y _ hy; have hp: lariat F s y i=0:= if_neg (fun hx=>hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (crew_flip F s).mp hx⟩))
       unfold W; rw [hp,← map_zero (PowerSeries.C (R:=ℝ)),launch_C,zero_smul]
    have hz (y:Letter F) (hy:y∈S): Crew F s y i:= (crew_flip F s).mpr ((Finset.mem_filter.mp hy).2)
    have hA y (h:y∈S): Wade o (W y) l:= by have H := ((report T hd o y).launch (lariat F s y i)); rw [(crew_rank F s (hz y h)).1] at H; exact H
    rw [he,(flags_sum _ W o hA p n).2,Finset.mul_sum]
    let P (j:F.Index) : Jets.Rays (wire G n) →ℝ := (θ * (F.act s.ortho (copy F (mint F i)) j).re) • fun z:Jets.Rays (wire G n)=> (T.places (copy F j) 0 (input G n z)).re
    have hh y (hy:y∈S): X^l*Kemp.banner l (W y p) n=paste (P (mint F y)) := by
       have hk:=hz y hy; let w:= mint F y; have hu:Pose.slots F y=l:= (crew_rank F s hk).1;unfold W; rw [←hu, banner_mul (report T hd o y),lariat,if_pos hk, worm,PowerSeries.map_C]; unfold sectionY;
       rw [banner_coin]; -- factor
       let t(z:Jets.Rays (wire G n)):= (T.places (copy F w) 0 (input _ _ z)).re
       let c:= Dawn.tone (pet F y).val s; let Z:= Dawn.notch (pet F y) (show Chapel.upper _≤D from ((paper_fits _).trans (Nat.le_trans d.le_succ hd))) p
       let κ:= (F.act s.ortho (copy F (mint F i)) w).re; let U:=Kemp.banner (Pose.slots F y) (paperback T w) n
       change X^_ * (C (MvPolynomial.C (c*κ)) * (C (MvPolynomial.C Z)* U))= paste ( (θ*κ) • t)
       rw [← scalar_paste _ t (coatG T n w), ← show X^(Pose.slots F y)*U=paste t from (debut T w (Pose.slots F y) le_rfl n hb), show θ=c*Z from shifted_conn s i y p hk _ _]; simp only [map_mul]; ring
    refine Eq.trans (Finset.sum_congr rfl hh) ((swims F s⁻¹ i (fun j=>paste (P j))).trans ?_)
    symm; have hz: paste (∑ j∈family F (mint F i),P j)=_:= Jets.garter P (family F (mint F i)) (fun j _=> (coatG T n j).const_smul (θ*(F.act s.ortho (copy F (mint F i)) j).re))
    rw [←hz]; apply congr_arg; funext z; rw [Finset.sum_apply];rfl
include hp
lemma Harmony : Son (shades T s i hd) (sectionY T hd i) (Pose.slots F i) s:=by
    intro n p I inst a b t ha hb' hx hg hr hw hR
    let l:=Pose.slots F i; let q:= froth s D p; let θ:= Dawn.notch (pet F i) (show Chapel.upper _≤D from ((paper_fits _).trans (Nat.le_trans d.le_succ hd))) q; let W := _root_.YM.FormalBulk08.Kemp.banner l (sectionY T hd i q) n
    let K:= _root_.YM.FormalBulk08.Kemp.banner l (shades T s i hd p) n
    let P (j:F.Index) (z: Jets.Rays (wire G n)):= (T.places (copy F j) 0 (input G n z)).re
    let v:= mint F i; let L j:= (F.act s.ortho (copy F v) j).re
    let J (z : Jets.Rays (wire G n)):= ∑ j∈family F v, θ * L j * P j z
    let Y := θ • P v
    have hz: X^l*K=paste J:=torsion T hb s i hd o p n
    have he:X^l*W=paste Y:= by unfold W sectionY; rw [banner_coin,mul_left_comm,show X^l*Kemp.banner l (paperback T v) n=paste (P v) from debut T v l le_rfl n hb]; exact scalar_paste θ (P v) (coatG T n v)
    have hJ : ContDiffAt ℝ ∞ J 0:= ContDiffAt.sum (fun j _=> contDiffAt_const.mul (coatG T n j))
    have hY : ContDiffAt ℝ ∞ Y 0:= (coatG T n v).const_smul θ
    have ht : J ∘ a=ᶠ[𝓝 0] Y∘b:= by
       filter_upwards [hR] with z hz; change J _=θ*P v _; rw [show P v (b z)=_ from assemblage T H hp s n _ _ _ v hz,Finset.mul_sum]; unfold J; exact Finset.sum_congr rfl fun j _=>mul_assoc ..
    apply mul_left_cancel₀ (pow_ne_zero l PowerSeries.X_ne_zero)
    have hy (f:Jets.Rays I→Jets.Rays (wire G n)) (Q:Pap (wire G n)) : X^l * roam ℝ (motor f) Q = roam ℝ (motor f) (X^l*Q):= by rw [map_mul,map_pow,show roam ℝ _ X=X from Series.change_X _]
    change X^l*roam ℝ _ K=X^l*roam ℝ _ W; rw [hy a,hy b,hz,he,← paste_steps _ _ hJ (hx.of_le le_top) ha,←paste_steps _ _ hY (hg.of_le le_top) hb']; exact paste_replace ht
end YM.FormalBulk08.Rial
