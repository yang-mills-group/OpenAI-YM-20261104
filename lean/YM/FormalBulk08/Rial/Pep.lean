import YM.FormalBulk08.Rial.Pad

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Rial
open Filter Set Function Lattice Laurent Wilson Exterior Stationary
open Orb Reef Jets Lava Lotus Mesa Gorge Shore City Kemp Rift Wine Pose PowerSeries Wick
open Planned.PrimaryIntegral295 Place Carrier Film Labels Source Source.Drops Next.Foundations
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge} {S:Finset Cover} {d:ℕ} {F: Frame G d} {I:Type*} {j u l r D:ℕ} {η A : ℝ}
lemma hymn_vanish (r:ℕ):hymn (0 : Tile (SpotC S G) r)=0:=by ext1; simp [hymn]
lemma hymn_tor (p:Tile (SpotC S G) r) (n:Side): sieve n (hymn p)=cores (Lotus.drip n ∘ chamber S G) p:= by
    funext v; rw [sieve_i]; rw [cores_here];
    let f (u:chain (SpotC S G) r):=chamber S G ∘ u
    let g u:= if Lotus.drip n ∘ u=v then hymn p u else 0
    have hx: Summable g := by
       let M:= Finset.univ.image f; refine summable_of_ne_finset_zero (s:=M) (fun i hi=>?_); unfold g; split_ifs; swap;· simp
       exact hymn_floor _ i fun a he=>hi (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,he⟩)
    have he : Function.support g ⊆ Set.range f := by
       intro u hu; change g u≠0 at hu; by_contra hv; apply hu; unfold g; split; exact hymn_floor p u (fun i hh=> hv ⟨i,hh⟩); rfl
    refine Eq.trans (b:=∑' u,g u) ?_ ?_; · apply tsum_congr; intro i; unfold g; congr
    rw [← Function.Injective.tsum_eq (show Injective f from fun i j h=> funext fun k=> chamber_safe _ _ (congr_fun h k)) he,tsum_fintype]; apply Finset.sum_congr rfl; intro i _; unfold g f; rw [hymn_power]; congr 1
variable (T:SectionData F)(hd : d+1≤D)

def paperback (i : F.Index):Pot G:= fun e k=>hymn (rancho (dabs T i) e k)
def sectionY (x:Letter F): Anthem D G := fun p=>Dawn.notch (pet F x) ((Dawn.paper_fits (pet F x)).trans (Nat.le_trans d.le_succ hd)) p • paperback T (mint F x) -- signature h
lemma report (o:Loc G 1)(x:Letter F) : Wade o (sectionY T hd x) (slots F x):= by
    let l:= slots F x; let b:= mint F x
    refine ⟨fun z e r he=> ?_,fun z e r=>?_,fun e r=> ?_⟩
    · apply le_of_eq; by_contra hz; change (_:ℝ) • hymn (rancho (dabs T (mint F x)) e r) ≠0 at he; rw [pinpaths T (mint _ _) e r hz,hymn_vanish,smul_zero] at he; contradiction
    · exact (hymn_agate _ (marble_agate r _)).smul _
    obtain ⟨C,hC⟩:=hymn_bill (rancho (dabs T b) e r) 1 (0,o); refine ⟨1,C,one_pos,hC.1,fun i=>?_⟩
    exact (hC.smul (Dawn.notch _ _ i)).mono ((mul_le_mul_of_nonneg_right (Dawn.notch_le _ i) hC.1).trans_eq (mul_comm ..))
lemma paperback_tor (i:F.Index)(h: (F.grades i).2≤u) (n): _root_.YM.FormalBulk08.Kemp.banner u (paperback T i) n=PowerSeries.map (MvPolynomial.rename (Lotus.drip n ∘ chamber _ _)).toRingHom (dabs T i):= by
    refine banner_eq ?_; funext e r; rw [badge (paperback T i) (j:=u) _ _ h];unfold paperback;rw [hymn_tor];unfold rancho;rw [coeff_map];exact (Shore.pebble _ _).symm
    · intro e r he; by_contra ht; unfold Yield at ht;unfold paperback at he; rw [pinpaths T i _ _ (by omega),hymn_vanish] at he; contradiction
    exact fun e r=> hymn_agate _ (marble_agate _ _)
lemma debut (i:F.Index)(k:ℕ)(hf:(F.grades i).2≤k)(n:Side)(h:Bid.pop T):
    X^(F.grades i).2 * _root_.YM.FormalBulk08.Kemp.banner k (paperback T i) n=paste (fun x : Jets.Rays (wire G n)=> (T.places (copy F i) 0 (input G n x)).re):= by
    rw [paperback_tor T i hf]; simp_rw [trueLamp]; rw [folds_byte _ _ ((lights_diff T i).contDiffAt.of_le le_top)]; rw [←dab_origin T i h,map_mul, map_pow,PowerSeries.map_X]
lemma citizenship (H:Hol G)(hs:T.Sound H) (hb:Bid.pop T) (i:F.Index) (h:(F.grades i).2≤u)(n:Side): Rite (_root_.YM.FormalBulk08.Kemp.banner u (paperback T i) n) (_root_.YM.FormalBulk08.Kemp.banner u (paperback T i) n) 1 0:= by
    intro I inst a b t ha hb' hk hz hr hT hu;let k:=(F.grades i).2
    let f(x:Jets.Rays (wire G n)):= (T.places (copy F i) 0 (input G n x)).re
    have he : f∘b =ᶠ[𝓝 0] f∘a:= hu.mono fun p hp=>congr_arg (fun z:ℂ=>z.re) (by rw [hp,pull_id];exact T.placed_invariant hs 0 _ _ _)
    have Hf : ContDiffAt ℝ ∞ f 0:= by unfold f; simp_rw [trueLamp]; exact (lights_diff T i).contDiffAt.comp _ (contDiffAt_pi.mpr fun j=>contDiffAt_apply ..) |>.of_le le_top
    have hv (r:Jets.Rays I→ Jets.Rays (wire G n)) (hr:ContDiffAt ℝ ∞ r 0) (hz:r 0=0): paste (f∘r)= X^k * roam ℝ (motor r) (_root_.YM.FormalBulk08.Kemp.banner u (paperback T i) n):= by rw [paste_steps f r Hf hr hz, ← show X^k*_=paste f from debut T i u h n hb,_root_.map_mul,map_pow]; rw [show roam ℝ _ X=X from Series.change_X _]
    apply mul_left_cancel₀ (pow_ne_zero k PowerSeries.X_ne_zero); rw [← hv a (hk.of_le le_top) ha,←hv b (hz.of_le le_top) hb']; exact paste_replace he.symm
lemma opens (o : Loc G 1)(H:Hol G)(hs:T.Sound H)(hb:Bid.pop T)(x:Letter F): Clef o (sectionY T hd x) (slots F x) := by
   refine ⟨⟨fun _ _=> by simp [sectionY,add_smul],fun _ _=> by simp [sectionY,mul_smul]⟩, report T hd _ x,?_⟩
   rw [solo_iff]; intro n p I i a b t ha hb' hx hg hr ht hy; unfold sectionY; rw [banner_coin, _root_.map_mul,_root_.map_mul, Wine.snow, Wine.snow, citizenship T H hs hb (mint F x) (le_refl _) n I a b t ha hb' hx hg hr ht hy]
end YM.FormalBulk08.Rial
