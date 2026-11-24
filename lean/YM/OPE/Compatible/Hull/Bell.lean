import YM.OPE.Compatible.Juniper.Post
import YM.OPE.Compatible.Sward.Lucent
/-!
# Build fixed-height real analytic×smooth LP mark extraction. Uniform Scrape.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}{C:KernelChoices}
open Finset
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin Module
local notation "X!"=> ShapeX
abbrev Hoard (G:Gauge)(b k m:ℕ): Submodule ℝ (Seat k m (Shade G)) where
   carrier:={p|∀ i:ℕ,∀ x:Page (Shade G) i,x∉encircled G b i → lilies m k _ p i x=0}
   zero_mem':= fun i x _=>by rw [_root_.map_zero]; rfl
   add_mem':= fun {p q} (hp:∀ i x,_→lilies m k (Shade G) p i x=0)(hq:∀ i x,_→lilies m k (Shade G) q i x=0) i x h=> by rw[map_add]; exact Eq.trans (congr_arg₂ (·+·) (hp i x h) (hq i x h)) (add_zero _)
   smul_mem':=fun a p (h:∀ i x,_→lilies m k (Shade G) p i x=0) i x he=>by rw [map_smul]; change a * _=_; rw[h _ _ he,mul_zero]
lemma delve (p:Seat k m (Shade G))(h:p∈ Hoard G b k m)(A:RowB (Shade G))(a:ℝ): boostS A a m k p ∈ Hoard G b k m:=by
       rw[boostS,Hflow]; apply (Hoard G b k m).sum_mem; intro i _; apply (Hoard G b k m).smul_mem; clear * - p h A; -- A????
       induction i with
       | zero=>simpa
       | succ i ih=>
            rw[pow_succ',Module.End.mul_apply]; let Y:= ((lapD A m k).toLinearMap ^ i) p; change lapD A m k Y∈Hoard G b k m; intro u x hx; rw[pulse_i]; change wind u * (Flume.Script.pad _ _ _) = _
            rw[show Flume.Script.pad A.val (lilies m k _ Y (u+2)) x=0 from ?_,mul_zero]; unfold Flume.Script.pad Sack.rope; refine (tsum_congr (g:=fun _=>0) ?_).trans (by simp) -- lemma syntax
            intro v; split_ifs with hv
            · apply mul_eq_zero_of_left; apply ih (u+2) v; rintro H; obtain ⟨j,hj,rfl⟩:=mem_image.mp H; apply hx; rw [←hv]; exact mem_image.mpr ⟨(fun i=> j i.succ.succ),mem_univ _,rfl⟩
            rfl
lemma StampQ (p:Seat k m (Shade G))(hp:p∈ Hoard G b k m)(x y:Fin i→ fieldX (Shade G))(ht: Exposure b ∘ x=Exposure b ∘ y): wholeX (lilies m k _ p i) x=wholeX (lilies m k _ p i) y:=by
      apply tsum_congr; intro j; by_cases hh:j∈encircled G b i
      · obtain ⟨j,h,rfl⟩:=Finset.mem_image.mp hh; apply congr_arg; exact Finset.prod_congr rfl fun u _=>congr_fun (congr_fun ht u) (j u)
      rw [hp _ _ hh,zero_mul,zero_mul]
lemma LayH (p:Song (Scoop G b))(h:ReadyP p k): (Locket h m).val∈ Hoard G (4*b) k m:=by
      intro i x ht; rw [show lilies m k _ (Locket h m).val=_ from sproutsX _ (TomX m k p h)]; exact HoneyOut _ _ ht -- ht
lemma Drowse (b:ℕ)(v:Bid.Dir G n): Packer G b (Exposure (4*b) (charW o v))= Cane G b o v:=by
      have hx:= climbsF o ((flats G n).toContinuousLinearMap) v; let L:= (flats G n).toContinuousLinearMap; have ht:charW o v=Charu o L v:= by simpa only[ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using hx
      rw [Fort, ← BFilm_s, ht]; exact flumes o _ b v
lemma Proto (p:Song (Scoop G b))(h:ReadyP p k)(m:ℕ):LightP o (m:=m) (Locket h m).val=Strike k p ∘ (Cane G b o):=by
      funext v; let q:=Locket h m; change Flair (lilies m k _ q.val) k _ _= Strike _ _ _; rw [show lilies m k _ q.val=_ from sproutsX _ (TomX m k p h)]; unfold Flair Strike; refine Finset.sum_congr rfl fun i _=>?_ ; unfold Script.value; rw [← timing,dropK]; let x:= charW o v; change p i _=p i _; refine congr_arg _ (funext fun j=> Drowse o b v) -- elabor
lemma Invest (p:Song (Scoop G b))(h:ReadyP p k)(v:Train r)(A:KernelChoices)(he:4 ≤ r):
      let R:= Vessel A v G n he; let S:=Cane G b o;let f:=LiftV (chamber R S) p k; let q:= boostS (rentV G v he A n) (1/2) m k (Locket h m).val
      formSong m k G o q i ∘ (fun y:Fin i→Bid.Dir G n=>(flats G n) ∘ y) = f i ∘ (fun y:Fin i→Bid.Dir G n=> S ∘ y):=by
            intro R S f q; let μζ:=PertExtension.Chart.tangent G (Exterior.Body 1 n); let F:= Strike k (formSong m k G o q); let Y:= Strike k f; let L:= (flats G n).toContinuousLinearMap; have hz:settled (m:=m) (Locket h m).val:=by intro i; exact (merit ((Locket h m).property) i).2.1
            have hp : F ∘ L=Y ∘ S:=by rw [show F ∘ L=LightP o (m:=m) q from funext fun i=> strikesT q .., ← wellD o _ _ _ hz,Proto o _ h m]; exact under μζ R S p h.finance
            have hy: f∈ harmon (Scoop G b) k:=peak _ _ _ _ h.finance; funext y; change formSong _ _ _ _ _ _ _=_; rw [← gradeC (chic o q (turfy _ _ _ hz)) i, ← gradeC hy i]; change Tensor.coeff F i 0 (L ∘ y)= Tensor.coeff Y i 0 (S∘ y); rw[← onceD L F (sailCost _ k).cost i y,← onceD S Y (sailCost _ k).cost i y,hp]
end YM.OPE.Spells
