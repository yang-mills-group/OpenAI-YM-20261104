import YM.OPE.Compatible.Hull.Loom
import YM.OPE.Compatible.Spades.Lores
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
open Work.F08
lemma loomA (p q:Fpaper G b): poke (r:=0) ![pealB p,pealB q]= (q.1.val).1 - p.1.val.1:=rfl -- edit
noncomputable def Taxon (G:Gauge)(b:ℕ): Finset Cover:= (Finset.univ×ˢFinset.univ).image fun x:Fpaper G b× Fpaper G b=>poke (r:=0) ![pealB x.1,pealB x.2]
lemma opYX (A B C:RowB (Shade G))(h:∀ a∈ Taxon G b,∀ x y,A.val x y a+B.val x y a=C.val x y a)(p:Seat k m (Shade G))(hp:p∈ Hoard G b k m): lapD C m k p= lapD A m k p+lapD B m k p:=by
      apply lilies_inj _ _ _; rw[map_add]; funext i; simp_rw [pulse_i,Pi.add_apply,pulse_i]; rw [← smul_add]; apply congr_arg; let v:=moduleAt m k (i+2) (Shade G) p; let x(F:RowB (Shade G)):= tunnel F.val (lilies m k _ p (i+2))
      have ht(F): x F= seed m _ _ (dent (m:=m) F v):=(nailD F v).symm
      have hs : x C=x A+x B:=by
           funext q; by_cases he: q∈ encircled G b (i+2)
           · obtain ⟨j,hj,rfl⟩:= Finset.mem_image.mp he; let y:=CageB b (i+2) j; have hh: poke y ∈ Taxon G b := Finset.mem_image.mpr ⟨(j 0,j (0:Fin (i+1)).succ), Finset.mem_product.mpr ⟨mem_univ _,mem_univ _⟩,rfl⟩; unfold x tunnel; simp only [Pi.add_apply]; rw [←h _ hh,mul_add]
           simp only [x,tunnel,Pi.add_apply,hp _ _ he,zero_mul,zero_add]
      unfold Flume.Script.pad; rw [show tunnel C.val _= x A+x B from hs]; convert! Sack.rope_add (f:=x A) (g:=x B) melt (by rw[ht]; exact tiller m _) (by rw[ht]; exact tiller m _) using 1 <;> congr! 2
lemma loLap (A:RowB (Shade G))(p:Seat k m (Shade G))(hp:p∈ Hoard G b k m)(i:ℕ): ((lapD A m k).toLinearMap ^i) p∈ Hoard G b k m:=by
       induction i with
       | zero=>simpa
       | succ i ih=>
            rw[pow_succ',Module.End.mul_apply]; let Y:= ((lapD A m k).toLinearMap ^ i) p; change lapD A m k Y∈Hoard G b k m; intro u x hx; rw[pulse_i]; change wind u * (Flume.Script.pad _ _ _) = _
            rw[show Flume.Script.pad A.val (lilies m k _ Y (u+2)) x=0 from ?_,mul_zero]; unfold Flume.Script.pad Sack.rope; refine (tsum_congr (g:=fun _=>0) ?_).trans (by simp)
            intro v; split_ifs with hv
            · apply mul_eq_zero_of_left; apply ih (u+2) v; rintro H; obtain ⟨j,hj,rfl⟩:=mem_image.mp H; apply hx; rw [←hv]; exact mem_image.mpr ⟨(fun i=> j i.succ.succ),mem_univ _,rfl⟩
            rfl
variable {η a:ℝ} (A B:RowB (Shade G)) (ha:A.fare≤a)(hb:B.fare ≤ a)(hh:0 ≤ η)(ht:∀ x∈Taxon G b,∀ i j, ‖A.val i j x-B.val i j x‖ ≤ η)
def spanKΩ (a:ℝ)(k:ℕ):ℕ→ℝ|0=>0|i+1=>wind k * ((wind k*a)^i+a*spanKΩ a k i)
include A B ha hb hh ht
lemma flareNorm (p:Seat k m (Shade G))(hp:p∈ Hoard G b k m)(i:ℕ):
     let f:=(lapD A m k).toLinearMap; let g:= (lapD B m k).toLinearMap
     ‖(f^i) p-(g^i) p‖ ≤ spanKΩ a k i * η * ‖p‖ :=by
           intro f g; let U:Row (Shade G) (Shade G):=fun i j x=> if x∈ Taxon G b then A.val i j x-B.val i j x else 0; let D:RowB (Shade G):={val:=U,fare:=η,positive:=hh,lease:=fun i j x=>by unfold U; split_ifs with hz; exact ht x hz i j; exact (norm_zero:‖(0:ℝ)‖=0).trans_le hh}; have he(x:Seat k m (Shade G))(h:x∈Hoard G b k m): f x-g x=lapD D m k x:=sub_eq_iff_eq_add.mpr (opYX D B A (fun t hx i j=>by unfold D U; simp [hx]) x h)
           let l:=wind k; have hx:0≤l:=by unfold l Silt.wind; positivity
           have hg(F:RowB (Shade G))(c:ℝ)(hc:F.fare ≤ c) (x:Seat k m (Shade G)): ‖lapD F m k x‖ ≤ l*c*‖x‖:= ((lapD F m k).le_opNorm x).trans (mul_le_mul_of_nonneg_right ((lapE F).trans (mul_le_mul_of_nonneg_left hc hx)) (norm_nonneg _)); let C:=l*a; have hc:0≤C:=mul_nonneg hx (B.positive.trans hb); have hz(i): ‖(f^i) p‖≤ C^i*‖p‖:=by induction i with| zero=>simp| succ i ih=> rw[pow_succ',pow_succ',End.mul_apply, mul_assoc]; exact (hg A a ha _).trans (mul_le_mul_of_nonneg_left ih hc)
           induction i with
           | zero=>simp [spanKΩ]
           | succ i ih=>
                rw[pow_succ',pow_succ',End.mul_apply,End.mul_apply]; let X:=(f^i) p; let Y:= (g^i) p; rw [show f X-g Y=lapD D m k X + g (X-Y) from by rw [← he X (loLap A p hp i), map_sub]; abel]
                exact ((norm_add_le ..).trans (add_le_add ((hg D η le_rfl _).trans (mul_le_mul_of_nonneg_left (hz i) (mul_nonneg hx hh))) ((hg B a hb _).trans (mul_le_mul_of_nonneg_left ih hc)))).trans_eq (by rw [show spanKΩ a k (i+1)=l*((l*a)^i+a*spanKΩ a k i) from rfl]; unfold C;ring)
end YM.OPE.Spells
