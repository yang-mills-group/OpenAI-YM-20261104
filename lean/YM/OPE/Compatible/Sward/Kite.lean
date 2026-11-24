import YM.OPE.Compatible.Sward.Limn
import YM.OPE.Compatible.Lob.Top
import YM.OPE.Compatible.Frog.Eye
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
open Cloud JetS
open scoped ContDiff
variable {v y:fieldX (Shade H)}
open Tensor WardBin
-- budget C estimate.O. Use masks of bad axes
open Cascade Terp Paver Rill Shell FreeResolvent Exterior MSbar.Tree MSbar.Tree.Resolvent Frequency Streamer
open Votive
variable {N:Side}{L:KernelChoices} (x:Site N)
open Drift Shell Char
variable {τ :Char.Phase→ℕ}{d:ℕ}
open PertExtension Series GaussianScore
open Matrix
section derive
lemma fallP (x:Seat k m (Shade H))(A:RowB (Shade H)): lapD A m k (Dower H k m x)= Dower H k m (lapD A m k x)+(2:ℝ) • (lapD A m k x):=by
       apply lilies_inj; funext i; rw [map_add, map_smul,Pi.add_apply, Pi.smul_apply, dowerP, pulse_i,pulse_i,dowerP,flareD,← add_smul];rw [smul_comm (wind i),Nat.cast_add,Nat.cast_two]
lemma soarP (x:Seat k m (Shade H))(A:RowB (Shade H))(t:ℝ):
     let S:=boostS A t m k; let U:=lapD A m k; let D:= Dower H k m
     S (D x)= D (S x)+ (2*t) • U (S x):=by
         intro S U D; let T:=U.toLinearMap; let f(i:ℕ):= (T^i) x; have ht(i:ℕ):f (i+1)=U (f i):=by unfold f; rw [pow_succ',End.mul_apply];rfl
         have hp(i:ℕ): (T^i) (D x)=D (f i)+ (2*i:ℝ) • f i:=by
             induction i with
             | zero=>simp[f]
             | succ i ih=> rw [pow_succ',End.mul_apply,ih,map_add,map_smul, ht, show T (D (f i))= _ from fallP (f i) A, show T (f i)=_ from (ht i).symm, ← (ht i)]; push_cast; rw [ _root_.add_assoc,← add_smul, show 2+2*(i:ℝ)=2*(i+1:ℝ) by ring]
         let g(i:ℕ):= t^i/(i.factorial:ℝ); have hu(y): S y=∑ i∈Finset.range (k+1), g i • ((T^i) y):= Hflow .. -- whitespace
         have hh(i:ℕ): g (i+1) * (2*(i+1:ℕ):ℝ)=(2*t)*g i:=by unfold g; rw[pow_succ,Nat.factorial_succ];push_cast;field_simp
         rw [hu, hu]; simp_rw[map_sum,map_smul,hp, smul_add,smul_sum,sum_add_distrib,smul_smul]; apply congr_arg; rw[Finset.sum_range_succ',Finset.sum_range_succ]
         have hx: x∈rooft (Shade H) k m k:=(show ∀i>k,lilies m k (Shade H) x i=0 from (sproutV m k x).1); have hz:f (k+1)=0:=(iterateD (by simpa only [one_smul] using! lap_deb A 1 k m) hx (k+1)).2 (by omega); have hk:=ht k; rw[hz] at hk; simp only [ hh,ht, Nat.cast_zero,mul_zero,zero_smul,show U ((T^k) x)=0 from hk.symm,smul_zero]; rfl
end derive
lemma tallP (p:Seat k m I) (c:ℝ)(h:Deep (m:=m) p j):Deep (m:=m) (c • p) j:=fun i hi=> by rw [map_smul,Pi.smul_apply,h i hi, smul_zero]
lemma TallA (p q:Seat k m I)(h:Deep (m:=m) p j)(hp:Deep (m:=m) q j):Deep (m:=m) (p+q) j:=fun i hi=>by rw[map_add,Pi.add_apply,h i hi,hp i hi,zero_add]
lemma tacks (p:Seat k m (Shade H))(hp:Deep (m:=m) p (j+2))(A: RowB (Shade H)): Deep (m:=m) (lapD A m k p) j:=fun i hi=>by rw [pulse_i,hp (i+2) (by omega)]; ext1 x; simp [pad,Sack.rope,tunnel]
lemma very (p:Seat k m I)(ht:Deep (m:=m) p j)(hx:i ≤ j): Deep (m:=m) p i:=fun _ hy=>ht _ (lt_of_lt_of_le hy hx)
lemma toning (p: Seat k m (Shade H))(t:ℝ) (A:RowB (Shade H))(h:Deep (m:=m) (boostS A t m k p) (j+2)): Deep (m:=m) (boostS A t m k (Dower H k m p)) j:=by
       rw [show boostS _ _ _ _ (Dower H k m p)=_ from soarP p A t]; apply TallA
       · intro i hi; rw [dowerP,h i (by omega),smul_zero]
       exact tallP _ _ (tacks _ h A)
section
variable (v:Train r)(h:r≥4)(w:Aware d τ)
lemma rugged (p: Tower (Shade H) d τ) (c:ℝ)(hp: TrueRay (L:=L) v h p k): TrueRay (L:=L) v h (rebase H w c p) k:=by
       intro i; by_cases he:i=2
       · subst i; rw [Drift.sip, map_add,map_smul]; apply TallA _ _ (hp 2); let V:= boostS (atlasF H v h L) (1/2) (τ 0) d; have hv:Deep (m:=τ 0) (V (p 0)) (k+2):= very _ (hp 0) (by norm_num)
         apply tallP; let u:= lapD (atlasF H v h L) (τ 0) d; let T:= toning _ (1/2) _ (k:=d) hv; -- fix apostrophes
         rw [show peakV H w (p 0)= Quit.Jac.armP H w 0 2 (by decide) (Dower H d _ (p 0)) from (by apply lilies_inj (Shade H) (d+(2:Phase).val) (τ 2);funext i; rw[Quit.Jac.armL,peak_eq]; exact (dowerP _ _).symm),Quit.Jac.lockC]; intro j hj; rw [Quit.Jac.armL]; exact T _ hj
       rw [sail _ _ w _ he]; exact hp i
end
end YM.OPE.Silt.Phere
