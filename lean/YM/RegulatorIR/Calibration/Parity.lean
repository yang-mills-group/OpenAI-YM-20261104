import YM.RegulatorIR.Calibration.Carrier

set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Calibration
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum Warm Profiles Centered Clocks Stage
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
variable {X:Type} {G:Gauge}{K:KernelChoices}{P:Patch}{p k e:ℕ}

def Steady (T: Orders X)(p:ℕ):Prop:=∀ i≤p, ∀ j,T i j ≠0→ i%2=j%2
lemma steadyL (H:P.Branches K G)(v r:ℕ)(h: r≠v): mainL K P G H v r=0:=by
 ext1 x;unfold mainL many massive; simp_rw [fun j=> positionS _ _ _ ((wingL K P G H).value j) (fun _ _=>rfl) (rooted ..) v r h,Pi.zero_apply]; exact tsum_zero
lemma steadyR (H:P.Branches K G)(v r:ℕ)(h: r≠v): mainR K P G H v r=0:=by
 ext1 x;unfold mainR many massive; let R:= avenue P K 4
 simp_rw [fun j=> positionS _ _ _ (boosted (S:=R) H j) (fun _ _=>rfl) (locally R H Clocks.flat j) v r h,Pi.zero_apply]; exact tsum_zero
lemma holdingH (L:Layer X X){T:Orders X}(h:Steady T p):∀ k,Steady (logHeat L T false k) p:=by
 intro k; induction k using Nat.strong_induction_on with
 | _ k ih=>
    intro i hi r hv; cases k with
    | zero=> rw [logHeat_first] at hv; split at hv; contradiction; exact h i hi r hv
    | succ k=>
       let V:=logHeat L T false;rw [logHeat_next] at hv; split at hv; contradiction
       by_cases hp: heating L (V k i) r=0
       · rw [hp,zero_add] at hv -- placeholders
         have he: drift L V V k i r ≠0:=fun h'=>hv (by rw [h', smul_zero,smul_zero]); obtain ⟨a,b,g,t,j,n,ha,hb,hg,hT,hN⟩:=joins_come he; have hx:= ih a (by omega) g (by omega) _ hT; have hh:= ih b (by omega) t (by omega) _ hN; omega
       have ht:= ih k (by omega) i hi (r+2) (heating_comes hp); omega
def Seconds (s:Scale)(p:ℕ):Prop:=∀ i≤p,i%2=1→ biases s i=0
variable {R:Type} {M:R→ℕ} {n:Page M→Side} (S:Circuit M n)(Y:Program K)(G:Gauge)(Z:∀ P:Patch,P.Branches K G)(s:Page M→ Scale)
-- shadow G ok
local notation "Q"=> S.payroll Y G Z
local notation "Tr"=> S.lane Y G Z
local notation "D"=> S.devices Y G Z
lemma steadyW (i:R)(h: Seconds (s (Page.opening M i)) p) : Steady ((Q s).bulk (Page.opening M i)) p:= by
 intro b hv j hp;let a:= Page.opening M i; have he:= (Q s).top_v i b j hp; change many (Circuit.mural G s i) b j ≠0 at hp
 by_cases hh:j<2
 · exact (hp (primary_low _ (Circuit.serene G s i) he.1 hh)).elim
 rw [primary_high _ (Circuit.serene G s i) he.1 (by omega) he.2] at hp; have hx:(b+2-j)%2≠1:=fun hx=>hp (by rw [show biases _ _= _ from h _ (by omega) hx,zero_smul]); omega
lemma steadyS (i:Flap M)(H:Seconds (s i.prev) p) (h:Steady ((Q s).bulk i.prev) p): Steady ((Q s).bulk i.next) p:=by
 let A:= D s i; let Z':= (Q s).bulk i.prev; let V:= A.jVac Z'; let Q':= (S.pactP i);
 have hJ: Steady V p:=by
    intro k hk r hv; have hh:= joint_h S Y G Z s i k r hv
    by_cases hp:Z' k r ≠ 0
    · exact h k hk r hp
    push Not at hp; change offer _ (Z' k r)+(D s i).addon k r≠0 at hv;
    rw [hp] at hv
    have hD: (D s i).addon k r ≠ 0:= fun he=>hv (by rw [he];ext1 x;simp [offer,Stalk.collect])
    rw [add_k _ _ _ _ _ _ _ hh.1] at hD;by_cases hg:r=k
    · exact congr_arg (·%2) hg.symm
    rw [Pi.add_apply,steadyL _ _ _ hg,zero_add, Finset.sum_apply] at hD;
    obtain ⟨j,hj,hH⟩:= exists_ne_zero_of_sum_ne_zero hD; have hq:=mem_antidiagonal.mp hj
    have hR:r=j.2+2:= Classical.not_not.mp fun hv=>hH (by rw [Pi.smul_apply,steadyR _ _ _ hv, smul_zero]); have hp:j.1%2≠ 1:=fun hy=> hH (by rw [show biases (s i.prev) j.1= (0:ℝ) from H _ (by omega) hy,zero_smul];rfl);omega
 intro k hk r hv; rw [← (Q s).step_v] at hv; unfold GridStep.pure at hv; split at hv; contradiction
 have hp :ceaseHeat A.line V false k r ≠0:=fun h=>hv (by
    change A.pullI (ceaseHeat A.line V _ _ _)=_;rw [h]; simpa using! pull_m A (0:Packet (Foot G⊕Foot G) r) 0)
 unfold ceaseHeat heated at hp; obtain ⟨i,_,hv⟩:= exists_ne_zero_of_sum_ne_zero hp; exact holdingH _ hJ i k hk r hv
end YM.RegulatorIR.Calibration
