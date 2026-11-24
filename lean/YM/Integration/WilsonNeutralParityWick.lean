import YM.FormalBulk08.Roof.Enroll
/-! Parity of the actual normalized marked heat expansion with its original
interacting quiet potential. The source rank and the coupling index shift
by the same parity at every thermal contraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralParityWick
open FormalBulk08 Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series
open Jets Work.F03 Work.F05 PowerSeries Bank Stationary Lotus Shore Mesa Gorge City Cork Rift Next.Free Flat RG Precision Tree
open Kemp Pose Glide Palm Wine Rial Roof
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical

def Parity {V:Type} (l:ℕ)(A:OrbitV V):Prop:=
  ∀ e r, A e r≠0 → r%2=(l+e)%2

theorem heat {V:Type}{S A:OrbitV V}(q:V→V→ℝ)(hs:Fiery S){l:ℕ}(ha:Parity l A)(n e r:ℕ):
    dipper q (swim q S) A n e r≠0 → r%2=(l+e)%2:=by
  induction n using Nat.strong_induction_on generalizing e r with
  | _ n ih =>
    cases n with
    | zero => simpa only [dipper_first] using ha e r
    | succ n =>
      intro use; by_contra wrong
      have previous:dipper q (swim q S) A n e (r+1+1)=0:=by
        by_contra live
        have h:=ih n (by omega) e (r+1+1) live
        omega
      have split:brawl q (swim q S) (dipper q (swim q S) A) n e r=0:=by
        apply brawl_vigil;intro a ha b hb w hw
        by_contra! live
        have h₁:=Lava.thermal q hs _ _ _ live.1
        simp only [Finset.HasAntidiagonal.mem_antidiagonal] at ha hb hw
        have h₂:=ih b.2 (by omega) _ _ live.2
        omega
      exact use (by rw [dipper_succ,previous,stare_nil,zero_add,split,smul_zero,smul_zero])

variable {G:Gauge} {d D j t l:ℕ} {K:KernelChoices}
variable (P:Flight j t)(V:Lodge P.patch)(W:Pot G)(ρ:ChartRatio G)(h:P.patch.Branches K G)
theorem child (T:Pot G)(p:Parity l T)(hw:Vivid W)(hr:LocalRatio ρ)(u:ℕ):
    Parity l (braise P V W T ρ h u):=by
  have carried:Parity l (coves K P V T):=by
    intro e r use;apply p e r;intro zero
    unfold coves Glide.urn at use
    rw [zero,jetty_zero,pearl_zero,pearl_zero,pearl_zero] at use
    exact use rfl
  intro e r use;by_contra wrong;apply use
  unfold braise;apply Finset.sum_eq_zero;intro n _
  have ho:border P V W T ρ h n e r=0:=by
    by_contra live
    exact wrong (heat _ (fairy W ρ P V K hw hr) carried n e r live)
  rw [ho,jetty_zero]

theorem average (Y:Anthem D G)(hL:2≤P.L.val)(hp:∀ f,Parity l (Y f))
    (hw:Vivid W)(hr:LocalRatio ρ)(d u:ℕ)(f:Dawn.Studio D):
    Parity l (quick P V W Y ρ h hL d u f):=by
  have at_site (x:Site P.L):Parity l (stepsong P Y hL f x):=by
    intro e r live;apply hp (Dawn.throughW x D hL f) e r;intro zero
    unfold stepsong work at live;rw [zero] at live;exact live rfl
  intro e r live;by_contra wrong;apply live
  unfold quick;simp only [Pi.smul_apply,Finset.sum_apply]
  rw [Finset.sum_eq_zero (f:=fun x=>braise P V W (stepsong P Y hL f x) ρ h u e r),smul_zero]
  intro x _;by_contra val
  exact wrong (child P V W ρ h _ (at_site x) hw hr u e r val)

end YM.Integration.WilsonNeutralParityWick
end
