import YM.FormalOPE.RG10.Spiral.Shine
/-! # Top H (signed sequence) covariance of the roster mixing
Use the exact *off-shell* constructed stencil/Wilson data, cover limit of finite-symbol reads on
angular projected curls, joint constrained jet and gauge-color hypotheses already proved on this
finite object; no higher-loop angular Ward identity assumed. Does not assert uniformity in
measurement mesh of any other estimate, e.g. rotation of origins only in the IR limit. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Spiral
open Function Wilson Lattice Gauge Precision Exterior Work.F03 Further.CorrectedLift.Compass Source Source.Drops
   PertExtension Filter RG PertExtension.LatticePT LatticePT.Projection Finset
open Next.Rank Hue Normal MvPolynomial AnalyticBridge.CouplingShape Heat.Top Further.CurvedGaussianJets.Shape
open Next.Foundations
open scoped Topology ContDiff BigOperators Classical RealInnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{d:ℕ}{F: Labels.Frame G d}
local notation "Λ" => Panel Slot G
variable (s: Signed)
local notation "T" => Labels.rotated s.ortho
local notation "H" => covarianceSymbol G

private lemma tier_rot (m:ℕ) (P:Labels.Pol G) : tier m (T P)= T (tier m P) := by
 induction P using MvPolynomial.induction_on' with
 | add i j h k=> rw [map_add,map_add,map_add,map_add,h,k]
 | monomial i j=>
   let w:= Labels.generation (G:=G)
   have he : IsWeightedHomogeneous w (T (monomial i j)) (Finsupp.weight w i):= Labels.pure_moved (fun n=>n+2) _ i j
   have hv : IsWeightedHomogeneous w ((monomial i) j) (Finsupp.weight w i):= isWeightedHomogeneous_monomial w i j rfl
   by_cases h : m=Finsupp.weight w i
   · subst m; change weightedHomogeneousComponent w _ _ = T (weightedHomogeneousComponent w _ _); rw [he.weightedHomogeneousComponent_same,hv.weightedHomogeneousComponent_same]
   change weightedHomogeneousComponent w _ _ = T (weightedHomogeneousComponent w _ _); rw [he.weightedHomogeneousComponent_ne m h,hv.weightedHomogeneousComponent_ne m h,map_zero]
lemma price_rot (d:ℕ)(P:Labels.Pol G) : capRead d (T P) = T (capRead d P):= by simp [capRead,tier_rot,map_sum]
variable (F' : Hol G)
include F'
lemma feel (P:poly Λ) : Heat.Ray.print d (exchange (clockwise s) P)= T (Heat.Ray.print d P) := by
 apply Labels.eval_ext; intro J; rw [Heat.Ray.display_jet,Labels.rotated,Labels.eval_changed,Heat.Ray.display_jet]
 unfold Spindle.text; rw [reads_val]; congr 2; funext i; rw [reads,clockwise,Finsupp.linearCombination_single,smul_eq_mul,← Complex.ofReal_mul]; apply congr_arg
 have he := East.takes_deriv F' i.1 d s (trunk d J); simp_rw [(Work.G02.slotGerm ..).2] at he;
 change _ = (glow (turning s d G (trunk d J)) i.1) i.2; rw [he]; rfl

omit F'
variable {S:SectionData F}{Φ:Hol G}(p : Bid.pop S)(h: S.Sound Φ)
local notation "D" => topMatrix S Φ h p
lemma minted (i:F.Index): (D).matrix H (F.act s.ortho (Pi.single i 1)) = F.act s.ortho ((D).matrix H (Pi.single i 1)) := by
 let d_i:= (D).basis i; let P:= milk H d_i; let g j:=F.act s.ortho (Pi.single i 1) j; let Q:= milk H (∑ j,g j • (D).basis j)
 have he:= onCover (fun n A=> turning_raw p h (n:=n) A s i); simp_rw [braid] at he
 have hr : Heat.Ray.print d (exchange (clockwise s) P)= Heat.Ray.print d Q:= Labels.eval_ext _ _ (fun J=> by simp_rw [Heat.Ray.display_jet]; exact he (access (trunk d J)))
 let hP := (Vertex.basis_fixed S Φ h p i).heat
 let u : Labels.Label G d:= Heat.HueTag.shadow (d:=d) P hP
 have hm : joint F P = F.coords u:= Heat.Ray.collect_normal _ rfl
 have hf : joint F Q= F.act s.ortho (joint F P) := by
    rw [hm, F.act_coords]; apply Heat.Ray.collect_normal; unfold Heat.Ray.clipped; rw [← hr,feel s Φ,price_rot]; rfl
 have hp : (D).matrix H (Pi.single i 1)=(D).joint P:= by unfold Heat.Frame.matrix; simp [Pi.single_apply,P,d_i]
 rw [hp]; change _=F.act s.ortho (joint F P); rw [←hf]; unfold Q; simp only [_root_.map_sum,map_smul]; rfl

lemma coils (x:F.Coeff): (D).matrix H (F.act s.ortho x) = F.act s.ortho ((D).matrix H x) := by
 have hx : (D).matrix H ∘ₗ (F.act s.ortho) = (F.act s.ortho) ∘ₗ ((D).matrix H) := by apply LinearMap.ext; intro x; nth_rw 1 2 [show x = ∑ i, x i • Pi.single i 1 from Eq.symm (by ext i; simp [Pi.single_apply,mul_ite])] ; simp_rw [map_sum,LinearMap.comp_apply,map_smul,minted]
 exact DFunLike.congr_fun hx x
lemma ordered (x:F.Coeff): (D).inverse H (F.act s.ortho x) = F.act s.ortho ((D).inverse H x) := by
 apply (D).injective (Q:=H); rw [coils]; simp only [show ∀ x, (D).matrix H ((D).inverse H x)=x from fun x=> (D).conversion H |>.apply_symm_apply x]
end YM.FormalOPE.RG10.Spiral
