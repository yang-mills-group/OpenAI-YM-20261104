import YM.MS.Arts.Step
import YangMills.WilsonProof.NativeSupport.YM.MS.Arts.Cabs
/-!
# extending isometry and stabilizers

Use only prefix action for necessities and O(all) if allowed. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arts
open Function Set Filter Finset MeasureTheory Real
open scoped Topology ContDiff InnerProductSpace
open Momentum
variable {A B:Type}[Fintype A][DecidableEq A] {m n k:ℕ}
variable (h:m≤n)
namespace Spin
variable (X:Spin (L m))
def taller : SectorP n≃L[ℝ] SectorP n:= (cabs h).trans ((X.turn.prodCongr (ContinuousLinearEquiv.refl ℝ (Momentum (Apart m n)))).trans (cabs h).symm)
lemma total (p:SectorP n): taller h X p= Left h (X.turn (Cl h p)) + Right h (Cr h p):= rfl

def arch : Spin (L n) where
    turn := taller h X
    rad x y:= by rw [farApart h,total,total]; simp only [map_add,leftCl,rightCl,Cl_left,Cr_down,add_zero,zero_add]; rw [X.rad, ← farApart h]

lemma arch_on (p:SectorP m): (arch h X).turn (Left h p)=Left h (X.turn p):= by simp only [arch,total,leftCl,Cr_down,map_zero,add_zero]
lemma arch_identity (p: Momentum (Apart m n)): (arch h X).turn (Right h p)=Right h p:= by simp only [arch,total,rightCl,Cl_left,map_zero,zero_add]
-- when b true get all, else within.
variable {b: Bool}
def within (b:Bool)(X:Spin (L m)): Prop:= b=false→∀ i, X.turn (Left (Nat.zero_le m) i)=Left (Nat.zero_le m) i
lemma arch_steady (H:X.within b): within b (arch h X):= by
   intro hi p; have hx : Left (Nat.zero_le n) p= Left h (Left (Nat.zero_le m) p):= by change _=sendB _ (sendB _ p); rw [sons,rides_link]
   rw [hx,arch_on,H hi]
lemma within_back (H:X.within b): within b X.back:= by intro hi p; nth_rw 1 [← H hi p]; rw [rear]
lemma fixedLeft {X:Spin (L n)}(he:∀ p, X.turn (Left h p)=Left h p): X.within b := by
   intro h0 i; rw [show Left (Nat.zero_le n) i=Left h (Left (Nat.zero_le m) i) from ?_, he _]; change _=sendB _ (sendB _ i); rw [sons, rides_link]
lemma fixedBasis {X:Spin (L n)}(he:∀ p, X.turn (Left h p)=Left h p)(i:L m): X.turn (spray (rises h i))=spray (rises h i):= by rw [← send_spray]; exact he _

lemma zap (s:A) (i:A): pairing (spray s) (spray i)=(if i=s then 1 else 0):= by simp [spray,pairing,Pi.single_apply,eq_comm]
omit [Fintype A] in
lemma blink (x:A): spray x≠0:= fun he=> by simpa [spray] using congr_fun he x
def spark (p:A): Spin A:= tilt (spray p) (blink _)
lemma sees_p (p:A): (spark p).turn (spray p) = -spray p:= by change wall _ _ _=_; simp only [wall_pay,sq_eq,zap,if_true,div_one,mul_one,two_smul]; abel
lemma sees_away {p q:A}(hx:p≠q): (spark p).turn (spray q)=spray q:= floors _ _ (by rw [zap,if_neg hx.symm])
lemma lightOn (p:Apart m n)(i:SectorP m): (spark (aside h p)).turn (Left h i)=Left h i:= by
    refine floors _ _ ?_; rw [← send_spray,pair_left,high] -- rewrite Right abbrev
-- rotate/align
lemma fit (p q:Momentum (Apart m n))(he:p.sq=q.sq): ∃ X:Spin (L n),(∀ i,X.turn (Left h i)=Left h i)∧ X.turn (Right h p)= Right h q:= by
    by_cases hp:Right h p=Right h q; exact ⟨⟨ContinuousLinearEquiv.refl ..,fun x y=>rfl⟩,fun i=>rfl,hp⟩
    refine ⟨tilt (Right h p-Right h q) (sub_ne_zero.mpr hp),fun i=> floors _ _ ?_, turns _ _ hp (by rw [sq_down,sq_down,he])⟩; rw [pair_left,pair_sub,high,high,sub_zero]
end Spin
-- first extra identification until m+1
lemma hatch_ext (h:m< n)(hp : n≤ k) : rises hp (hatch h) = hatch (lt_of_lt_of_le h hp):= by ext; rfl
end YM.MS.Arts
