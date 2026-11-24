import YM.MSbar.Chord.Beds
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter Rolling Lattice RG Wilson Push Uniform
open Precision Gauge MSbar.Wave StressFlux
open scoped Topology Matrix.Norms.Frobenius ContDiff Classical BigOperators InnerProductSpace
open AnalyticBridge.VerifiedReset
variable {G:Gauge}{n:Side}
local notation "S₀"=> Site n
local notation "E"=> Edge (Site n)
local notation "N"=> n.val
-- centered coords; allow even.
noncomputable def halfE (e:Axis)(b:Axis): ℝ:= if b=e then (1/2:ℝ) else 0
noncomputable def zone (e:Edge (Site n))(x:Site n)(b:Axis) := coord e.1 x b-halfE e.2 b
noncomputable def middle (e v: Edge (Site n)) (b:Axis): ℝ:= zone e v.1 b +halfE v.2 b
@[simp] lemma zone_mid (o x:Site n)(i j k:Axis): middle (o,i) (x,j) k+halfE i k-halfE j k= coord o x k:=by unfold middle zone; abel
def beadPad (b x:Site n)(m:ℕ):ℝ:= (1+(separation x b:ℝ))^m
lemma medium_size (e v:E)(i:Axis) : |middle e v i| ≤ beadPad e.1 v.1 1:=by
    let j:=(separation v.1 e.1:ℝ); unfold middle zone; refine (abs_add_le ..).trans ?_; have he(e:Axis) :|halfE e i|≤1/2:=by unfold halfE; split <;> norm_num
    exact (add_le_add ((abs_sub ..).trans (add_le_add (small_coord ..) (he _))) (he _)).trans_eq (by unfold beadPad;ring)
private lemma phase_le (b:S₀)(x:S₀)(s:Signed)(k:S₀) (d:Axis) : separation (sendEdge s k (x,d)).1 (affine s k b) ≤ separation x b+1:=by
    let o:=affine s k x; let a:=s.perm d
    have hs:10≥ 1:=by omega
    by_cases he: s.flip d
    · have hh :sendEdge s k (x,d)=(o-step a,a):=by simp [o,a,sendEdge,posDir,Step.rotate,Step.used,he]
      rw [hh]; apply (separation_triangle _ o _).trans; apply le_trans (Nat.add_le_add _ (le_of_eq (spin_separation ..))) (Nat.add_comm ..|>.le); have hf:= Work.E01.sep_step_le (o-step a) a; rw [show (o-step a:S₀)+step a=o from sub_add_cancel ..] at hf; exact hf -- sub_add lemma
    have hh:sendEdge s k (x,d)=(o,a):=by simp [o,a,sendEdge,posDir,Step.rotate,Step.used,he]
    rw [hh]; exact (spin_separation ..).le.trans (by omega)
lemma lanes (s:Signed)(b:S₀)(e v:E): separation (sendEdge s b e).1 (sendEdge s b v).1 ≤ separation e.1 v.1+2:=by
    apply (separation_triangle _ (affine s b v.1) _).trans; apply le_trans (Nat.add_le_add (phase_le v.1 e.1 s b e.2) _) (show separation e.1 v.1+1+1≤ _ by omega); rw [separation_comm]; simpa only [separation_self, Nat.zero_add] using phase_le v.1 v.1 s b v.2
-- adjust old midpoint.Backs. keep slack 40.
lemma rises (s:Signed)(k:S₀)(x:S₀)(d:Axis)(b:S₀)(i:Axis) (he:10*separation (affine s k x) b < N)(hN:4 ≤ N): coord b (sendEdge s k (x,d)).1 (s.perm i)+halfE (s.perm d) (s.perm i)= coord b (affine s k x) (s.perm i)+sign s d*halfE d i:=by -- simplify
    let o:= affine s k x; let y:=sendEdge s k (x,d); let a:=s.perm d
    have hi : halfE (s.perm d) (s.perm i)= halfE d i:=by unfold halfE; simp
    by_cases hp:s.flip d
    · have hh :sendEdge s k (x,d)=(o-step a,a):=by simp [o,a,sendEdge,posDir,Step.rotate,Step.used,hp]
      rw [hi,hh,show sign s d= -1 from (by simp [sign,hp])];dsimp only
      have hv:coord b (o-Step.vec (posDir a):S₀) (s.perm i) = coord b o (s.perm i)-(if i=d then 1 else 0):=by
          have hk:= lift_step (d:=negDir a) he hN -- parameter not named d? verify
          change lift (o+_ - b) = _ at hk; unfold coord; rw [show (o-Step.vec (posDir a):S₀)=o + Step.vec (negDir a) from ?_] -- syntax weird. adjust
          · rw [hk]; unfold a; simp [sub_eq_add_neg,o]; -- inspect
          exact sub_eq_add_neg o (step a)
      change coord b (o-step a) (s.perm i)+ _=_; rw [show coord b (o-step a) (s.perm i) = _ from hv]; unfold halfE; split <;> linarith
    have hh:sendEdge s k (x,d)=(o,a):=by simp [o,a,sendEdge,posDir,Step.rotate,Step.used,hp]
    rw [hi,hh,show sign s d=1 from (by simp [sign,hp]),one_mul]
end YM.MSbar.Midpoint
