import YM.FVA2.Position.Weft
import YangMills.WilsonProof.NativeSupport.YM.FVA2.Position.Table
/-!
# Acting on a rack by the signed axis permutations

Signs are indexed by *input* axis. On these kernels use right-composition.
See `Weft`, `Column`, `Frugal` for use in the full formal comparison.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.Brass
open Function Set Filter Finset
open MS MS.Plane MS.Arts MS.Arts.Spin MS.Landau MS.Landau.Detect MS.Momentum MS.Koszul
open MS.Outlook MS.Halo MS.Motif
open Weft
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {m n:ℕ}{G:Gauge} (s t:Signed)
-- prolong $E4+D$ (additional even 2*n dimensions). Discrete skeleton.
abbrev sig (s:Signed)(a:Axis):ℝ:= if s.flip a then -1 else 1
lemma sig_p (a:Axis): sig s a*sig s a=1:= by unfold sig; split <;> simp
lemma sig_c (a:Axis): sig s⁻¹ (s.perm a)=sig s a:= by simp [sig]
lemma sig_t {E:Type}[AddCommGroup E][Module ℝ E](a:Axis)(u:E): sig s a • sig s a • u=u:= by rw [smul_smul,sig_p,one_smul]
lemma mat_t (a b:Axis): s.matrix b a= if b=s.perm a then sig s a else 0:= by rw [Signed.matrix_at]; simp [eq_comm (a:=b)]
lemma ax_v (x:E4)(i:Axis) : (Ortho.move s.ortho x) (s.perm i)=sig s i*x i:= by rw [Signed.ortho_move]; simp only [Signed.act_at ]; unfold sig; split <;> simp
lemma from_t (x:FourP)(i:Axis): (hand s).turn x (s.perm i)=sig s i*x i:= by change Signed.act s x _= _; rw [Signed.act_at]; unfold sig; split <;> simp
lemma director (i:Axis): (hand s).turn (spray i)=sig s i • spray (s.perm i):= by
 funext j; obtain ⟨j,rfl⟩:= s.perm.surjective j; rw [from_t]; by_cases he:i=j <;> simp [he,spray,(eq_comm (a:=j))]
lemma hand_zero : hand 1=nil Axis:= pointS _ _ Signed.act_one
lemma handMul : hand (s*t)=paste (hand s) (hand t):= pointS _ _ (fun _=> Signed.act_mul ..)
lemma handInv : hand s⁻¹=(hand s).back:= pointS _ _ (fun x=> by apply (hand s).turn.injective; rw [front]; exact Signed.act_inv ..)

abbrev viewD (s:Signed)(n:ℕ): Spin (L n):= arch (Nat.zero_le n) (hand s)
abbrev cash (s:Signed)(n:ℕ): Rack G n→ₗ[ℂ]Rack G n:= lamp (viewD s n)
lemma pressMul : viewD (s*t) m=paste (viewD s m) (viewD t m):=by rw [viewD, handMul, arch_group]
lemma tangent (n:ℕ): viewD 1 n=nil _:= by rw [viewD,hand_zero, arch_nil]
lemma invertS : viewD s⁻¹ n=( viewD s n ).back:= by rw [viewD,handInv,back_b]
lemma gatherH (f:Rack G m): cash (s*t) m f=cash t m (cash s m f):= by rw [ cash, pressMul ]; exact ( beamL (G:=G) (viewD t m) (viewD s m) f ).symm
lemma back_s (f:Rack G m): cash s m ( cash s⁻¹ m f )=f:= by rw [← gatherH,inv_mul_cancel]; unfold cash; rw [tangent]; exact beam_e f
lemma Ahead (i:Axis)(n:ℕ): (viewD s n).turn (spray (chair n i))=sig s i • spray (chair n (s.perm i)):= by unfold viewD chair; rw [← send_spray, Spin.arch_on, director,map_smul, send_spray]
lemma Away (n:ℕ)(i:Apart 0 n): (viewD s n).turn (spray (aside (Nat.zero_le n) i))=spray (aside (Nat.zero_le n) i):= by unfold viewD; rw [← send_spray]; exact arch_identity ..
-- need entrances: narrow full sum over l.Prop
lemma pore (i:Axis)(ℓ:L m): (viewD s m).profile ℓ (chair m (s.perm i))= if ℓ=chair m i then sig s i else 0 := by
    rw [ dual, ← invertS, Spin.profile, Ahead, Pi.smul_apply,smul_eq_mul, sig_c ]; simp [spray,Pi.single_apply,mul_ite]
lemma top (i:Axis)(j: L m) : (viewD s m).profile (chair m i) j= if j=chair m (s.perm i) then sig s i else 0:= by rw [Spin.profile, Ahead]; simp [spray,Pi.single_apply,mul_ite]
-- general discrete action. always arbitrary (not limited Signed scopes on mark kernels)
def heading (s:Signed)(n:ℕ): L n ≃ L n:= let Z:= equivS (Nat.zero_le n); Z.symm.trans ((Equiv.sumCongr s.perm (Equiv.refl _)).trans Z)
def mark (i:L n):ℝ:= ((equivS (Nat.zero_le n)).symm i).elim (sig s) (fun _=>1)
lemma ahead (k:Axis): heading s n (chair n k)=chair n (s.perm k):=by unfold heading; rw [ show chair n k= equivS (Nat.zero_le n) (Sum.inl k) from rfl]; simp only [Equiv.trans_apply,Equiv.symm_apply_apply]; rfl
lemma amark (k:Axis): mark s (chair n k)=sig s k:= by unfold mark; rw [ show chair n k= equivS (Nat.zero_le n) (Sum.inl k) from rfl]; simp
lemma trail (x: Apart 0 n): heading s n (aside ( Nat.zero_le n ) x)=aside ( Nat.zero_le n ) x:= by unfold heading; rw [show aside ( Nat.zero_le n ) x= equivS ( Nat.zero_le n ) (Sum.inr x) from rfl]; simp only [Equiv.trans_apply,Equiv.symm_apply_apply]; rfl
lemma tmark (x:Apart 0 n): mark s (aside ( Nat.zero_le n ) x)=1:= by unfold mark; rw [show aside ( Nat.zero_le n ) x= equivS ( Nat.zero_le n ) (Sum.inr x) from rfl]; simp
lemma turns_top (i:L m): (viewD s m).turn (spray i)=mark s i • spray ( heading s m i):= by
 rcases rangeA i (Nat.zero_le m) with ⟨i,rfl⟩|⟨i,rfl⟩; · rw [show rises (Nat.zero_le m) i=chair m i from rfl,ahead,amark,Ahead]
 rw [Away,trail,tmark,one_smul]
-- every profile gain sign
lemma flare (x y:L m): (viewD s m).profile x y= if y=heading s m x then mark s x else 0:= by unfold Spin.profile; rw [turns_top]; simp [spray,Pi.single_apply,mul_ite]
local notation "α"=> Arts.Cfield
abbrev toward (x:Cfield G m) : Cfield G m:= embA (heading s m).toEmbedding x
def tt (x:Cfield G m):ℝ:= x.1.1.elim 1 (mark s)
def torso (x:Shore G m): Shore G m:= (toward s x.1,(viewD s m).turn x.2)
def rack (x:Legs (Shore G m)):= x.map (torso s)
def Track (x:Legs (Shore G m)):ℝ:= (x.map ( fun i=>tt s i.1 )).prod
lemma area (x y:Cfield G m) : (viewD s m).prop x y= if y=toward s x then (tt s x:ℂ) else 0:= by
    rcases x with ⟨⟨_|i,a⟩,c⟩ <;> rcases y with ⟨⟨_|j,b⟩,d⟩ <;> by_cases he:c=d <;> by_cases hh:a=b <;> simp [he,hh,toward, Spin.prop, Spin.rayS, Spin.shadow,tt,embA,eq_comm (a:=d),eq_comm (a:=b)] -- maybe unfold Option; `tt` parser!
    rw [flare]; split <;> simp
lemma evaluate (f:Rack G m)(x: Legs (Shore G m)): cash s m f x= ( Track s x:ℂ ) * f ( rack s x ):= by
    induction x generalizing f with| nil=> simp [rack,Track,cash,lamp] | cons a l ih=> unfold cash lamp; rw [Pilot.met]; change ∑ i,(viewD _ m).prop a.1 i * cash s m _ l=_; simp_rw [area,ite_mul,zero_mul]; rw [Finset.sum_ite_eq']; rw [if_pos (Finset.mem_univ _),ih]; unfold Track rack; simp only [List.map_cons,List.prod_cons,Complex.ofReal_mul,mul_assoc]; rfl
end YM.FVA2.Position.Brass
