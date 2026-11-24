import YM.FVA2.Parity.Recogn
/-!
# Build the parity policy prior to installation of the fully rank-budgeted data

If given, preserve also `Horder` and `UnitP`. See `Teller/Where` for the use.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Parity.Screen
open Function Set Filter Finset Lattice MeasureTheory
open MS MS.Koszul MS.Plane MS.Book MS.Native MS.Native.Orient MS.Native.Chart
open MS.Native.Sew MS.Cylinder MS.Cylinder.Lab MS.Landau MS.Landau.Detect MS.Color MS.Native.Paint
open MS.Momentum MS.Menus MS.Native.Wilsonian MS.City MS.Wind MS.Arts MS.Outlook MS.Tone MS.Logarithm
open MS.Book.Program MS.Book.Convolve MS.Tone.Frame Hue.Agent Hue.Agent.Kappa Position
open MS.Heat MS.Heat.Signal MS.High MS.High.Knobs MS.Land MS.Plane.Wire
open MS.Local.Physical MS.Mach MS.Dock MS.Pearl MS.Train MS.Wind.Leading Position.Favors
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {J:Type}{m n d i k t:ℕ}{G:Gauge}{p:Team}{r v:ℤ}
local notation "γ"=> grey G Cover
local notation "Ψ"=> Hue.flip (Lane4 G)
local notation "℘"=> ( Press.portDeck G )
variable (Y:XSpace.Initialize G){Z:Booked (Press.portDeck G)}(T:MS_Data G Z)
local notation "ℳ"=> Press.wickInput Y
local notation "g"=> Glyph (Press.portDeck G) d
local notation "ι"=> Plaid (Press.portDeck G) d
local notation "σ"=> Screen.sigma
local notation "H"=> Screen.shaded
lemma Sig (i:ℕ): σ i *σ i=1:= by unfold Screen.sigma; rw [← mul_pow ]; norm_num
abbrev both (a:ι)(m:Acts ℘ d) (t:Bool) : Acts ℘ d:= if t then Screen.shaded a.1.val m else m
abbrev morn (a:ι)(m:Acts ℘ d): Acts ℘ d:= stepF Finset.univ (fun _:Bool=> (2:ℝ)⁻¹) (both a m)
lemma calibrated {E:Type*} [AddCommGroup E][Module ℝ E](x:E): ∑ _:Bool, (2:ℝ)⁻¹ • x=x:= by simp only [Fintype.sum_bool, ← add_smul, show (2:ℝ)⁻¹+(2:ℝ)⁻¹=1 from (by norm_num),one_smul]
lemma retained (m:Acts ℘ d)(a:ι)(hx:FitOrder ( read a ) (m 0)): FitOrder (read a) (morn a m 0):= by
    have ht(i:Bool): FitOrder (read a) ( both a m i 0 ):= by cases i; exact hx; exact tollCap _ _ hx
    refine ⟨fun i=> lower_r _ (fun i hi x=> ht i|>.Low x) i,fun j hj=>?_⟩; change (∑ i:Bool, (( 2: ℝ )⁻¹) • ( both a m i 0).register ) j=_; simp_rw [ Finset.sum_apply,Pi.smul_apply,show ∀ i: Bool,( both a m i 0).register j=_ from fun i=>( ht i).Single _ hj, calibrated]
lemma policy (m:Acts ℘ d)(h:Correct p)(a:ι)(he: Fixed (col (horizonF ℳ p m)) ( Archive d ( T.marks d a )) false d 0): Fixed ( col (horizonF ℳ p (morn a m))) (Archive d ( T.marks d a )) false d 0:= by
    have he'(i:Bool): Fixed ( col (horizonF ℳ p ( both a m i ))) (Archive d ( T.marks d a )) false d 0:= by cases i; exact he; exact pledged Y m _ _ (Optic.marks T d a) h he
    unfold morn; rw [Favors.total_H, Crosswind.col_sum,← calibrated ( Archive _ _) ]; exact Crosswind.fixed_sum _ (fun i _=> he' i ) _
def brush (S:Prescription ℘): Prescription ℘:= ⟨S.team,fun i v=> morn v (S.fees i v), fun i a=> retained _ _ ( S.init i a) ⟩
lemma trueS (S:Prescription ℘)(h:G.Simple)(he:TaylorOKF T ℳ S): TaylorOKF T ℳ (brush S):= ⟨he.bulk,fun d a=> policy Y T _ (standardF h he) a (he.mark d a)⟩
structure Right (S:Prescription ℘) : Prop where
    cost (d:ℕ) (a:Plaid ℘ d) (n:ℕ) : rightS a.1.val n ( S.fees d a n ).register=( S.fees d a n ).register
lemma equation (m:Acts ℘ d)(a:ι)(n:ℕ)(i:g): ( (morn a m) n ).register i= ( 2:ℝ )⁻¹ • (m n).register i+( 2:ℝ )⁻¹ • ( rightS a.1.val n (m n).register i):= by
    change (∑ j:Bool, ( 2:ℝ )⁻¹ • ( both a m j n ).register ) i= _; rw [Fintype.sum_bool, Pi.add_apply, add_comm]; rfl
lemma verifiedS (S: Prescription ℘) : Right (brush S):= by
    constructor; intro d a n; funext i; change rightS a.1.val n ((morn a _ ) n).register i= ( morn a (S.fees d a) n ).register i; rw [rightS,equation, smul_add, rightS, smul_comm (σ _) ( ( 2:ℝ )⁻¹ ), smul_comm (σ _) ( ( 2:ℝ )⁻¹ ), smul_smul, add_comm ]; rw [smul_smul (σ _) (σ _) _,Sig, one_smul] -- order
-- never destroy preexisting H / Unit
variable {F:DMark G d→Acts (Press.portDeck G) d}
lemma art (h:Favors.Held F): Favors.Held (fun a=>H a.1.val (F a)):= by
    intro a s n; funext j; unfold Favors.move; unfold Screen.shaded; simp_rw [ erect, Finset.sum_apply, Pi.smul_apply, rightS]; -- for RHS rank.'
    let k:= σ (n+j.grade+a.1.val); have he := congr_fun (h a s n) j; unfold Favors.move Favors.erect at he; simp only [Finset.sum_apply,Pi.smul_apply] at he; -- need k both sides
    calc
     _= k • (∑ i:Axes.Case G d a.1.val, Axes.markS s G d a.1.val a.2 i • (F ( Favors.pin a i) n).register j ) := by rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=> smul_comm ..
     _= _:=by rw [he,Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=> smul_comm k (Axes.markS s G j.size j.grade i j.2.2) _
lemma stillH (h:Favors.Held F): Favors.Held (fun a=> morn a ( F a ) ):= by
    let c i (a:ι):= both a ( F a ) i; have hC(i:Bool): Held ( c i ):= by cases i; exact h; exact art h
    intro a s n; let f i:= fun a:ι=>( c i a n ).register; change move s (fun a=>∑ i:Bool,( 2:ℝ )⁻¹ • f i a ) a= erect s (∑ i:Bool, ( 2:ℝ )⁻¹ • f i a ); rw [move_sum, erect_sum]; exact Finset.sum_congr rfl fun i _=> congr_arg ( (( 2:ℝ )⁻¹) • ·) (hC i a s n)
lemma keepsH (S:Prescription ℘)(h:Horder S): Horder (brush S):= ⟨fun i=> stillH ( h.property i )⟩
lemma keepsU (S:Prescription ℘)(h: Ace.UnitP S): Ace.UnitP (brush S):= by
    constructor; intro a n; funext i; change ( ( morn a (S.fees 0 a) ) n ).register i = _; rw [ equation, h.aq a n, rightS, Ace.register ]; split_ifs with hs; swap; · simp
    have hn:a.1.val=0:= by have he:=a.1.isLt; omega
    unfold sigma; rw [hs.1, show i.grade=0 from le_antisymm i.memory (Nat.zero_le _),hn]; norm_num [ ← add_smul]
theorem eternal (S:Prescription ℘)(h:G.Simple)(hs: TaylorOKF T ℳ S)(ht:Horder S)(hp:Ace.UnitP S): TaylorOKF T ℳ (brush S)∧Right (brush S)∧ Horder (brush S)∧ Ace.UnitP (brush S):= ⟨trueS Y T S h hs,verifiedS S,keepsH S ht, keepsU S hp⟩
end YM.FVA2.Parity.Screen
